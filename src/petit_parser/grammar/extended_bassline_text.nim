## The bassline textual syntax with dialect blocks. `lang NAME [[ … ]]`
## reads the block with the parser registered as NAME, so a dialect's own
## notation stands where a value would and reads as values. The block is
## a Lua long bracket, `[=[ … ]=]` at any level, for content holding `]]`.
## A dialect parser is used as given: resolve it, and let it read the
## whole block.

import std/[algorithm, sequtils, strutils, sugar, tables]
import ../parser
import ./[bassline_text, sexp, json, uri]
export bassline_text

type Dialects* = Table[string, Parser[BlNode]]

proc langForm(dialects: Dialects): Parser[BlNode] =
  let
    gap = space().star.skip
    ends = notAhead(noneOf(Delims, "symbol character"))
    name = noneOf(Delims, "symbol character").plus.flatten("a dialect name")
    opener = sequence((str("lang"), ends, gap, position(), name, gap,
                       ch('['), ch('=').star.flatten, ch('[')))
      .map(m => (m[3], m[4], m[7].len))
    unknown = failure[BlNode]("a known dialect")
    unfinished = failure[BlNode]("the end of the block")
  opener.callCC(
    proc (next: Parser[(int, string, int)], ctx: Context): Result[BlNode] =
      var o = next.parseOn(ctx)
      if not o.isSuccess: return failedAs(BlNode, o)
      let
        (at, name, level) = o.take
        close = "]" & '='.repeat(level) & "]"
        input = ctx.input
        stop = input.text.find(close, o.pos, input.stop - 1)
      if stop < 0: return fail[BlNode](failure[BlNode]("'" & close & "'"), ctx.at(input.stop))
      let dialect = dialects.getOrDefault(name)
      if dialect.isNil: return fail[BlNode](unknown, ctx.at(at))
      let outer = input.stop
      input.stop = stop
      defer: input.stop = outer
      var r = dialect.parseOn(ctx.at(o.pos))
      if not r.isSuccess: r
      elif r.pos < stop: fail[BlNode](unfinished, ctx.at(r.pos))
      else: succeed(r.take, stop + close.len))

proc extendedValue*(dialects: Dialects): Parser[BlNode] =
  ## One value, bare.
  basslineValue(@[langForm(dialects)], @["lang"])

proc extendedForm*(dialects: Dialects): Parser[BlNode] =
  ## One value and the space around it.
  extendedValue(dialects).trim(space())

proc extendedParser*(dialects: Dialects): Parser[BlNode] =
  ## Exactly one value.
  extendedForm(dialects).complete.resolve

proc extendedDocument*(dialects: Dialects): Parser[seq[BlNode]] =
  ## Any number of values, including none.
  extendedForm(dialects).star.trim(space()).complete.resolve

# Two dialects from the grammars here

proc sexpNode(s: Sexp): BlNode =
  let n = case s.kind
    of skSymbol: BlNode(kind: bkSymbol, text: s.stringVal)
    of skString: BlNode(kind: bkText, text: s.stringVal)
    of skNumber: BlNode(kind: bkInt, text: $s.numberVal)
    of skList: BlNode(kind: bkList, items: s.listVal.map(sexpNode))
  if s.quoted: BlNode(kind: bkRecord, items: @[BlNode(kind: bkSymbol, text: "quote"), n]) else: n

proc sexpDialect*(): Parser[BlNode] =
  ## Symbols, numbers, text and lists as themselves, `'x` as `(quote x)`.
  sexpParser().map(sexpNode)

proc shortlex(a, b: string): int =
  if a.len != b.len: cmp(a.len, b.len) else: cmp(a, b)

proc jsonNode(j: JsonValue): BlNode =
  case j.kind
  of jkNull: BlNode(kind: bkNil)
  of jkBool: BlNode(kind: bkSymbol, text: $j.boolVal)
  of jkString: BlNode(kind: bkText, text: j.stringVal)
  of jkNumber: BlNode(kind: bkInt, text: j.numberVal)
  of jkArray: BlNode(kind: bkList, items: j.arrayVal.map(jsonNode))
  of jkObject:
    let keys = j.objectVal.keys.toSeq.sorted(shortlex)
    BlNode(kind: bkDict,
           entries: keys.map(k => (BlNode(kind: bkText, text: k), jsonNode(j.objectVal[k]))))

proc integral(j: JsonValue): bool =
  case j.kind
  of jkNumber: j.numberVal.allCharsInSet(Digits + {'-'})
  of jkArray: j.arrayVal.all(integral)
  of jkObject: j.objectVal.values.toSeq.all(integral)
  else: true

proc jsonDialect*(): Parser[BlNode] =
  ## null is nil, true and false are symbols, strings are text, arrays
  ## are lists and objects are dicts keyed by text. A number that is not
  ## an integer is refused.
  jsonParser().where(integral, "integers only").map(jsonNode)

proc standardDialects*(): Dialects =
  {"sexp": sexpDialect(), "json": jsonDialect(), "uri": uriParser()}.toTable
