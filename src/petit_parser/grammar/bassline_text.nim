## The bassline textual syntax (data-model.org, "Textual Syntax") read into
## a light tree. Numbers are kept as spelled with the `_` separators
## removed, bytes are kept as bytes, and text and symbols are decoded.

import std/[hashes, sequtils, sets, strutils, sugar]
import ../parser

type
  BlKind* = enum
    bkNil, bkInt, bkText, bkSymbol, bkBytes, bkList, bkRecord, bkSet, bkDict

  BlNode* = object
    mark*: bool
    case kind*: BlKind
    of bkNil: discard
    of bkInt, bkText, bkSymbol: text*: string
    of bkBytes: bytes*: seq[byte]
    of bkList, bkRecord, bkSet: items*: seq[BlNode]
    of bkDict: entries*: seq[(BlNode, BlNode)]

const Delims* = " \t\n\r[]{}():'\";!"

func `==`*(a, b: BlNode): bool =
  if a.kind != b.kind or a.mark != b.mark: return false
  case a.kind
  of bkNil: true
  of bkInt, bkText, bkSymbol: a.text == b.text
  of bkBytes: a.bytes == b.bytes
  of bkList, bkRecord, bkSet: a.items == b.items
  of bkDict: a.entries == b.entries

func hash*(n: BlNode): Hash =
  var h = hash(n.kind) !& hash(n.mark)
  case n.kind
  of bkNil: discard
  of bkInt, bkText, bkSymbol: h = h !& hash(n.text)
  of bkBytes: h = h !& hash(n.bytes)
  of bkList, bkRecord, bkSet: h = h !& hash(n.items)
  of bkDict: h = h !& hash(n.entries)
  !$h

proc toBytes*(s: string): seq[byte] = @(s.toOpenArrayByte(0, s.high))

proc marked(n: BlNode): BlNode =
  result = n
  result.mark = true

proc allDifferent(items: seq[BlNode]): bool =
  var seen: HashSet[BlNode]
  for i in items:
    if seen.containsOrIncl(i): return false
  true

proc uniqueKeys(entries: seq[(BlNode, BlNode)]): bool =
  var seen: HashSet[BlNode]
  for (k, _) in entries:
    if seen.containsOrIncl(k): return false
  true

proc unescaped(c: char): string =
  case c
  of 'n': "\n"
  of 't': "\t"
  of 'r': "\r"
  else: $c

proc quoted(q: char): Parser[string] =
  let
    escape = (ch('\\') & chars($q & "\\ntr", "escape")).map(m => unescaped(m[1]))
    run = noneOf($q & "\\", "character").plus.flatten
  delimited(ch(q), ch(q), (run / escape).star).map(parts => parts.join)

proc space*(): Parser[Nothing] =
  ## Whitespace or a `;` comment.
  chars(" \t\n\r", "whitespace").skip / (ch(';') & neg(newline()).star).skip

proc basslineValue*(extensions: seq[Parser[BlNode]] = @[], reserved: seq[string] = @[]): Parser[BlNode] =
  ## One value, bare. `extensions` are tried before a symbol, and the
  ## `reserved` words are never read as one.
  let
    ws = space()
    value = undefined[BlNode]("value")
    form = value.trim(ws)
    ends = notAhead(noneOf(Delims, "symbol character"))

    hex = chars(HexDigits, "hex digit")
    hexBody = (hex & (ch('_').optional & hex).star).skip.optional
    bytesTok = sequence((str("0x"), hexBody, ends)).flatten("bytes")
      .where(b => (b.len - 2 - b.count('_')) mod 2 == 0, "an even count of hex digits")
      .map(b => BlNode(kind: bkBytes, bytes: parseHexStr(b[2 .. ^1].replace("_", "")).toBytes))
    numberStart = digit().skip / (ch('-') & digit()).skip
    digits = ch('0').skip / (between('1', '9') & (ch('_').optional & digit()).star).skip
    numberTok = sequence((ch('-').optional, digits, ends)).flatten("number")
      .where(n => n != "-0", "a number")
      .map(n => BlNode(kind: bkInt, text: n.replace("_", "")))
    nilTok = (str("nil") & ends).map(_ => BlNode(kind: bkNil))
    text = quoted('"').map(s => BlNode(kind: bkText, text: s))
    quotedSymbol = quoted('\'').map(s => BlNode(kind: bkSymbol, text: s))
    bare = noneOf(Delims, "symbol character").plus.flatten("symbol")
    keyword = choice(reserved.map(w => (str(w) & ends).skip("'" & w & "'")))
    symbol = sequence((notAhead(numberStart), notAhead(keyword), bare))
      .map(m => BlNode(kind: bkSymbol, text: m[2]))
    rawAtom = choice(@[bytesTok, numberTok, nilTok, text, quotedSymbol] & extensions & @[symbol])
    atom = (rawAtom & (ch('!') & ends).optional)
      .map(m => (if m[1].isSome: marked(m[0]) else: m[0]))

    list = delimited(ch('['), ch(']').trim(ws), form.star)
      .map(items => BlNode(kind: bkList, items: items))
    record = delimited(ch('('), ch(')').trim(ws), form.plus)
      .map(items => BlNode(kind: bkRecord, items: items))
    colon = ch(':').trim(ws)
    entries = ((form & colon).pick(0) & form).star
    members = form.star
    sameKey = failure[BlNode]("distinct keys")
    sameMember = failure[BlNode]("distinct members")
    # the first member, read once, decides between a dict and a set
    braced = (form & (colon & form).pick(1).optional).callCC(
      proc (next: Parser[(BlNode, Option[BlNode])], ctx: Context): Result[BlNode] =
        var f = next.parseOn(ctx)
        if not f.isSuccess: return failedAs(BlNode, f)
        var (k, v) = f.take
        if v.isSome:
          var r = entries.parseOn(ctx.at(f.pos))
          if not r.isSuccess: return failedAs(BlNode, r)
          var es = r.take
          es.insert((move k, v.get), 0)
          if not uniqueKeys(es): return fail[BlNode](sameKey, ctx.at(r.pos))
          succeed(BlNode(kind: bkDict, entries: es), r.pos)
        else:
          var r = members.parseOn(ctx.at(f.pos))
          if not r.isSuccess: return failedAs(BlNode, r)
          var items = r.take
          items.insert(move k, 0)
          if not allDifferent(items): return fail[BlNode](sameMember, ctx.at(r.pos))
          succeed(BlNode(kind: bkSet, items: items), r.pos))
    emptyDict = colon.map(_ => BlNode(kind: bkDict))
    emptySet = epsilon(BlNode(kind: bkSet))
    braces = delimited(ch('{'), ch('}').trim(ws), emptyDict / braced / emptySet)
    frame = list / record / braces
    markedFrame = (ch('!') & frame).pick(1).map(marked)

  value.define(markedFrame / frame / atom)
  value

proc basslineForm*(extensions: seq[Parser[BlNode]] = @[], reserved: seq[string] = @[]): Parser[BlNode] =
  ## One value and the space around it.
  basslineValue(extensions, reserved).trim(space())

proc basslineParser*(): Parser[BlNode] =
  ## Exactly one value.
  basslineForm().complete.resolve

proc basslineDocument*(): Parser[seq[BlNode]] =
  ## Any number of values, including none.
  basslineForm().star.trim(space()).complete.resolve
