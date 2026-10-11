## The bassline textual syntax (data-model.org, "Textual Syntax") read into
## a light tree. Numbers are kept as spelled with the `_` separators
## removed, bytes are kept as bytes, and text and symbols are decoded.

import std/[strutils, sugar]
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

const Delims = " \t\n\r[]{}():'\";!"

func `==`*(a, b: BlNode): bool =
  if a.kind != b.kind or a.mark != b.mark: return false
  case a.kind
  of bkNil: true
  of bkInt, bkText, bkSymbol: a.text == b.text
  of bkBytes: a.bytes == b.bytes
  of bkList, bkRecord, bkSet: a.items == b.items
  of bkDict: a.entries == b.entries

proc toBytes*(s: string): seq[byte] = @(s.toOpenArrayByte(0, s.high))

proc marked(n: BlNode): BlNode =
  result = n
  result.mark = true

proc allDifferent(items: seq[BlNode]): bool =
  for i in 1 ..< items.len:
    if items[i] in items[0 ..< i]: return false
  true

proc uniqueKeys(entries: seq[(BlNode, BlNode)]): bool =
  var keys: seq[BlNode]
  for (k, _) in entries: keys.add k
  allDifferent(keys)

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

proc space(): Parser[Nothing] =
  chars(" \t\n\r", "whitespace").skip / (ch(';') & neg(newline()).star).skip

proc basslineForm(): Parser[BlNode] =
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
    symbol = (notAhead(numberStart) & bare).map(m => BlNode(kind: bkSymbol, text: m[1]))
    rawAtom = bytesTok / numberTok / nilTok / text / quotedSymbol / symbol
    atom = (rawAtom & (ch('!') & ends).optional)
      .map(m => (if m[1].isSome: marked(m[0]) else: m[0]))

    list = delimited(ch('['), ch(']').trim(ws), form.star)
      .map(items => BlNode(kind: bkList, items: items))
    record = delimited(ch('('), ch(')').trim(ws), form.plus)
      .map(items => BlNode(kind: bkRecord, items: items))
    entry = (form & ch(':').trim(ws)).pick(0) & form
    emptySet = (ch('{') & ch('}').trim(ws)).map(_ => BlNode(kind: bkSet))
    emptyDict = sequence((ch('{'), ch(':').trim(ws), ch('}').trim(ws)))
      .map(_ => BlNode(kind: bkDict))
    dict = delimited(ch('{'), ch('}').trim(ws), entry.plus)
      .where(uniqueKeys, "distinct keys")
      .map(entries => BlNode(kind: bkDict, entries: entries))
    pset = delimited(ch('{'), ch('}').trim(ws), form.plus)
      .where(allDifferent, "distinct members")
      .map(items => BlNode(kind: bkSet, items: items))
    frame = list / record / emptySet / emptyDict / dict / pset
    markedFrame = (ch('!') & frame).pick(1).map(marked)

  value.define(markedFrame / frame / atom)
  form

proc basslineParser*(): Parser[BlNode] =
  ## Exactly one value.
  basslineForm().complete.resolve

proc basslineDocument*(): Parser[seq[BlNode]] =
  ## Any number of values, including none.
  basslineForm().star.trim(space()).complete.resolve