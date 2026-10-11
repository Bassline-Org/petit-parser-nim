import std/[options, strutils, sugar, tables, unicode]
import ../parser

type
  JsonKind* = enum
    jkNull, jkBool, jkString, jkNumber, jkArray, jkObject

  JsonValue* = object
    case kind*: JsonKind
    of jkNull: discard
    of jkBool: boolVal*: bool
    of jkString: stringVal*: string
    of jkNumber: numberVal*: string
    of jkArray: arrayVal*: seq[JsonValue]
    of jkObject: objectVal*: Table[string, JsonValue]

proc escaped(c: char): string =
  case c
  of 'b': "\b"
  of 'f': "\f"
  of 'n': "\n"
  of 'r': "\r"
  of 't': "\t"
  else: $c

proc decoded(hi: int, lo: Option[(string, int)]): string =
  if hi in 0xD800 .. 0xDBFF and lo.isSome and lo.get[1] in 0xDC00 .. 0xDFFF:
    Rune(0x10000 + (hi - 0xD800) shl 10 + lo.get[1] - 0xDC00).toUTF8
  elif lo.isSome:
    Rune(hi).toUTF8 & Rune(lo.get[1]).toUTF8
  else:
    Rune(hi).toUTF8

proc jsonParser*(): Parser[JsonValue] =
  let
    ws = chars({' ', '\t', '\n', '\r'}, "whitespace")
    value = undefined[JsonValue]("value")

    hex4 = chars(HexDigits, "hex digit").times(4).flatten.map(h => parseHexInt(h))
    unicode = sequence((str("\\u"), hex4, (str("\\u") & hex4).optional))
      .map(m => decoded(m[1], m[2]))
    escape = (str("\\") & chars("\"\\/bfnrt", "escape"))
      .map(m => escaped(m[1]))
    run = chars({'\x20' .. '\xFF'} - {'"', '\\'}, "character").plus.flatten
    text = delimited(ch('"'), ch('"'), (run / escape / unicode).star)
      .map(m => m.join).trim(ws)

    digits = digit().plus
    integer = ch('0').skip / (between('1', '9') & digit().star).skip
    fraction = (ch('.') & digits).skip.optional
    exponent = (chars("eE", "exponent") & chars("+-", "sign").optional & digits).skip.optional
    jsonNumber = sequence((ch('-').optional, integer, fraction, exponent)).flatten("number").trim(ws)
      .map(s => JsonValue(kind: jkNumber, numberVal: s))

    tru = str("true").map(_ => JsonValue(kind: jkBool, boolVal: true))
    fals = str("false").map(_ => JsonValue(kind: jkBool, boolVal: false))
    null = str("null").map(_ => JsonValue(kind: jkNull))
    jsonLiteral = (tru / fals / null).trim(ws)

    jsonString = text.map(s => JsonValue(kind: jkString, stringVal: s))
    comma = ch(',').trim(ws)
    jsonArray = delimited(ch('[').trim(ws), ch(']').trim(ws), value.starSeparated(comma))
      .map(m => JsonValue(kind: jkArray, arrayVal: m.elements))
    entry = sequence((text, ch(':').trim(ws), value)).map(m => (m[0], m[2]))
    jsonObj = delimited(ch('{').trim(ws), ch('}').trim(ws), entry.starSeparated(comma))
      .map(m => JsonValue(kind: jkObject, objectVal: m.elements.toTable))

  value.define(jsonObj / jsonArray / jsonNumber / jsonString / jsonLiteral)
  value.complete.resolve