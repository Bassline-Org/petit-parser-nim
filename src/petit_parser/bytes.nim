## Leaves over bytes: a `seq[byte]` source, with positions that print as
## byte offsets.

import std/[strutils, setutils, sugar]
import ./parser

type ByteParser*[R] = Parser[seq[byte], R]

proc bytes*(bs: set[byte], expected: string): ByteParser[byte] = oneOf[seq[byte], byte](bs, expected)
proc ch*(b: byte): ByteParser[byte] = oneOf[seq[byte], byte]({b}, "0x" & b.toHex)
proc anyByte*(): ByteParser[byte] = bytes(fullSet(byte), "any byte")

proc str*(lit: openArray[byte]): ByteParser[seq[byte]] =
  let lit = @lit
  var hex = "0x"
  for b in lit: hex.add b.toHex
  leaf[seq[byte], seq[byte]](hex,
    proc (ctx: Context[seq[byte]]): int =
      if ctx.pos + lit.len > ctx.input.stop: return -1
      for i, b in lit:
        if ctx.input.source[ctx.pos + i] != b: return -1
      ctx.pos + lit.len,
    (ctx: Context[seq[byte]], stop: int) => lit)

proc parse*[R](p: ByteParser[R], data: openArray[byte]): Result[R] = parser.parse(p, @data)
proc accepts*(p: SourceParser[seq[byte]], data: openArray[byte]): bool = parser.accepts(p, @data)

proc toBytes*(s: string): seq[byte] = @(s.toOpenArrayByte(0, s.high))

func toText*(data: openArray[byte]): string =
  result = newString(data.len)
  for i, b in data: result[i] = b.char
