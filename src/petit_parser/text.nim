## Leaves over text: a `string` source read as characters, with positions
## that print as line:column.

import std/[strutils, setutils, sugar]
import ./parser

type TextParser*[R] = Parser[string, R]

proc lineCol*(text: string, pos: int): (int, int) =
  let before = text[0 ..< min(pos, text.len)]
  (before.count('\n') + 1, pos - before.rfind('\n'))

proc newInput*(text: sink string): Input[string] =
  result = parser.newInput[string](text)
  let input = result
  result.locateFn = proc (pos: int): string =
    let (line, col) = lineCol(input.source, pos)
    $line & ":" & $col

proc chars*(cs: set[char], expected: string): TextParser[char] = oneOf[string, char](cs, expected)
proc chars*(cs, expected: string): TextParser[char] = oneOf[string, char](cs.toSet, expected)
proc noneOf*(cs, expected: string): TextParser[char] = oneOf[string, char](cs.toSet.complement, expected)
proc ch*(c: char): TextParser[char] = oneOf[string, char]({c}, "'" & c & "'")
proc between*(lo, hi: char): TextParser[char] = oneOf[string, char]({lo .. hi}, "'" & lo & "'..'" & hi & "'")

proc pattern*(spec: string): TextParser[char] =
  ## A character class: "a-zA-Z_", or negated "^0-9".
  let negated = spec.startsWith '^'
  var
    cs: set[char]
    i = negated.ord
  while i < spec.len:
    if i + 2 < spec.len and spec[i + 1] == '-':
      cs.incl {spec[i] .. spec[i + 2]}
      i += 3
    else:
      cs.incl spec[i]
      inc i
  chars(if negated: cs.complement else: cs, "[" & spec & "]")

proc anyChar*(): TextParser[char] = chars(fullSet(char), "any character")
proc digit*(): TextParser[char] = chars(Digits, "digit")
proc letter*(): TextParser[char] = chars(Letters, "letter")
proc lowercase*(): TextParser[char] = chars({'a' .. 'z'}, "lowercase letter")
proc uppercase*(): TextParser[char] = chars({'A' .. 'Z'}, "uppercase letter")
proc word*(): TextParser[char] = chars(Letters + Digits + {'_'}, "letter or digit")
proc whitespace*(): TextParser[char] = chars(Whitespace, "whitespace")

proc continuesWith(ctx: Context[string], lit: string): bool =
  ctx.pos + lit.len <= ctx.input.stop and ctx.input.source.continuesWith(lit, ctx.pos)

proc str*(lit: string): TextParser[string] =
  leaf[string, string]("'" & lit & "'",
    (ctx: Context[string]) => (if ctx.continuesWith(lit): ctx.pos + lit.len else: -1),
    (ctx: Context[string], stop: int) => lit)

proc continuesWithIgnoreCase(ctx: Context[string], lit: string): bool =
  if ctx.pos + lit.len > ctx.input.stop: return false
  for i, c in lit:
    if ctx.input.source[ctx.pos + i].toLowerAscii != c.toLowerAscii: return false
  true

proc strIgnoreCase*(lit: string): TextParser[string] =
  ## `lit` in any ASCII case; the value is the input as written.
  leaf[string, string]("'" & lit & "'",
    (ctx: Context[string]) => (if ctx.continuesWithIgnoreCase(lit): ctx.pos + lit.len else: -1),
    (ctx: Context[string], stop: int) => ctx.input.source[ctx.pos ..< stop])

proc newline*(): TextParser[string] =
  leaf[string, string]("newline",
    proc (ctx: Context[string]): int =
      if ctx.continuesWith("\r\n"): ctx.pos + 2
      elif ctx.pos < ctx.input.stop and ctx.input.source[ctx.pos] in {'\n', '\r'}: ctx.pos + 1
      else: -1,
    (ctx: Context[string], stop: int) => ctx.input.source[ctx.pos ..< stop])

proc trim*[R](p: TextParser[R]): TextParser[R] =
  ## `p` with whitespace skipped on both sides.
  p.trim(whitespace())

proc text*[R](t: Token[R]): string =
  ## The text a token covers.
  Input[string](t.input).source[t.start ..< t.stop]
