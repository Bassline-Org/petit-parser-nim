## Node shapes, the analyses read off them, and `optimize`: every rewrite
## shown to happen, and shown to change nothing a parse answers.

import std/[algorithm, strutils, sugar, tables, unittest]
import petit_parser
import petit_parser/parser
import petit_parser/grammar/[json, sexp]

proc apply(a: int, op: char, b: int): int =
  case op
  of '+': a + b
  of '-': a - b
  of '*': a * b
  else: a div b

proc fold(l: Separated[int, char]): int = l.foldLeft(apply)

proc calculator(): TextParser[int] =
  let expr = undefined[string, int]("expr")
  let number = digit().plus.flatten("number").map((s: string) => parseInt(s)).trim
  let parens = sequence((ch('(').trim, expr, ch(')').trim)).map((t: (char, int, char)) => t[1])
  let primary = (number / parens).named("primary")
  let term = primary.plusSeparated(pattern("*/").trim).map(fold)
  expr.define(term.plusSeparated(pattern("+-").trim).map(fold))
  expr.complete

proc without(bs: set[byte], b: byte): set[byte] =
  ## at runtime: the compiler trips over folding differences of byte sets
  result = bs
  result.excl b

proc sameMessage(a, b: string): bool =
  ## the same expectations at the same place; a dispatched choice records
  ## the alternatives it tried before those it skipped, so the order of the
  ## names may differ
  proc parts(m: string): (seq[string], string) =
    let at = m.rfind(" at ")
    var names = m[0 ..< at]
    names.removePrefix("expected ")
    names.removePrefix("one of ")
    var ns = names.split(", ")
    ns.sort
    (ns, m[at .. ^1])
  parts(a) == parts(b)

proc kinds(root: ParserBase): CountTable[NodeKind] =
  for p in root.allParsers: result.inc p.kind

template agree(plain, optimized: untyped, inputs: openArray[string], values: static bool = true) =
  ## the same positions and messages on both paths, and the same values
  ## where they can be compared
  for input in inputs:
    let
      a = plain.parse(input)
      b = optimized.parse(input)
    check a.isSuccess == b.isSuccess
    if a.isSuccess and b.isSuccess:
      when values: check a.value == b.value
      check a.pos == b.pos
    elif not a.isSuccess and not b.isSuccess:
      check sameMessage(a.message, b.message)
    check plain.accepts(input) == optimized.accepts(input)

suite "node shapes":
  test "every node says what it is":
    check ch('a').kind == nkSet
    check ch('a').elementSet == {byte('a')}
    check str("ab").kind == nkLiteral and str("ab").min == 2
    check str("ab").elementSet == {byte('a')}
    check (ch('a') & ch('b')).kind == nkSequence
    check (ch('a') / ch('b')).kind == nkChoice
    check digit().star.kind == nkRepeat and digit().star.min == 0 and digit().star.max < 0
    check digit().times(3).min == 3 and digit().times(3).max == 3
    check digit().optional.kind == nkOptional
    check digit().map((c: char) => 1).kind == nkMap
    check digit().trim.kind == nkTrim and digit().trim.children.len == 3
    check notAhead(digit()).kind == nkNotAhead and neg(digit()).kind == nkNeg
    check epsilon[string]().kind == nkEpsilon and endOfInput[string]().kind == nkEnd
    check parser.any[string]().kind == nkAny and failure[string, int]("x").kind == nkFailure
    check anyChar().kind == nkSet   # a set of every character
    check digit().flatten.kind == nkFlatten and digit().skip.kind == nkSkip
    check undefined[string, int]("v").kind == nkSettable
    check newline().kind == nkLeaf   # written by hand: nothing known of it

  test "a set over wide elements is a leaf":
    check oneOf[seq[int16], int16]({1'i16, 2'i16}, "small").kind == nkLeaf

suite "analysis":
  test "first sets and nullability of leaves and wrappers":
    proc firstOf(x: ParserBase): First = analyse(x).first(x)
    proc nullableOf(x: ParserBase): bool = analyse(x).nullable(x)
    let g = (digit().star & ch('x'))
    check firstOf(digit()).es == Digits.asBytes
    check not nullableOf(digit())
    check nullableOf(digit().star)
    check firstOf(g).es == (Digits + {'x'}).asBytes
    check not nullableOf(g)
    check firstOf(str("let")).es == {byte('l')}
    check nullableOf(epsilon[string]()) and nullableOf(endOfInput[string]())
    check firstOf(neg(ch('"'))).es == (Everything.without(byte('"')))
    check nullableOf(notAhead(digit()))
    let opt = digit().optional('0') / ch('y')
    check firstOf(opt).es == (Digits + {'y'}).asBytes
    check nullableOf(opt)

  test "hand-written leaves and callCC are unknown":
    let a = analyse(newline() & digit())
    check not a.first(newline()).known
    let traced = digit().callCC(proc (next: TextParser[char], ctx: Context[string]): Result[char] =
      next.parseOn(ctx))
    check not analyse(traced).first(traced).known

  test "a trimmer's elements come first":
    let
      t = digit().trim
      a = analyse(t)
    check a.first(t).es == (Digits + Whitespace).asBytes

  test "recursion reaches a fixpoint":
    let calc = calculator().resolve
    let a = analyse(calc)
    var primary: ParserBase
    for p in a.nodes:
      if p.name == "primary": primary = p
    check primary != nil
    check a.first(primary).es == (Digits + Whitespace + {'('}).asBytes
    check not a.nullable(primary)
    check a.first(calc).es == (Digits + Whitespace + {'('}).asBytes

  test "next sets":
    let
      a1 = ch('a')
      b1 = ch('b')
      g = a1 & b1.star & ch('c')
      a = analyse(g)
    check a.next(a1).es == {byte('b'), byte('c')}
    check a.next(b1).es == {byte('b'), byte('c')}
    check not a.next(a1).atEnd
    check a.next(g).atEnd and a.next(g).es == {}

suite "rewrites":
  test "a choice of sets is one set":
    let p = (ch('a') / ch('b') / ch('c')).optimize
    check p.kind == nkSet
    check p.elementSet == {byte('a'), byte('b'), byte('c')}
    check p.expected == "one of 'a', 'b', 'c'"
    check p.parse("b").value == 'b'
    check p.parse("d").message == "expected one of 'a', 'b', 'c' at 1:1"

  test "adjacent sets merge inside a mixed choice":
    let p = (ch('a') / ch('b') / str("cd").map((s: string) => 'c')).optimize
    check p.kind == nkChoice and p.children.len == 2
    check p.children[0].kind == nkSet
    check p.parse("cd").value == 'c' and p.parse("b").value == 'b'

  test "neg of a set is the complement, notAhead of a set is a test":
    let n = neg(ch('"')).optimize
    check n.kind == nkSet and n.elementSet == Everything.without(byte('"'))
    check n.parse("x").value == 'x' and not n.parse("\"").isSuccess
    let t = notAhead(digit()).optimize
    check t.kind == nkTest
    check t.parse("x").isSuccess and not t.parse("1").isSuccess and t.parse("").isSuccess

  test "a repetition of a set is a span":
    let p = digit().plus.optimize
    check p.kind == nkSpan and p.min == 1
    check p.parse("123x").value == @['1', '2', '3']
    check p.parse("x").message == "expected digit at 1:1"
    let s = digit().skip.star.optimize
    check s.kind == nkSpan
    check s.parse("12").pos == 2
    let f = digit().plus.flatten("number").optimize
    check f.children[0].kind == nkSpan
    check f.parse("42a").value == "42"

  test "a repetition of a choice beginning with sets is a span with a rest":
    let
      comment = (ch(';') & neg(newline()).star).skip
      ws = whitespace().skip / comment
      p = ws.star.optimize
    check p.kind == nkSpan
    check p.children.len == 1 and p.children[0].kind == nkSkip
    check p.parse("  ; hi\n  x").pos == 9
    check p.parse("x").pos == 0

  test "a set alternative behind an alternative that could take its element stays":
    let p = (str("ab").map((s: string) => 'a') / ch('a')).star.optimize
    check p.kind == nkRepeat   # 'a' may begin "ab", so the loop may not take it
    check p.parse("aab").value == @['a', 'a']

  test "trimmers become spans":
    let p = digit().trim.optimize
    check p.kind == nkTrim
    check p.children[1].kind == nkSpan and p.children[2].kind == nkSpan
    check p.children[1] == p.children[2]   # one span for the shared trimmer
    check p.parse("  7  ").pos == 5

  test "a choice is dispatched on the next element":
    let
      ident = letter().plus.flatten("identifier")
      p = (str("let") / str("if") / ident).optimize
    check p.isDispatched
    check p.parse("let").value == "let"
    check p.parse("ifx").value == "if"
    check p.parse("x").value == "x"
    check p.parse("1").message == "expected one of 'let', 'if', identifier at 1:1"
    check p.parse("").message == "expected one of 'let', 'if', identifier at 1:1"

  test "a nullable or unknown alternative is tried everywhere":
    let nl = item[string]((c: char) => c == '\n', "newline")   # by hand: unknown
    let p = (digit() / nl / epsilon[string]().map((n: Nothing) => ' ')).optimize
    check p.isDispatched
    check p.parse("\n").value == '\n'
    check p.parse("x").value == ' '
    check p.parse("").value == ' '

  test "a choice with nothing to dispatch on is left alone":
    check not (newline() / strIgnoreCase("x")).optimize.isDispatched
    check (newline() / str("x")).optimize.isDispatched   # 'x' is skipped where it cannot begin
    check not (epsilon[string, int](1) / epsilon[string, int](2)).optimize.isDispatched

  test "a shared beginning is cached":
    var calls = 0
    let ident = letter().plus.flatten("identifier").callCC(
      proc (next: TextParser[string], ctx: Context[string]): Result[string] =
        inc calls
        next.parseOn(ctx))
    let p = ((ident & ch(':')).pick(0) / (ident & ch('=')).pick(0)).optimize
    check ident.cacheWindow == 1
    check p.parse("ab=").value == "ab"
    check calls == 1
    calls = 0
    check not p.parse("ab!").isSuccess
    check calls == 1
    check p.parse("ab!").message == "expected one of ':', '=' at 1:3"

  test "a leaf beginning is not cached":
    let p = ((ch('a') & ch('b')) / (ch('a') & ch('c'))).optimize
    check p.children[0].children[0].cacheWindow == 0

  test "another source type is only resolved":
    let p = (oneOf[seq[int16], int16]({1'i16}, "one") / oneOf[seq[int16], int16]({2'i16}, "two")).optimize
    check p.kind == nkChoice
    check p.parse(@[2'i16]).value == 2

suite "caches":
  test "cached answers again at the same position, memoize at several":
    var calls = 0
    proc counting(): TextParser[char] =
      digit().callCC(proc (next: TextParser[char], ctx: Context[string]): Result[char] =
        inc calls
        next.parseOn(ctx))
    let c = counting().cached
    discard ((c & ch('a')) / (c & ch('b'))).parse("1b")
    check calls == 1
    calls = 0
    let m = counting().memoize(4)
    let p = (sequence((m, m, ch('x'))) / sequence((m, m, ch('y')))).pick(0)
    check p.parse("12y").value == '1'
    check calls == 2
    check p.parse("12z").message == "expected one of 'x', 'y' at 1:3"

  test "a cached failure is recorded again":
    let c = digit().cached
    let p = (c & ch('a')) / (c & ch('b'))
    check p.parse("x").message == "expected digit at 1:1"

  test "more input or a new epoch empties the cache":
    let
      c = str("ab").cached
      input = newInput("a")
    var ctx = Context[string](input: input, pos: 0)
    check not c.parseOn(ctx).isSuccess
    input.source.add 'b'
    input.stop = 2
    check c.parseOn(ctx).isSuccess
    input.source = "ax"
    input.stop = 2
    check c.parseOn(ctx).isSuccess         # stale: the same stop and position
    inc input.epoch
    check not c.parseOn(ctx).isSuccess     # told the source changed

suite "optimized grammars agree with their plain selves":
  test "the calculator":
    let
      plain = calculator().resolve
      fast = calculator().optimize
    check fast.kinds[nkSpan] > 0
    agree plain, fast, ["1 + 2 * (3 + 4)", " (8 - 2) / 3 ", "10 - 2 - 3", "1 + (2 * 3", "1 +\n  * 2",
                        "", "(", "7", "((((7))))", "1 2"]
    check fast.parse("1 +\n  * 2").message == "expected one of number, '(' at 2:3"

  test "json":
    let
      plain = jsonParser()
      fast = jsonParser().optimize
    agree plain, fast, ["""{"a": [1, 2.5e3, true, null, "xé"], "b": {}}""", "[1,]", "{\"a\" 1}",
                        "", "  42  ", "[", "\"open", "tru"], values = false

  test "sexp":
    let
      plain = sexpParser()
      fast = sexpParser().optimize
    agree plain, fast, ["(a (b c) \"d\" 'e ; comment\n 1)", "(a", ")", "", "x", "(a . b)"], values = false
