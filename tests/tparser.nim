import std/[strutils, sugar, unittest]
import petit_parser

proc apply(a: int, op: char, b: int): int =
  case op
  of '+': a + b
  of '-': a - b
  of '*': a * b
  else: a div b

proc fold(l: Separated[int, char]): int = l.foldLeft(apply)

proc calculator(): Parser[int] =
  let expr = undefined[int]("expr")
  let number = digit().plus.flatten("number").map((s: string) => parseInt(s)).trim
  let parens = sequence((ch('(').trim, expr, ch(')').trim)).map((t: (char, int, char)) => t[1])
  let primary = (number / parens).named("primary")
  let term = primary.plusSeparated(pattern("*/").trim).map(fold)
  expr.define(term.plusSeparated(pattern("+-").trim).map(fold))
  expr.complete.resolve

template agree(p: untyped, inputs: openArray[string]) =
  for input in inputs:
    let slow = p.parse(input)
    let fast = p.fastParseOn(Context(input: Input(text: input)))
    check (if slow.isSuccess: slow.pos else: -1) == fast

suite "leaves":
  test "chars and literals":
    check ch('a').parse("abc").value == 'a'
    check pattern("a-z").parse("q").value == 'q'
    check not pattern("^0-9").parse("5").isSuccess
    check str("let").parse("let x").value == "let"
    check not str("let").parse("le").isSuccess
    check endOfInput().parse("").isSuccess
    check noneOf("ab", "not a or b").parse("c").value == 'c'
    check between('a', 'f').parse("d").value == 'd'
    check word().plus.flatten.parse("ab_1 x").value == "ab_1"
    check uppercase().parse("Q").value == 'Q' and not lowercase().parse("Q").isSuccess

  test "ignore case, newline, epsilon, failure, position":
    check strIgnoreCase("select").parse("SeLeCt *").value == "SeLeCt"
    check not strIgnoreCase("select").parse("selec").isSuccess
    check newline().parse("\r\nx").pos == 2 and newline().parse("\nx").pos == 1
    check not newline().parse("x").isSuccess
    check epsilon().parse("x").pos == 0
    check epsilon(7).parse("").value == 7
    check not failure[int]("nope").parse("x").isSuccess
    check failure[int]("nope").parse("x").message == "expected nope at 1:1"
    check (ch('a') & position()).parse("ab").value == ('a', 1)

  test "a failed result has no value":
    expect ParseError:
      discard ch('a').parse("b").value

suite "combinators":
  test "sequence and choice":
    let p = ch('a') & ch('b')
    check p.parse("ab").value == ('a', 'b')
    check ((str("ab") / str("a")).parse("a")).value == "a"
    let four = sequence((ch('a'), digit().plus.flatten, str("-"), ch('z').optional))
    check four.parse("a12-").value == ('a', "12", "-", none(char))
    check four.children.len == 4
    check not four.parse("a-").isSuccess
    check sequence((ch('a'),)).parse("a").value == ('a',)

  test "choice flattens unnamed choices only":
    let abc = ch('a') / ch('b') / ch('c')
    check abc.children.len == 3
    let ab = (ch('a') / ch('b')).named("ab")
    check (ab / ch('c')).children.len == 2

  test "possessive repetition":
    check digit().star.parse("123x").value == @['1', '2', '3']
    check not digit().plus.parse("x").isSuccess
    check digit().times(2).parse("123").pos == 2
    check digit().repeat(1, 2).parse("123").value.len == 2
    check ch('a').optional.star.parse("aab").pos == 2

  test "lazy repetition stops before its limit":
    let body = anyChar().starLazy(ch('"')).flatten
    let quoted = sequence((ch('"'), body, ch('"'))).map((t: (char, string, char)) => t[1])
    check quoted.parse("\"hi there\" rest").value == "hi there"
    check not quoted.parse("\"open").isSuccess
    check anyChar().repeatLazy(ch('!'), 1, 2).parse("ab!").value == @['a', 'b']
    check not anyChar().repeatLazy(ch('!'), 1, 2).parse("abc!").isSuccess
    check ch('a').optional.starLazy(ch('!')).parse("b").message == "expected one of 'a', '!' at 1:1"
    agree anyChar().starLazy(ch('!')), ["ab!", "!", "ab", ""]

  test "greedy repetition backs up to its limit":
    let upToLast = anyChar().starGreedy(ch('!')).flatten
    check upToLast.parse("a!b!c").value == "a!b"
    check anyChar().plusGreedy(ch('!')).parse("!").message ==
      "expected one of any character, '!' at 1:2"
    check anyChar().repeatGreedy(ch('!'), 0, 1).parse("a!").value == @['a']
    check not anyChar().repeatGreedy(ch('!'), 0, 1).parse("abc!").isSuccess
    agree anyChar().starGreedy(ch('!')), ["a!b!c", "!", "abc", ""]

  test "separated repetition":
    let list = digit().plusSeparated(ch(',').trim)
    let r = list.parse("1, 2,3,").value
    check r.elements == @['1', '2', '3'] and r.separators.len == 2
    check list.parse("1, 2,3,").pos == 6
    check digit().starSeparated(ch(',')).parse("x").value.elements.len == 0
    check not list.parse("x").isSuccess
    check digit().timesSeparated(ch(','), 2).parse("1,2,3").pos == 3
    let minus = digit().map(c => parseInt($c)).plusSeparated(ch('-'))
    check minus.parse("9-3-2").value.foldLeft(apply) == 4
    check minus.parse("9-3-2").value.foldRight(apply) == 8
    agree list, ["1,2", "1,", "", "1, 2 ,3"]

  test "optional, map, flatten, token":
    check ch('x').optional.parse("y").value.isNone
    check digit().optional('0').parse("y").value == '0'
    check (digit().plus.flatten ==> (s => s.len)).parse("4242").value == 4
    let t = letter().plus.flatten.token.parse("hello world").value
    check t.value == "hello" and t.start == 0 and t.stop == 5 and t.text == "hello"

  test "lookahead consumes nothing":
    check ahead(ch('a')).parse("ab").pos == 0
    check notAhead(ch('a')).parse("b").isSuccess
    check not notAhead(ch('a')).parse("a").isSuccess

  test "neg consumes one element that is not p":
    let body = neg(ch('"')).star.flatten
    check body.parse("ab\"c").value == "ab"
    let comment = sequence((str("/*"), neg(str("*/")).star.flatten, str("*/")))
    check comment.parse("/* a * b */x").value[1] == " a * b "
    check not neg(ch('x')).parse("").isSuccess
    check neg(ch('x')).parse("x").message == "expected not 'x' at 1:1"
    check neg(ch(0xFF'u8), byte).star.parse([1'u8, 2, 0xFF]).value == @[1'u8, 2]
    agree neg(str("*/")).star, ["a*/", "*/", "ab", "", "*"]

  test "where filters with its own expectation":
    let num = digit().map((c: char) => parseInt($c))
    let even = num.where((n) => n mod 2 == 0, "even digit")
    check even.parse("4").value == 4
    check even.parse("3").message == "expected even digit at 1:1"
    check not even.accepts("3")
    agree even, ["4", "3", "x"]

  test "callCC wraps a delegate":
    var calls = 0
    let traced = digit().callCC(proc (next: (Context) -> Result[char], ctx: Context): Result[char] =
      inc calls
      next(ctx))
    check traced.plus.parse("12x").value == @['1', '2']
    check calls == 3

  test "trim skips its trimmers repeatedly, on both sides":
    let comment = str("#") & noneOf("\n", "comment").star & newline()
    let p = digit().trim(whitespace().skip / comment.skip)
    check p.parse("  # a\n # b\n 7 # c\n").pos == 18
    check p.parse("7").value == '7'
    check (digit().trim(ch('<'), ch('>')) & ch('!')).parse("<<7>>!").pos == 6
    agree p, ["  7  ", "7", " # x\n7", "x"]

suite "both parse paths agree":
  test "fast path matches slow path":
    agree (str("ab") / ch('a').flatten) & digit().star & ch('z').optional,
          ["ab12z", "a", "ab", "x", "a9", ""]

  test "resolved delegates follow the rewired child":
    let calc = calculator()
    for input in ["1+(2*3)", "(1", "7"]:
      check calc.accepts(input) == calc.parse(input).isSuccess

suite "recursion and resolve":
  test "calculator":
    let calc = calculator()
    check calc.parse("1 + 2 * (3 + 4)").value == 15
    check calc.parse(" (8 - 2) / 3 ").value == 2
    check calc.parse("10 - 2 - 3").value == 5
    check calc.accepts("1+(2*3)")
    check not calc.accepts("1+")

  test "resolve removes every forward reference and keeps cycles":
    let calc = calculator()
    for n in calc.allParsers:
      check not (n of SettableParser[int])
    # still cyclic: a child of `primary` leads back to `primary`
    let primary = block:
      var found: ParserBase
      for n in calc.allParsers:
        if n.name == "primary": found = n
      found
    var cycles = false
    for c in primary.children:
      if c.allParsers.contains(primary): cycles = true
    check cycles   # primary -> parens -> expr -> term -> primary
    check calc.parse("((((7))))").value == 7

  test "unresolved reference is a build error":
    let p = undefined[int]("missing")
    expect ValueError:
      discard (p & ch('a')).resolve

suite "bytes":
  test "byte leaves and byte input":
    let frame = sequence((ch(0xA0'u8), bytes({0x00'u8 .. 0x7F'u8}, "ascii").star, str([0xFF'u8])))
    let r = frame.parse([0xA0'u8, 0x41, 0x42, 0xFF])
    check r.isSuccess and r.value[0] == 0xA0'u8 and r.value[1] == @[0x41'u8, 0x42]
    check not frame.parse([0xA0'u8, 0x80, 0xFF]).isSuccess
    check anyByte().star.flatten.parse([0x00'u8, 0xFF]).value == "\x00\xFF"
    check frame.accepts([0xA0'u8, 0xFF])

suite "errors":
  test "furthest failure lists every expectation":
    let r = calculator().parse("1 + (2 * 3")
    check not r.isSuccess
    check r.pos == 10
    let m = r.message
    check "')'" in m
    check "[*/]" in m
    check "[+-]" in m
    check m.endsWith("at 1:11")

  test "show messages":
    echo "    ", calculator().parse("1 + (2 * 3").message
    echo "    ", calculator().parse("1 +\n  * 2").message

  test "multi-line position":
    let r = calculator().parse("1 +\n  * 2")
    check r.message.endsWith("at 2:3")