import std/[math, strutils, sugar, unittest]
import petit_parser

proc arith(): Parser[int] =
  let b = newExpressionBuilder[int]()
  b.primitive(digit().plus.flatten("number").trim.map((s: string) => parseInt(s)))
  b.group.wrapper(ch('(').trim, ch(')').trim, (l: char, v: int, r: char) => v)
  b.group.prefix(ch('-').trim, (op: char, a: int) => -a)
  b.group.postfix(ch('!').trim, (a: int, op: char) => fac(a))
  b.group.right(ch('^').trim, (a: int, op: char, b: int) => a ^ b)
  let product = b.group
  product.left(ch('*').trim, (a: int, op: char, b: int) => a * b)
  product.left(ch('/').trim, (a: int, op: char, b: int) => a div b)
  let sum = b.group
  sum.left(ch('+').trim, (a: int, op: char, b: int) => a + b)
  sum.left(ch('-').trim, (a: int, op: char, b: int) => a - b)
  b.build.complete

suite "expression builder":
  let p = arith()

  test "precedence and associativity":
    check p.parse("1 + 2 * 3").value == 7
    check p.parse("(1 + 2) * 3").value == 9
    check p.parse("10 - 2 - 3").value == 5
    check p.parse("2 ^ 3 ^ 2").value == 512
    check p.parse("2 * 3!").value == 12
    check p.parse("-2 ^ 2").value == 4
    check p.parse("-(1 + 2)").value == -3
    check p.parse(" - - 4 ").value == 4

  test "both paths agree and the loopback is resolved":
    for input in ["1+(2", "1 +", "(3)!", "2^", ""]:
      check p.accepts(input) == p.parse(input).isSuccess
    for n in p.allParsers:
      check not (n of SettableParser[int])

  test "failures name the operands expected":
    let m = p.parse("1 +").message
    check "number" in m and "'('" in m and "'-'" in m
    check m.endsWith("at 1:4")
