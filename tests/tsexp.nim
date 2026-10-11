import std/unittest
import petit_parser
import petit_parser/grammar/sexp

let p = sexpParser()

suite "sexp":
  test "a form with comments, nesting and every atom kind":
    let r = p.parse("""
      ; leading comment
      (foo bar 'baz   ; trailing comment
         (1 -2 1_000 "str\"i\\ng" 1+ - +) ()
         (nested(tight)"s"))
    """)
    check r.isSuccess
    let top = r.value
    check top.kind == skList and top.listVal.len == 6
    check top.listVal[0].stringVal == "foo" and not top.listVal[0].quoted
    check top.listVal[2].stringVal == "baz" and top.listVal[2].quoted
    let atoms = top.listVal[3].listVal
    check atoms[0].numberVal == 1 and atoms[1].numberVal == -2 and atoms[2].numberVal == 1000
    check atoms[3].kind == skString 
    check atoms[3].stringVal == "str\"i\\ng"
    check atoms[4].kind == skSymbol and atoms[4].stringVal == "1+"
    check atoms[5].stringVal == "-" and atoms[6].stringVal == "+"
    check top.listVal[4].listVal.len == 0
    let tight = top.listVal[5].listVal
    check tight.len == 3 and tight[1].listVal[0].stringVal == "tight" and tight[2].kind == skString

  test "quote":
    check p.parse("'(a b)").value.quoted
    check p.parse("'(a b)").value.listVal.len == 2
    check p.parse("' x").value.stringVal == "x"
    check p.parse("''x").value.quoted

  test "an atom too wide for an int is a symbol":
    check p.parse("123456789012345678901234").value.kind == skSymbol

  test "the whole input is one form":
    for bad in ["(foo", ")", "\"open", "(a) b", "", "; only a comment"]:
      check not p.parse(bad).isSuccess
    check p.parse("(a").message == "expected one of ''', '(', '\"', atom, ')' at 1:3"

  test "both paths agree":
    for input in ["(a (b) 'c)", "(a", "x ; c", "\"\\q\""]:
      check p.accepts(input) == p.parse(input).isSuccess
    for n in p.allParsers:
      check not (n of SettableParser[Sexp])