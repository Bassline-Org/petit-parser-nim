import std/[os, sugar, tables, unittest]
import petit_parser
import petit_parser/grammar/extended_bassline_text

proc sym(s: string): BlNode = BlNode(kind: bkSymbol, text: s)
proc num(s: string): BlNode = BlNode(kind: bkInt, text: s)
proc txt(s: string): BlNode = BlNode(kind: bkText, text: s)
proc list(items: varargs[BlNode]): BlNode = BlNode(kind: bkList, items: @items)
proc rec(items: varargs[BlNode]): BlNode = BlNode(kind: bkRecord, items: @items)

proc words(): Parser[BlNode] =
  word().plus.flatten("word").map(sym).trim.star.map(ws => list(ws))

var dialects = standardDialects()
dialects["words"] = words()

let
  one = extendedParser(dialects)
  doc = extendedDocument(dialects)

suite "extended bassline text":
  test "a block reads with its dialect":
    check one.parse("lang sexp [[ (a 1 \"x\") ]]").value == list(sym"a", num"1", txt"x")
    check one.parse("lang words [[ hello world ]]").value == list(sym"hello", sym"world")

  test "blocks stand where values do":
    let r = one.parse("""(q lang json [[ {"b": [1, 2], "a": null} ]] lang sexp [[ 'x ]]!)""").value
    check r.items.len == 3
    check r.items[1] == BlNode(kind: bkDict, entries: @[(txt"a", BlNode(kind: bkNil)),
                                                         (txt"b", list(num"1", num"2"))])
    check r.items[2] == BlNode(kind: bkRecord, mark: true, items: @[sym"quote", sym"x"])

  test "long brackets hold the shorter close":
    check one.parse("lang sexp [=[ \"]]\" ]=]").value == txt"]]"

  test "lang is reserved":
    check one.parse("language").value == sym"language"
    check one.parse("'lang'").value == sym"lang"
    check not one.parse("lang").isSuccess

  test "failures":
    check one.parse("lang nope [[ x ]]").message == "expected a known dialect at 1:6"
    check one.parse("lang sexp [[ (a").message == "expected ']]' at 1:16"
    check one.parse("lang words [[ hello, world ]]").message ==
      "expected one of word, the end of the block at 1:20"
    check one.parse("lang json [[ 1.5 ]]").message == "expected integers only at 1:18"
    check one.parse("lang sexp [[ (a ]]").message == "expected one of ''', '(', '\"', atom, ')' at 1:17"

  test "the corpus still reads":
    let corpus = doc.parse(readFile(currentSourcePath.parentDir / "bassline-corpus.bl"))
    check corpus.isSuccess and corpus.value.len == 150

  test "both paths agree":
    for input in ["lang sexp [[ (a) ]]", "lang nope [[ x ]]", "[lang words [[ a b ]] 1]", "lang"]:
      check one.accepts(input) == one.parse(input).isSuccess

  test "reads at compile time":
    const r = extendedParser(standardDialects()).parse("(x lang sexp [[ (a 1) ]])").value
    check r == rec(sym"x", list(sym"a", num"1"))
