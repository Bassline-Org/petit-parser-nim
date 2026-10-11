import std/[os, unittest]
import petit_parser
import petit_parser/grammar/bassline_text

let
  one = basslineParser()
  doc = basslineDocument()
  corpus = doc.parse(readFile(currentSourcePath.parentDir / "bassline-corpus.bl"))

proc head(c: BlNode): string =
  if c.items[0].kind == bkSymbol: c.items[0].text else: ""

suite "bassline text":
  test "the corpus reads as a document":
    check corpus.isSuccess
    check corpus.value.len == 150

  test "reads cases read as their value":
    var seen = 0
    for c in corpus.value:
      if c.head == "reads":
        let r = one.parse(c.items[1].text)
        check r.isSuccess and r.value == c.items[2]
        inc seen
    check seen == 17

  test "refuses and incomplete cases fail":
    var seen = 0
    for c in corpus.value:
      if c.head in ["refuses", "incomplete"]:
        check not one.parse(c.items[1].text).isSuccess
        inc seen
    check seen == 42

  test "document cases read as their values":
    for c in corpus.value:
      if c.head == "document":
        let r = doc.parse(c.items[1].text)
        check r.isSuccess and r.value == c.items[2].items

  test "spellings are normalised":
    check one.parse("0xDE_AD").value.bytes == @[0xde'u8, 0xad]
    check one.parse("-1_000").value.text == "-1000"
    check one.parse("9223372036854775808").value.text == "9223372036854775808"
    check one.parse("'a\\'b\\n'").value.text == "a'b\n"
    check one.parse("\"say \\\"hi\\\"\"").value.text == "say \"hi\""

  test "marks":
    check one.parse("!{a: 1}").value.mark
    check not one.parse("{a: 1}").value.mark
    let r = one.parse("(f go! !(g) \"s\"! 0x!)").value
    check r.items[1].mark and r.items[2].mark and r.items[3].mark and r.items[4].mark
    check not r.items[0].mark
    check r.items[4].kind == bkBytes and r.items[4].bytes.len == 0

  test "sets and dicts keep their members in order":
    let s = one.parse("{b a}").value
    check s.kind == bkSet and s.items[0].text == "b"
    let d = one.parse("{b: 1 a: 2}").value
    check d.kind == bkDict and d.entries[0][0].text == "b" and d.entries[1][1].text == "2"

  test "both paths agree":
    for input in ["[1 2", "{a: 1 a: 2}", "(f go! !(g))", "0x123", "-0", "a!b", "; c\n5"]:
      check one.accepts(input) == one.parse(input).isSuccess
    for n in one.allParsers:
      check not (n of SettableParser[BlNode])
