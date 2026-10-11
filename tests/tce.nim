import std/[os, unittest]
import petit_parser
import petit_parser/grammar/[bassline_text, bassline_ce]

let
  here = currentSourcePath.parentDir
  one = ceParser()
  corpus = ceDocument().parse(readFile(here / "bassline-corpus.blb"))

proc head(c: BlNode): string =
  if c.items[0].kind == bkSymbol: c.items[0].text else: ""

suite "canonical encoding, unvalidated":
  test "the corpus reads as a document":
    check corpus.isSuccess
    check corpus.value.len == 150

  test "ce cases decode to their value":
    var seen = 0
    for c in corpus.value:
      if c.head == "ce":
        let r = one.parse(c.items[3].bytes)
        check r.isSuccess and r.value == c.items[2]
        inc seen
    check seen == 53

  test "starved input fails":
    var seen = 0
    for c in corpus.value:
      if c.head == "starved":
        check not one.parse(c.items[2].bytes).isSuccess
        inc seen
    check seen == 6

  test "only structural rules are enforced":
    let structural = ["invalid-tag", "end-with-bits", "end-at-top", "stranded-key", "length-bits"]
    for c in corpus.value:
      if c.head == "reject":
        let accepted = one.parse(c.items[2].bytes).isSuccess
        check accepted == (c.items[3].text notin structural)

  test "lengths in every form":
    check one.parse("\x33abc").value.text == "abc"
    check one.parse("\x37\x08abcdefgh").value.text == "abcdefgh"
    check one.parse("\x37\xff\x00\x00\x00\x02ab").value.text == "ab"
    check one.parse("\x5a\xde\xad").value.bytes == @[0xde'u8, 0xad]
    check one.parse("\x5a\xde\xad").value.mark
    check one.parse("\x37\x08abc").message == "expected a whole payload at 1:3"
    check one.parse("\x00").message == "expected a value header at 1:1"
    check one.parse("\x61\xa0").message == "expected a value header at 1:1"

  test "both paths agree":
    for input in ["\x60\x21\x31\xa0", "\x60\x21", "\x80\x41\x61\xa0", "", "\xa0"]:
      check one.accepts(input) == one.parse(input).isSuccess
    for n in one.allParsers:
      check not (n of SettableParser[BlNode])
