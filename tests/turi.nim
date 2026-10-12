import std/unittest
import petit_parser
import petit_parser/grammar/[bassline_text, extended_bassline_text, uri]

let
  p = uriParser()
  bl = basslineParser()

template reads(text, expected: string) =
  check p.parse(text).value == bl.parse(expected).value

suite "references":
  test "a url with every slot":
    reads "https://user:pw@example.com:8443/a/b%20c?x=1&y=2#frag",
      """{scheme: https who: {user: "user:pw" name: "example.com" port: 8443}
          where: ["a" "b c"] how: [("x" "1") ("y" "2")] which: "frag"}"""

  test "hosts and paths":
    reads "http://[2001:db8::1]:80/", """{scheme: http who: {name: "2001:db8::1" port: 80} where: [""]}"""
    reads "https://example.com", """{scheme: https who: {name: "example.com"}}"""
    reads "file:///etc/hosts", """{scheme: file who: {name: ""} where: ["etc" "hosts"]}"""
    reads "../a/b?x", """{where: [".." "a" "b"] how: [("x" nil)]}"""

  test "schemes that pack the party into the path":
    reads "mailto:alice@example.com?subject=hi",
      """{scheme: mailto who: {user: "alice" name: "example.com"} how: [("subject" "hi")]}"""
    reads "urn:isbn:0451450523", """{scheme: urn who: {name: "isbn"} where: ["0451450523"]}"""
    reads "did:web:example.com:user:alice",
      """{scheme: did who: {name: "web"} where: ["example.com" "user" "alice"]}"""
    reads "tel:+15550100", """{scheme: tel where: ["+15550100"]}"""
    reads "magnet:?xt=urn:btih:abc", """{scheme: magnet how: [("xt" "urn:btih:abc")]}"""
    reads "ipfs://bafybeigdyrzt/readme.md",
      """{scheme: ipfs who: {name: "bafybeigdyrzt"} where: ["readme.md"]}"""
    reads "data:text/plain;base64,SGk=", """{scheme: data where: ["text" "plain;base64,SGk="]}"""

  test "addresses outside the uri syntax":
    reads "git@github.com:goose/bassline.git",
      """{who: {user: "git" name: "github.com"} where: ["goose" "bassline.git"]}"""
    reads "alice@example.com", """{who: {user: "alice" name: "example.com"}}"""

  test "refusals":
    check not p.parse("http://exa mple.com").isSuccess
    check not p.parse("https://example.com/%zz").isSuccess
    check p.parse("").isSuccess   # the empty reference: nothing said, every slot absent

  test "as a dialect block":
    let r = extendedParser(standardDialects()).parse("(link lang uri [[ https://example.com/a?b=1 ]])")
    check r.value == bl.parse("""(link {scheme: https who: {name: "example.com"} where: ["a"] how: [("b" "1")]})""").value

  test "both paths agree":
    for input in ["https://a.b/c", "git@h:p", "x@y", "../z", "", "mailto:a@b"]:
      check p.accepts(input) == p.parse(input).isSuccess
