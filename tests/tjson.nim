import std/[strutils, tables, unittest]
import petit_parser
import petit_parser/grammar/json

let p = jsonParser()

suite "json":
  test "a document":
    let r = p.parse("""
      {
        "name": "bassline",
        "engines": { "node": ">=22.0.0" },
        "tags": [ "values", "ce", 3 ],
        "empty": [ ], "nothing": { },
        "flags": [true, false, null]
      }
    """)
    check r.isSuccess
    let doc = r.value
    check doc.kind == jkObject and doc.objectVal.len == 6
    check doc.objectVal["name"].stringVal == "bassline"
    check doc.objectVal["engines"].objectVal["node"].stringVal == ">=22.0.0"
    check doc.objectVal["tags"].arrayVal[2].numberVal == "3"
    check doc.objectVal["empty"].arrayVal.len == 0
    check doc.objectVal["nothing"].objectVal.len == 0
    check doc.objectVal["flags"].arrayVal[1].kind == jkBool
    check doc.objectVal["flags"].arrayVal[2].kind == jkNull

  test "numbers are kept as spelled":
    for n in ["0", "-0", "10", "-1.5", "1e3", "1.50E-2", "-0.5e+3"]:
      check p.parse(n).value.numberVal == n
    for bad in ["01", "1.", ".5", "+1", "1e", "-"]:
      check not p.parse(bad).isSuccess

  test "strings are decoded":
    check p.parse(""" "a " """).value.stringVal == "a "
    check p.parse(""" "a\"b\\c\/d\n\t" """).value.stringVal == "a\"b\\c/d\n\t"
    check p.parse(""" "\u0041\u00e9" """).value.stringVal == "Aé"
    check p.parse(""" "\ud83d\ude00!" """).value.stringVal == "😀!"
    check p.parse(""" "\u0041\u0042" """).value.stringVal == "AB"
    check not p.parse("\"a\nb\"").isSuccess
    check not p.parse(""" "\x" """).isSuccess
    check not p.parse(""" "open """).isSuccess

  test "the whole input is the document":
    for bad in ["[1,2,]", "{\"a\" 1}", "{\"a\":1,}", "\"x\" junk", "[1] [2]", ""]:
      check not p.parse(bad).isSuccess
    let m = p.parse("[1,2,]").message
    check "']'" notin m and "number" in m and "'{'" in m
    check m.endsWith("at 1:6")

  test "both paths agree":
    for input in ["[1, {\"a\": [true]}]", "[1,]", " null ", "\"\\u12\""]:
      check p.accepts(input) == p.parse(input).isSuccess
    for n in p.allParsers:
      check not (n of SettableParser[JsonValue])
