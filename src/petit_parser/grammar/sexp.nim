## S-expressions: atoms, "strings", (lists) and 'quoted forms, with `;`
## comments. An atom is a run of non-delimiters; one that reads as an
## integer is a number, any other is a symbol.

import std/[parseutils, sugar, strutils]
import ../parser

type
  SexpKind* = enum
    skSymbol, skNumber, skString, skList

  Sexp* = object
    quoted*: bool
    case kind*: SexpKind
    of skSymbol, skString: stringVal*: string
    of skNumber: numberVal*: int
    of skList: listVal*: seq[Sexp]

proc atom(text: string): Sexp =
  var n: int
  try:
    if text.parseInt(n) == text.len: return Sexp(kind: skNumber, numberVal: n)
  except ValueError: discard
  Sexp(kind: skSymbol, stringVal: text)

proc quoting(s: Sexp): Sexp =
  result = s
  result.quoted = true

proc escaped(c: char): string =
  case c
  of 'n': "\n"
  of 't': "\t"
  else: $c

proc sexpParser*(): Parser[Sexp] =
  let
    comment = (ch(';') & neg(newline()).star).skip
    ws = chars(" \t\r\n", "whitespace").skip / comment
    sexp = undefined[Sexp]("sexp")
    form = sexp.trim(ws)

    quote = (ch('\'') & form).pick(1).map(quoting)
    escape = (str("\\") & chars("\"\\nt", "escape")).map(m => escaped(m[1]))
    run = noneOf("\"\\", "character").plus.flatten
    text = delimited(ch('"'), ch('"'), (run / escape).star)
      .map(m => Sexp(kind: skString, stringVal: m.join))
    atomp = noneOf(" \t\r\n()'\";", "atom").plus.flatten.map(atom)
    list = delimited(ch('('), ch(')'), form.star)
      .map(m => Sexp(kind: skList, listVal: m))

  sexp.define(quote / list / text / atomp)
  form.complete.resolve