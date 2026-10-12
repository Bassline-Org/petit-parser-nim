## The bassline text reader for JavaScript. `nimble reader` builds
## `dist/bassline_text.mjs`, which exports `parseBassline(text)`. It
## answers `{values: [...]}`, each value a plain object with `kind` as a
## string, `mark` where set, `text`, `bytes` as a Uint8Array, `items` or
## `entries` as arrays, and `start` and `stop` offsets on the top level
## values, or `{error: message, offset, line, column}`. Dialect blocks
## read with the standard dialects.

import std/[jsffi, strutils]
import ../petit_parser
import ./grammar/extended_bassline_text

proc document(): Parser[seq[Token[BlNode]]] =
  let ws = space()
  extendedValue(standardDialects()).token.trim(ws).star.trim(ws).complete.resolve

let doc = document()

proc toUint8Array(bs: seq[byte]): JsObject {.importjs: "new Uint8Array(#)".}

proc toJsValue(n: BlNode): JsObject =
  result = newJsObject()
  result.kind = cstring(($n.kind)[2 .. ^1].toLowerAscii)
  if n.mark:
    result.mark = true
  case n.kind
  of bkNil: discard
  of bkInt, bkText, bkSymbol: result.text = cstring(n.text)
  of bkBytes: result.bytes = toUint8Array(n.bytes)
  of bkList, bkRecord, bkSet:
    var items = newSeq[JsObject]()
    for i in n.items: items.add toJsValue(i)
    result.items = items
  of bkDict:
    var entries = newSeq[JsObject]()
    for (k, v) in n.entries:
      entries.add @[toJsValue(k), toJsValue(v)].toJs
    result.entries = entries

proc parseBassline*(text: cstring): JsObject {.exportc.} =
  let r = doc.parse($text)
  result = newJsObject()
  if r.isSuccess:
    var values = newSeq[JsObject]()
    for t in r.value:
      var v = toJsValue(t.value)
      v.start = t.start
      v.stop = t.stop
      values.add v
    result.values = values
  else:
    let (line, column) = r.input.text.lineCol(r.pos)
    result.error = cstring(r.message)
    result.offset = r.pos
    result.line = line
    result.column = column

{.emit: "export { parseBassline }".}
