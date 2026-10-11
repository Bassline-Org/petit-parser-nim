## The canonical encoding (data-model.org, "Canonical Binary Encoding")
## read into the same tree the text grammar builds, without validation.
## Lengths are taken as stated, and integers, UTF-8, order and duplicates
## are not checked. Only the structure has to hold: a known tag, length
## bits only where there is a length, a payload that is all there, and a
## frame closed by END.

import std/sugar
import ../parser
import ./bassline_text

type Header = tuple[tag, lll: uint8, mark: bool]

proc headerData(b: byte): Header =
  let
    tag: uint8 = b shr 4
    mark: bool = (b and 0x08) != 0
    lll: uint8 = b and 0x07
  (tag, lll, mark)

func length(text: string, pos: var int, lll: uint8): int =
  ## The payload length after a header: `lll` itself, or the medium or
  ## large form it announces, read from `pos`. -1 when that is cut short.
  result = int lll
  if result < 7: return
  if pos >= text.len: return -1
  result = text[pos].int
  inc pos
  if result == 255:
    if pos + 4 > text.len: return -1
    result = 0
    for i in 0 .. 3: result = result shl 8 or text[pos + i].int
    pos += 4

func atom(head: Header, payload: openArray[char]): BlNode =
  case head.tag
  of 2: BlNode(kind: bkInt, mark: head.mark, text: payload.substr)
  of 3: BlNode(kind: bkText, mark: head.mark, text: payload.substr)
  of 4: BlNode(kind: bkSymbol, mark: head.mark, text: payload.substr)
  else: BlNode(kind: bkBytes, mark: head.mark, bytes: @(payload.toOpenArrayByte(0, payload.high)))

proc ceValue(): Parser[BlNode] =
  ## One header read, then a dispatch on its tag.
  let
    value = undefined[BlNode]("value")
    stop = ch(byte(0xA0))
    members = value.star & stop
    entries = (value & value).star & stop
    header = failure[Nothing]("a value header")
    payload = failure[Nothing]("a whole payload")

  proc scalar(head: Header, ctx: Context): Result[BlNode] =
    var pos = ctx.pos
    let n = ctx.input.text.length(pos, head.lll)
    if n < 0 or pos + n > ctx.input.text.len: return fail[BlNode](payload, ctx.at(pos))
    succeed(atom(head, ctx.input.text.toOpenArray(pos, pos + n - 1)), pos + n)

  proc framed(head: Header, ctx: Context): Result[BlNode] =
    if head.tag == 8:
      var r = entries.parseOn(ctx)
      if not r.isSuccess: return failedAs(BlNode, r)
      var inside = r.take
      succeed(BlNode(kind: bkDict, mark: head.mark, entries: move(inside[0])), r.pos)
    else:
      var r = members.parseOn(ctx)
      if not r.isSuccess: return failedAs(BlNode, r)
      var inside = r.take
      let v = case head.tag
              of 6: BlNode(kind: bkList, mark: head.mark, items: move(inside[0]))
              of 7: BlNode(kind: bkRecord, mark: head.mark, items: move(inside[0]))
              else: BlNode(kind: bkSet, mark: head.mark, items: move(inside[0]))
      succeed(v, r.pos)

  let node = anyByte().map(headerData).callCC(
    proc (next: Parser[Header], ctx: Context): Result[BlNode] =
      let h = next.parseOn(ctx)
      if not h.isSuccess: return failedAs(BlNode, h)
      let head = h.value
      case head.tag
      of 2, 3, 4, 5: scalar(head, ctx.at(h.pos))
      of 1, 6, 7, 8, 9:
        if head.lll != 0: fail[BlNode](header, ctx)
        elif head.tag == 1: succeed(BlNode(kind: bkNil, mark: head.mark), h.pos)
        else: framed(head, ctx.at(h.pos))
      else: fail[BlNode](header, ctx))
  value.define(node)
  value

proc ceParser*(): Parser[BlNode] =
  ## Exactly one value.
  ceValue().complete.resolve

proc ceDocument*(): Parser[seq[BlNode]] =
  ## A bare concatenation of values, as in a `.blb` file.
  ceValue().star.complete.resolve