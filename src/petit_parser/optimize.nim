## `optimize`: rewrites after `resolve` that keep what a grammar reads and
## answers and change how it is read, so a grammar can be written the
## plain way. Each rewrite is a shape found in the graph and a node that
## does the same work in fewer steps, and all of them rest on `analysis`:
##
## - a choice of sets is one set, `neg` of a set is its complement and
##   `notAhead` of a set is a `test`;
## - a repetition of a set, or of a choice that begins with sets, is a
##   `span`, one loop over the elements with the other alternatives read
##   as before; a trimmer becomes the span of itself;
## - a choice is told, for each next element, which alternatives can
##   begin with it (`dispatch`), from their first sets; a miss fails as
##   the alternatives would have;
## - a node that begins several alternatives of one choice is `cached`,
##   so the alternative tried next does not read it again.
##
## The analyses mean something for sources whose element type is one byte
## wide; for any other source `optimize` is `resolve`.

import std/[sequtils, sugar, tables]
import ./parser, ./analysis

proc fromBytes[E](bs: set[byte]): set[E] =
  for b in bs: result.incl E(b)

const
  Leaves = {nkLeaf, nkSet, nkLiteral, nkAny, nkEnd, nkEpsilon, nkFailure, nkTest, nkSpan,
            nkFlatten, nkSkip, nkNeg}
    ## nodes that fail as themselves and are not worth caching

# ---------------------------------------------------------------------------
# Sets

proc isSet(p: ParserBase): bool = p.kind == nkSet
proc isSkippedSet(p: ParserBase): bool = p.kind == nkSkip and p.children[0].kind == nkSet

proc setAlgebra[S](p: ParserBase): ParserBase =
  ## `neg(set)`, `notAhead(set)` and choices of sets, as single nodes.
  type E = elementOf(S)
  result = p
  case p.kind
  of nkNeg:
    let c = p.children[0]
    if c.isSet:
      result = oneOf[S, E](fromBytes[E](Everything - c.elementSet), p.expected)
  of nkNotAhead:
    let c = p.children[0]
    if c.isSet:
      result = test[S, E](fromBytes[E](c.elementSet), p.expected)
  of nkChoice:
    let alts = p.children
    if alts.anyIt(it.isSet) and alts.len > 1:
      var
        merged: seq[Parser[S, E]]
        pending: seq[ParserBase]   # adjacent sets to fold into one
        changed = false
      template flush() =
        if pending.len == 1: merged.add Parser[S, E](pending[0])
        elif pending.len > 1:
          var
            es: set[byte]
            names: seq[string]
          for q in pending:
            es = es + q.elementSet
            if q.expected notin names: names.add q.expected
          merged.add oneOf[S, E](fromBytes[E](es), names.alternatives)
          changed = true
        pending.setLen 0
      for alt in alts:
        if alt.isSet: pending.add alt
        else:
          flush()
          merged.add Parser[S, E](alt)
      flush()
      if changed:
        if merged.len == 1:
          result = merged[0]
          result.expected = p.expected
        else:
          result = choice(merged)
        result.name = p.name
        if p.name.len > 0: result.expected = p.name
  else: discard

# ---------------------------------------------------------------------------
# Spans

proc spanOver[S](a: Analysis, item: ParserBase, min, max: int, expected: string): ParserBase =
  ## The span that reads `item` repeated, or nil when `item` does not
  ## begin with sets it can take as a loop.
  type E = elementOf(S)
  if item.isSet:
    return span[S, E, E](fromBytes[E](item.elementSet), min, max, nil, (e: E) => e, expected)
  if item.isSkippedSet:
    return span[S, E, Nothing](fromBytes[E](item.children[0].elementSet), min, max, nil,
                               (e: E) => Nothing(), expected)
  if item.kind != nkChoice: return nil
  let alts = item.children
  # a set alternative is taken by the loop only where no alternative before
  # it could match the same element
  var
    es: set[byte]
    taken: seq[bool]
    skipped = false
    kinds: set[NodeKind]
  for i, alt in alts:
    var ok = alt.isSet or alt.isSkippedSet
    if ok:
      let mine = if alt.isSet: alt.elementSet else: alt.children[0].elementSet
      for j in 0 ..< i:
        if taken[j]: continue
        let f = a.first(alts[j])
        if not f.known or f.nullable or (f.es * mine) != {}:
          ok = false
          break
      if ok:
        es = es + mine
        kinds.incl alt.kind
    taken.add ok
  if es == {} or kinds.len != 1: return nil
  skipped = nkSkip in kinds
  var rest: seq[ParserBase]
  for i, alt in alts:
    if not taken[i]: rest.add alt
  template build(R: typedesc, mk: untyped): ParserBase =
    var r: Parser[S, R]
    if rest.len == 1: r = Parser[S, R](rest[0])
    elif rest.len > 1:
      r = choice(rest.mapIt(Parser[S, R](it)))
      r.name = item.name
      if item.name.len > 0: r.expected = item.name
    span[S, E, R](fromBytes[E](es), min, max, r, mk, expected)
  if skipped: build(Nothing, (e: E) => Nothing())
  else: build(E, (e: E) => e)

proc spans[S](a: Analysis, p: ParserBase): ParserBase =
  ## A possessive repetition that can be a span is one.
  result = p
  if p.kind == nkRepeat:
    let s = spanOver[S](a, p.children[0], p.min, p.max, p.expected)
    if not s.isNil: result = s

proc trims[S](a: Analysis, made: var Table[ParserBase, ParserBase], p: ParserBase): ParserBase =
  ## A trimmer is skipped as often as it matches, which is a span of it.
  result = p
  if p.kind != nkTrim: return
  let cs = p.children
  for trimmer in [cs[1], cs[2]]:
    if trimmer.kind == nkSpan: continue
    if trimmer notin made:
      let s = spanOver[S](a, trimmer, 0, -1, trimmer.expected)
      if s.isNil: continue
      made[trimmer] = s
    p.replace(trimmer, made[trimmer])

# ---------------------------------------------------------------------------
# Dispatch

proc leading(a: Analysis, p: ParserBase, acc: var seq[string]) =
  ## What the nodes that fail first in `p` expect, when nothing `p` can
  ## begin with is next: the message a miss reads.
  case p.kind
  of nkSequence:
    for c in p.children:
      a.leading(c, acc)
      if not a.nullable(c): break
  of nkChoice:
    for c in p.children: a.leading(c, acc)
  of nkOptional, nkRepeat, nkRepeatLazy, nkRepeatGreedy, nkRepeatSeparated, nkMap, nkToken,
     nkWhere, nkAhead, nkNesting, nkSettable, nkCallCC, nkTrim:
    if p.children.len > 0: a.leading(p.children[0], acc)
  of nkNotAhead, nkTest: discard   # succeed where nothing they look for is next
  else:
    if p.expected notin acc: acc.add p.expected

proc dispatches(a: Analysis, p: ParserBase) =
  ## A choice is told which alternatives can begin with each next element.
  if p.kind != nkChoice or p.isDispatched: return
  let
    alts = p.children
    firsts = alts.mapIt(a.first(it))
  if alts.len < 2 or not firsts.anyIt(it.known and not it.nullable): return
  var
    table = newSeq[seq[int]](256)
    atEnd: seq[int]
    gain = false
  for b in 0 .. 255:
    for i, f in firsts:
      if not f.known or f.nullable or byte(b) in f.es: table[b].add i
    if table[b].len < alts.len: gain = true
  for i, f in firsts:
    if not f.known or f.nullable: atEnd.add i
  if atEnd.len < alts.len: gain = true
  if not gain: return
  var leading: seq[seq[string]]
  for alt in alts:
    var names: seq[string]
    a.leading(alt, names)
    leading.add names
  p.dispatch(table, atEnd, leading)

# ---------------------------------------------------------------------------
# Caches where alternatives share a beginning

proc leader(p: ParserBase): ParserBase =
  ## The node read first when `p` is.
  result = p
  while true:
    case result.kind
    of nkSequence, nkMap, nkToken, nkWhere, nkNesting, nkSettable, nkOptional, nkTrim:
      if result.children.len == 0: return
      result = result.children[0]
    else: return

proc prefixCaches(p: ParserBase) =
  ## A node that begins two alternatives of `p` keeps its last result, so
  ## the second alternative does not read it again.
  if p.kind != nkChoice: return
  var seen: CountTable[ParserBase]
  for alt in p.children: seen.inc alt.leader
  for node, n in seen:
    if n >= 2 and node.kind notin Leaves: node.enableCache(1)

# ---------------------------------------------------------------------------

proc optimize*[S, R](root: Parser[S, R]): Parser[S, R] =
  ## `root` resolved and rewritten: the same grammar, read with its sets
  ## merged, its repetitions of sets and its trimmers as spans, its
  ## choices dispatched on the next element and shared beginnings cached.
  var r: ParserBase = root.resolve
  when dispatchable(elementOf(S)):
    var a = analyse(r)
    for pass in 0 ..< 3:
      r = r.rewrite((p: ParserBase) => setAlgebra[S](p))
      a = analyse(r)
      r = r.rewrite((p: ParserBase) => spans[S](a, p))
      a = analyse(r)
    var made: Table[ParserBase, ParserBase]
    r = r.rewrite((p: ParserBase) => trims[S](a, made, p))
    a = analyse(r)
    for p in a.nodes: prefixCaches(p)
    for p in a.nodes: dispatches(a, p)
  Parser[S, R](r)
