## What a grammar can be seen to do before it runs: for every node, which
## elements may come first (`first`), whether it may succeed consuming
## nothing (`nullable`), and which elements may follow it (`next`). Read
## off the node shapes alone, as least fixpoints over the cyclic graph, in
## byte space: the analyses mean something for sources whose element type
## is one byte wide, text and bytes, and say "unknown" wherever a node
## was written by hand. `optimize` is built on them.

import std/tables
import ./parser

const Everything* = {0'u8 .. 255'u8}

type
  First* = object
    known*: bool      ## false: anything may come first
    es*: set[byte]    ## the elements that may come first, when known
    nullable*: bool   ## may succeed consuming nothing, whatever comes next

  Next* = object
    known*: bool      ## false: anything may follow
    es*: set[byte]    ## the elements that may follow, when known
    atEnd*: bool      ## the end of the input may follow

  Analysis* = ref object
    nodes*: seq[ParserBase]   ## every node reachable from the root, the root first
    firsts: Table[ParserBase, First]
    nexts: Table[ParserBase, Next]

const
  Unknown = First(known: false, nullable: true)
  Empty = First(known: true)

func union(a, b: First): First =
  ## what may come first when either may be read
  First(known: a.known and b.known, es: a.es + b.es, nullable: a.nullable or b.nullable)

func then(a, b: First): First =
  ## what may come first when `a` is read and then `b`
  if not a.known: return Unknown
  if not a.nullable: return a
  First(known: b.known, es: a.es + b.es, nullable: b.nullable)

proc first*(a: Analysis, p: ParserBase): First =
  ## What may come first when `p` is read.
  a.firsts.getOrDefault(p, Unknown)

proc nullable*(a: Analysis, p: ParserBase): bool =
  ## Whether `p` may succeed consuming nothing.
  a.first(p).nullable

proc next*(a: Analysis, p: ParserBase): Next =
  ## What may follow `p` in a parse from the root.
  a.nexts.getOrDefault(p, Next(known: false, atEnd: true))

proc firstOf(a: Analysis, p: ParserBase): First =
  ## `p`'s first set from its shape and its children's current values.
  let cs = p.children
  template child(i: int): First = a.first(cs[i])
  case p.kind
  of nkLeaf, nkCallCC: result = Unknown
  of nkNotAhead, nkTest:
    # succeed, consuming nothing, wherever what they look for is not next
    result = First(known: true, nullable: true)
  of nkSet: result = First(known: true, es: p.elementSet)
  of nkLiteral:
    result = if p.min == 0: First(known: true, nullable: true)
             else: First(known: true, es: p.elementSet)
  of nkAny: result = First(known: true, es: Everything)
  of nkEnd, nkEpsilon: result = First(known: true, nullable: true)
  of nkFailure: result = Empty
  of nkSequence:
    result = First(known: true, nullable: true)
    for c in cs: result = result.then(a.first(c))
  of nkChoice:
    result = Empty
    for c in cs: result = result.union(a.first(c))
  of nkRepeat, nkRepeatLazy, nkRepeatGreedy, nkRepeatSeparated:
    result = child(0)
    if p.min == 0: result.nullable = true
  of nkOptional:
    result = child(0)
    result.nullable = true
  of nkMap, nkToken, nkAhead, nkWhere, nkFlatten, nkSkip, nkSettable, nkNesting:
    result = child(0)
  of nkNeg:
    let inner = child(0)
    result = if inner.known and not inner.nullable: First(known: true, es: Everything - inner.es)
             else: First(known: true, es: Everything)
  of nkTrim:
    # the trimmers may match any number of times, the body once
    let left = child(1)
    result = First(known: left.known, es: left.es, nullable: true).then(child(0))
  of nkSpan:
    result = First(known: true, es: p.elementSet, nullable: p.min == 0)
    if cs.len > 0: result = result.union(a.first(cs[0]))

func merge(a: var Next, b: Next): bool =
  ## widens `a` by `b`, answering whether it changed
  let before = a
  a.known = a.known and b.known
  a.es = a.es + b.es
  a.atEnd = a.atEnd or b.atEnd
  a != before

func following(f: First, after: Next): Next =
  ## what may follow a node read before `f`, which is followed by `after`
  result = Next(known: f.known, es: f.es)
  if f.nullable: discard result.merge(after)

func either(f: First, after: Next): Next =
  ## what may follow a node after which `f` or `after` may come
  result = Next(known: f.known, es: f.es)
  discard result.merge(after)

proc nextsFrom(a: Analysis, p: ParserBase): seq[(ParserBase, Next)] =
  ## what `p` says may follow each of its children
  let
    cs = p.children
    own = a.next(p)
  template firstOf(i: int): First = a.first(cs[i])
  case p.kind
  of nkSequence:
    for i, c in cs:
      var rest = First(known: true, nullable: true)
      for j in i + 1 ..< cs.len: rest = rest.then(a.first(cs[j]))
      result.add (c, rest.following(own))
  of nkRepeat, nkRepeatGreedy:
    result.add (cs[0], firstOf(0).either(own))
    if cs.len > 1: result.add (cs[1], own)
  of nkRepeatLazy:
    result.add (cs[0], firstOf(0).union(firstOf(1)).either(own))
    result.add (cs[1], own)
  of nkRepeatSeparated:
    result.add (cs[0], firstOf(1).either(own))
    result.add (cs[1], firstOf(0).either(own))
  of nkTrim:
    result.add (cs[0], firstOf(2).either(own))
    result.add (cs[1], firstOf(1).union(firstOf(0)).either(own))
    result.add (cs[2], firstOf(2).either(own))
  of nkSpan:
    if cs.len > 0:
      result.add (cs[0], First(known: true, es: p.elementSet).union(firstOf(0)).either(own))
  of nkChoice, nkOptional, nkMap, nkToken, nkWhere, nkFlatten, nkSkip, nkSettable, nkNesting, nkAhead:
    for c in cs: result.add (c, own)
  of nkNotAhead, nkNeg, nkCallCC, nkLeaf:
    # run to look, or by a handler: what follows them is nobody's business
    for c in cs: result.add (c, Next(known: false, atEnd: true))
  of nkSet, nkLiteral, nkAny, nkEnd, nkEpsilon, nkFailure, nkTest: discard

proc analyse*(root: ParserBase): Analysis =
  ## The analysis of every node reachable from `root`, computed once.
  result = Analysis(nodes: root.allParsers)
  for p in result.nodes: result.firsts[p] = Empty
  var changed = true
  while changed:
    changed = false
    for p in result.nodes:
      let f = result.firstOf(p)
      if f != result.firsts[p]:
        result.firsts[p] = f
        changed = true
  for p in result.nodes: result.nexts[p] = Next(known: true)
  result.nexts[root] = Next(known: true, atEnd: true)
  changed = true
  while changed:
    changed = false
    for p in result.nodes:
      for (c, n) in result.nextsFrom(p):
        if result.nexts[c].merge(n): changed = true

proc `$`*(f: First): string =
  if not f.known: return "anything"
  result = $f.es
  if f.nullable: result.add " or nothing"

proc `$`*(n: Next): string =
  if not n.known: return "anything"
  result = $n.es
  if n.atEnd: result.add " or the end"
