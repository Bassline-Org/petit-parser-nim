## A PetitParser port, after the Dart version, over any source with `len`
## and `[]`: text, bytes, or a sequence of values. A node's behaviour is a
## set of closures over its own state, so the graph protocol (`children`,
## `replace`) is untyped, `fastParseOn` knows the source and only
## `parseOn` knows the result type. Two parse paths: `parseOn` builds
## values; `fastParseOn` only recognises, answering the new position or -1,
## and allocates nothing (greedy repetition excepted: it keeps the positions
## it may back up to). One `Run` per parse keeps the furthest failure and
## every node that failed there, for "expected one of" errors, across every
## input the parse opens.
##
## Only leaves know the source. The ones here work for any source; `text`
## and `bytes` add the ones that read characters and bytes.

import std/[options, sets, hashes, strutils, macros, sugar]
export options

const MaxDepth* {.intdefine.} = 1000
  ## Nested references under way before a parse fails. A placeholder,
  ## once resolved, counts one level each time it is entered.

type
  Run* = ref object
    ## One parse: the furthest failure, and how deep the references are.
    input*: InputBase
    pos*: int
    nodes*: seq[ParserBase]
    depth*: int

  InputBase* = ref object of RootObj
    stop*: int                   ## where reading ends: the length, or a block's end
    parent*: InputBase           ## the input this one was entered from, if any
    at*: int                     ## and where
    depth*: int                  ## how many inputs this one is entered through
    run*: Run
    locateFn*: Locate            ## how a position prints in a message; nil for the default

  Locate* = proc (input: InputBase, pos: int): string {.nimcall.}

  Input*[S] = ref object of InputBase
    source*: S

  Context*[S] = object
    input*: Input[S]
    pos*: int

  ParseError* = object of CatchableError

  ParserBase* = ref object of RootObj
    name*, expected*: string
    isRef: bool
    childrenFn: () -> seq[ParserBase]
    replaceFn: (ParserBase, ParserBase) -> void
    nestFn: (ParserBase) -> ParserBase   ## a placeholder's counting stand-in

  SourceParser*[S] = ref object of ParserBase
    fastFn: (Context[S]) -> int

  Parser*[S, R] = ref object of SourceParser[S]
    parseFn: (Context[S]) -> Result[R]

  Result*[R] = object
    pos*: int
    case isSuccess*: bool
    of true: val: R
    of false:
      failed*: ParserBase
      input*: InputBase        ## set by `parse`, so `message` can explain

  Nothing* = object

  Token*[R] = object
    value*: R
    input*: InputBase
    start*, stop*: int

  Separated*[R, S] = object
    elements*: seq[R]
    separators*: seq[S]

func value*[R](r: Result[R]): R =
  if r.isSuccess:
    r.val
  else:
    raise newException(ParseError, "tried to access value of a failed result")

proc take*[R](r: var Result[R]): R =
  ## The value, moved out of the result.
  if r.isSuccess:
    move(r.val)
  else:
    raise newException(ParseError, "tried to take the value of a failed result")

# ---------------------------------------------------------------------------
# Inputs and where a position is

proc newInput*[S](source: sink S): Input[S] =
  result = Input[S](source: source, run: Run())
  result.stop = result.source.len

proc child*[S](parent: InputBase, at: int, source: sink S): Input[S] =
  ## A source entered from `parent` at `at`: a frame's body, a block. It
  ## shares the parent's run, so failures inside it count toward the
  ## furthest, and prints positions as its parent does when it reads the
  ## same kind of source.
  result = Input[S](source: source, run: parent.run, parent: parent, at: at,
                    depth: parent.depth + 1)
  result.stop = result.source.len
  if parent of Input[S]: result.locateFn = parent.locateFn

proc place*(input: InputBase, pos: int): seq[int] =
  ## The path to `pos` from the root input, outermost first.
  result = newSeq[int](input.depth + 1)
  result[^1] = pos
  var i = input
  while not i.parent.isNil:
    result[i.depth - 1] = i.at
    i = i.parent

proc locate*(input: InputBase, pos: int): string =
  if not input.locateFn.isNil: input.locateFn(input, pos)
  elif input.parent.isNil: $pos
  else: input.place(pos).join(".")

proc message*[R](r: Result[R]): string =
  if r.isSuccess:
    raise newException(ParseError, "tried to read the message of a successful result")
  var expected: seq[string]
  let nodes = if r.input.isNil: @[r.failed] else: r.input.run.nodes
  for n in nodes:
    if n.expected notin expected: expected.add n.expected
  let where = if r.input.isNil: $r.pos else: r.input.run.input.locate(r.input.run.pos)
  let what = if expected.len == 1: expected[0] else: "one of " & expected.join(", ")
  "expected " & what & " at " & where

# ---------------------------------------------------------------------------
# Core protocol

proc hash*(p: ParserBase): Hash = hash(cast[pointer](p))

template at*(ctx: Context, newPos: int): untyped =
  Context[typeof(ctx.input.source)](input: ctx.input, pos: newPos)

proc succeed*[R](value: sink R, pos: int): Result[R] {.inline.} =
  Result[R](isSuccess: true, val: value, pos: pos)

proc cmpPlace(a: InputBase, apos: int, b: InputBase, bpos: int): int =
  ## Document order of two places, each a position in an input, by their
  ## paths from the root without spelling them out. Inside a frame comes
  ## after the frame.
  if a == b or a.parent.isNil or b.parent.isNil: return cmp(apos, bpos)
  if a.depth > b.depth:
    let c = cmpPlace(a.parent, a.at, b, bpos)
    return if c != 0: c else: 1
  if b.depth > a.depth:
    let c = cmpPlace(a, apos, b.parent, b.at)
    return if c != 0: c else: -1
  let c = cmpPlace(a.parent, a.at, b.parent, b.at)
  if c != 0: c else: cmp(apos, bpos)

proc later(input: InputBase, pos: int, run: Run): bool {.inline.} =
  ## Is (`input`, `pos`) further on in document order than the run's
  ## furthest failure?
  if run.input.isNil: return true
  if input == run.input: return pos > run.pos
  cmpPlace(input, pos, run.input, run.pos) > 0

proc record(input: InputBase, node: ParserBase, pos: int) {.inline.} =
  let run = input.run
  if input.later(pos, run):
    run.input = input
    run.pos = pos
    run.nodes.setLen 0
  if input == run.input and pos == run.pos and node notin run.nodes:
    run.nodes.add node

proc fail*[S, R](node: ParserBase, ctx: Context[S]): Result[R] =
  ## A failure of `node` where `ctx` stands, remembered for the message.
  ctx.input.record(node, ctx.pos)
  Result[R](isSuccess: false, failed: node, pos: ctx.pos)

proc judged*[S, R](node: ParserBase, ctx: Context[S]): Result[R] =
  ## A failure of `node` about the whole span that ended where `ctx`
  ## stands. It outranks the guesses made inside the span, so the message
  ## names it alone when nothing failed further on.
  let
    input = InputBase(ctx.input)
    run = input.run
  if not input.later(ctx.pos, run) and (input != run.input or ctx.pos != run.pos):
    return Result[R](isSuccess: false, failed: node, pos: ctx.pos)
  run.input = input
  run.pos = ctx.pos
  run.nodes = @[node]
  Result[R](isSuccess: false, failed: node, pos: ctx.pos)

template failedAs*(T: typedesc, r: untyped): untyped =
  ## `r`'s failure as a `Result[T]`, for a handler answering another type.
  Result[T](isSuccess: false, failed: r.failed, pos: r.pos)

proc parseOn*[S, R](p: Parser[S, R], ctx: Context[S]): Result[R] {.inline.} = p.parseFn(ctx)
proc fastParseOn*[S](p: SourceParser[S], ctx: Context[S]): int {.inline.} = p.fastFn(ctx)

proc children*(p: ParserBase): seq[ParserBase] =
  if not p.childrenFn.isNil: result = p.childrenFn()

proc replace*(p, source, target: ParserBase) =
  if not p.replaceFn.isNil: p.replaceFn(source, target)

proc same(a, b: ParserBase): bool = a == b
proc kids(ps: varargs[ParserBase]): seq[ParserBase] = @ps

template swapIn(field, source, target: untyped) =
  if same(field, source):
    when typeof(field) is Parser or typeof(field) is SourceParser: field = typeof(field)(target)
    else: field = target

template over(node, child: untyped) =
  ## The graph protocol of a node with one child, captured as a var.
  node.childrenFn = () => kids(child)
  node.replaceFn = proc (source, target: ParserBase) = swapIn(child, source, target)

template overBoth(node, a, b: untyped) =
  node.childrenFn = () => kids(a, b)
  node.replaceFn = proc (source, target: ParserBase) =
    swapIn(a, source, target)
    swapIn(b, source, target)

proc recognising[S, R](p: Parser[S, R]): (Context[S]) -> int =
  ## The fast path of a node whose value decides whether it matches.
  proc (ctx: Context[S]): int =
    let r = p.parseOn(ctx)
    if r.isSuccess: r.pos else: -1

proc sourceTypeOf[S, R](p: Parser[S, R]): S = discard
proc resultTypeOf[S, R](p: Parser[S, R]): R = discard

proc named*[S, R](p: Parser[S, R], name: string): Parser[S, R] =
  p.name = name
  p.expected = name
  p

# ---------------------------------------------------------------------------
# Leaves: a recogniser and how to read what it matched

proc leaf*[S, R](expected: string, step: (Context[S]) -> int,
                 value: (Context[S], int) -> R): Parser[S, R] =
  ## A node from its two paths: `step` answers the position after a match
  ## or -1, `value` reads the match that ended at `stop`.
  let p = Parser[S, R](expected: expected, fastFn: step)
  p.parseFn = proc (ctx: Context[S]): Result[R] =
    let stop = step(ctx)
    if stop < 0: fail[S, R](p, ctx) else: succeed(value(ctx, stop), stop)
  p

proc item*[S](pred: (typeof(default(S)[0])) -> bool,
              expected: string): Parser[S, typeof(default(S)[0])] =
  ## One element of the source where `pred` holds.
  leaf[S, typeof(default(S)[0])](expected,
    (ctx: Context[S]) => (if ctx.pos < ctx.input.stop and pred(ctx.input.source[ctx.pos]): ctx.pos + 1
                          else: -1),
    (ctx: Context[S], stop: int) => ctx.input.source[ctx.pos])

proc oneOf*[S, E](es: set[E], expected: string): Parser[S, E] =
  ## One element of the source from a set, for sources of ordinals.
  leaf[S, E](expected,
    (ctx: Context[S]) => (if ctx.pos < ctx.input.stop and ctx.input.source[ctx.pos] in es: ctx.pos + 1
                          else: -1),
    (ctx: Context[S], stop: int) => ctx.input.source[ctx.pos])

proc any*[S](): Parser[S, typeof(default(S)[0])] =
  ## Any one element.
  leaf[S, typeof(default(S)[0])]("any element",
    (ctx: Context[S]) => (if ctx.pos < ctx.input.stop: ctx.pos + 1 else: -1),
    (ctx: Context[S], stop: int) => ctx.input.source[ctx.pos])

proc endOfInput*[S](): Parser[S, Nothing] =
  leaf[S, Nothing]("end of input",
    (ctx: Context[S]) => (if ctx.pos >= ctx.input.stop: ctx.pos else: -1),
    (ctx: Context[S], stop: int) => Nothing())

proc epsilon*[S](): Parser[S, Nothing] =
  ## Matches nothing, always.
  leaf[S, Nothing]("nothing", (ctx: Context[S]) => ctx.pos, (ctx: Context[S], stop: int) => Nothing())

proc epsilon*[S, T](value: T): Parser[S, T] =
  leaf[S, T]("nothing", (ctx: Context[S]) => ctx.pos, (ctx: Context[S], stop: int) => value)

proc failure*[S, R](expected: string): Parser[S, R] =
  ## Fails, always, expecting `expected`.
  leaf[S, R](expected, (ctx: Context[S]) => -1, (ctx: Context[S], stop: int) => default(R))

proc position*[S](): Parser[S, int] =
  ## The position reached, consuming nothing.
  leaf[S, int]("position", (ctx: Context[S]) => ctx.pos, (ctx: Context[S], stop: int) => ctx.pos)

# ---------------------------------------------------------------------------
# Sequence: a tuple of parsers answers the tuple of their values

macro sequence*(parsers: tuple): untyped =
  ## `sequence((a, b, c))` is `a` then `b` then `c`, answering `(A, B, C)`.
  let
    given = genSym(nskLet, "given")
    ps = genSym(nskVar, "parsers")
    node = genSym(nskLet, "node")
    S = genSym(nskType, "S")
    R = genSym(nskType, "R")
    (pos, ctx) = (ident"pos", ident"ctx")
    (source, target) = (ident"source", ident"target")
    first = nnkBracketExpr.newTree(given, newLit 0)
  var
    slots = nnkTupleConstr.newTree()
    takes = newStmtList()
    types = nnkTupleConstr.newTree()
    values = nnkTupleConstr.newTree()
    parse = newStmtList()
    fast = newStmtList()
    kids = newCall(bindSym"kids")
    names = nnkBracket.newTree()
    swaps = newStmtList()
  for i in 0 ..< parsers.getType.len - 1:
    let
      g = nnkBracketExpr.newTree(given, newLit i)
      q = nnkBracketExpr.newTree(ps, newLit i)
      r = ident("r" & $i)
      t = newCall(bindSym"resultTypeOf", g)
    slots.add nnkBracketExpr.newTree(bindSym"Parser", S, newCall(bindSym"typeof", t))
    takes.add quote do: `q` = `g`
    types.add t
    values.add newCall(ident"move", newDotExpr(r, ident"val"))
    parse.add quote do:
      var `r` = `q`.parseOn(`ctx`.at(`pos`))
      if not `r`.isSuccess: return failedAs(`R`, `r`)
      `pos` = `r`.pos
    fast.add quote do:
      `pos` = `q`.fastParseOn(`ctx`.at(`pos`))
      if `pos` < 0: return -1
    kids.add q
    names.add newDotExpr(q, ident"expected")
    swaps.add quote do: swapIn(`q`, `source`, `target`)
  quote do:
    let `given` = `parsers`
    type `S` = typeof(sourceTypeOf(`first`))
    var `ps`: `slots`
    `takes`
    type `R` = typeof(`types`)
    let `node` = Parser[`S`, `R`](expected: `names`.join(" then "))
    `node`.parseFn = proc (`ctx`: Context[`S`]): Result[`R`] =
      var `pos` = `ctx`.pos
      `parse`
      succeed(`values`, `pos`)
    `node`.fastFn = proc (`ctx`: Context[`S`]): int =
      var `pos` = `ctx`.pos
      `fast`
      `pos`
    `node`.childrenFn = () => `kids`
    `node`.replaceFn = proc (`source`, `target`: ParserBase) = `swaps`
    `node`

proc `&`*[S, A, B](a: Parser[S, A], b: Parser[S, B]): Parser[S, (A, B)] = sequence((a, b))

# ---------------------------------------------------------------------------
# Ordered choice: the first alternative that succeeds

type ChoiceParser*[S, R] = ref object of Parser[S, R]
  alts: seq[Parser[S, R]]

proc alternatives(names: seq[string]): string =
  case names.len
  of 0: "no alternative"
  of 1: names[0]
  else: "one of " & names.join(", ")

proc choice*[S, R](alts: varargs[Parser[S, R]]): Parser[S, R] =
  var names: seq[string]
  for a in alts:
    if a.expected notin names: names.add a.expected
  let c = ChoiceParser[S, R](alts: @alts, expected: names.alternatives)
  c.parseFn = proc (ctx: Context[S]): Result[R] =
    for alt in c.alts:
      result = alt.parseOn(ctx)
      if result.isSuccess: return
    if c.alts.len == 0: result = fail[S, R](c, ctx)
  c.fastFn = proc (ctx: Context[S]): int =
    for alt in c.alts:
      let pos = alt.fastParseOn(ctx)
      if pos >= 0: return pos
    -1
  c.childrenFn = proc (): seq[ParserBase] =
    for alt in c.alts: result.add alt
  c.replaceFn = proc (source, target: ParserBase) =
    for alt in c.alts.mitems: swapIn(alt, source, target)
  c

proc `/`*[S, R](a, b: Parser[S, R]): Parser[S, R] =
  ## `a / b / c` is one flat choice; a named choice stays a unit.
  var alts: seq[Parser[S, R]]
  for x in [a, b]:
    if x of ChoiceParser[S, R] and x.name.len == 0: alts.add ChoiceParser[S, R](x).alts
    else: alts.add x
  choice(alts)

# ---------------------------------------------------------------------------
# Repetition. `max` < 0 is unbounded. An item that consumes nothing ends
# the run once `min` is met, so a nullable item cannot loop.

proc repeat*[S, R](item: Parser[S, R], min: int, max = -1): Parser[S, seq[R]] =
  ## Possessive: as many items as match, never giving input back.
  assert max < 0 or min <= max
  var item = item
  let p = Parser[S, seq[R]](expected: item.expected)
  p.parseFn = proc (ctx: Context[S]): Result[seq[R]] =
    var
      values: seq[R]
      pos = ctx.pos
    while max < 0 or values.len < max:
      var r = item.parseOn(ctx.at(pos))
      if not r.isSuccess:
        if values.len < min: return failedAs(seq[R], r)
        break
      if r.pos == pos and values.len >= min: break
      values.add move(r.val)
      pos = r.pos
    succeed(values, pos)
  p.fastFn = proc (ctx: Context[S]): int =
    var
      count = 0
      pos = ctx.pos
    while max < 0 or count < max:
      let next = item.fastParseOn(ctx.at(pos))
      if next < 0:
        if count < min: return -1
        break
      if next == pos and count >= min: break
      pos = next
      inc count
    pos
  p.over(item)
  p

proc star*[S, R](item: Parser[S, R]): Parser[S, seq[R]] = item.repeat(0)
proc plus*[S, R](item: Parser[S, R]): Parser[S, seq[R]] = item.repeat(1)
proc times*[S, R](item: Parser[S, R], n: int): Parser[S, seq[R]] = item.repeat(n, n)

proc repeatLazy*[S, R](item: Parser[S, R], limit: SourceParser[S], min: int,
                       max = -1): Parser[S, seq[R]] =
  ## Items until `limit` matches, as few as possible; `limit` is not consumed.
  assert max < 0 or min <= max
  var (item, limit) = (item, limit)
  let p = Parser[S, seq[R]](expected: item.expected)
  p.parseFn = proc (ctx: Context[S]): Result[seq[R]] =
    var
      values: seq[R]
      pos = ctx.pos
    while values.len < min or limit.fastParseOn(ctx.at(pos)) < 0:
      if values.len >= min and max >= 0 and values.len >= max:
        return fail[S, seq[R]](limit, ctx.at(pos))
      var r = item.parseOn(ctx.at(pos))
      if not r.isSuccess: return failedAs(seq[R], r)
      if r.pos == pos and values.len >= min: return fail[S, seq[R]](limit, ctx.at(pos))
      values.add move(r.val)
      pos = r.pos
    succeed(values, pos)
  p.fastFn = proc (ctx: Context[S]): int =
    var
      count = 0
      pos = ctx.pos
    while count < min or limit.fastParseOn(ctx.at(pos)) < 0:
      if count >= min and max >= 0 and count >= max: return -1
      let next = item.fastParseOn(ctx.at(pos))
      if next < 0 or (next == pos and count >= min): return -1
      pos = next
      inc count
    pos
  p.overBoth(item, limit)
  p

proc starLazy*[S, R](item: Parser[S, R], limit: SourceParser[S]): Parser[S, seq[R]] =
  item.repeatLazy(limit, 0)
proc plusLazy*[S, R](item: Parser[S, R], limit: SourceParser[S]): Parser[S, seq[R]] =
  item.repeatLazy(limit, 1)

proc repeatGreedy*[S, R](item: Parser[S, R], limit: SourceParser[S], min: int,
                         max = -1): Parser[S, seq[R]] =
  ## As many items as match, then back up until `limit` matches after them.
  assert max < 0 or min <= max
  var (item, limit) = (item, limit)
  let p = Parser[S, seq[R]](expected: item.expected)
  p.parseFn = proc (ctx: Context[S]): Result[seq[R]] =
    var
      values: seq[R]
      pos = ctx.pos
    while values.len < min:
      var r = item.parseOn(ctx.at(pos))
      if not r.isSuccess: return failedAs(seq[R], r)
      values.add move(r.val)
      pos = r.pos
    var stops = @[pos]
    while max < 0 or values.len < max:
      var r = item.parseOn(ctx.at(pos))
      if not r.isSuccess or r.pos == pos: break
      values.add move(r.val)
      pos = r.pos
      stops.add pos
    while limit.fastParseOn(ctx.at(stops[^1])) < 0:
      if stops.len == 1: return fail[S, seq[R]](limit, ctx.at(stops[0]))
      discard stops.pop
      discard values.pop
    succeed(values, stops[^1])
  p.fastFn = proc (ctx: Context[S]): int =
    var
      count = 0
      pos = ctx.pos
    while count < min:
      pos = item.fastParseOn(ctx.at(pos))
      if pos < 0: return -1
      inc count
    var stops = @[pos]
    while max < 0 or count < max:
      let next = item.fastParseOn(ctx.at(pos))
      if next < 0 or next == pos: break
      pos = next
      inc count
      stops.add pos
    while limit.fastParseOn(ctx.at(stops[^1])) < 0:
      if stops.len == 1: return -1
      discard stops.pop
    stops[^1]
  p.overBoth(item, limit)
  p

proc starGreedy*[S, R](item: Parser[S, R], limit: SourceParser[S]): Parser[S, seq[R]] =
  item.repeatGreedy(limit, 0)
proc plusGreedy*[S, R](item: Parser[S, R], limit: SourceParser[S]): Parser[S, seq[R]] =
  item.repeatGreedy(limit, 1)

proc repeatSeparated*[S, R, T](item: Parser[S, R], sep: Parser[S, T], min: int,
                               max = -1): Parser[S, Separated[R, T]] =
  ## Items with `sep` between them; a trailing `sep` is left unconsumed.
  assert max < 0 or min <= max
  var (item, sep) = (item, sep)
  let p = Parser[S, Separated[R, T]](expected: item.expected)
  p.parseFn = proc (ctx: Context[S]): Result[Separated[R, T]] =
    var
      list: Separated[R, T]
      pos = ctx.pos
    while max < 0 or list.elements.len < max:
      var
        at = pos
        s: Result[T]
      if list.elements.len > 0:
        s = sep.parseOn(ctx.at(pos))
        if not s.isSuccess:
          if list.elements.len < min: return failedAs(Separated[R, T], s)
          break
        at = s.pos
      var r = item.parseOn(ctx.at(at))
      if not r.isSuccess:
        if list.elements.len < min: return failedAs(Separated[R, T], r)
        break
      if r.pos == pos and list.elements.len >= min: break
      if list.elements.len > 0: list.separators.add move(s.val)
      list.elements.add move(r.val)
      pos = r.pos
    succeed(list, pos)
  p.fastFn = proc (ctx: Context[S]): int =
    var
      count = 0
      pos = ctx.pos
    while max < 0 or count < max:
      var at = pos
      if count > 0:
        at = sep.fastParseOn(ctx.at(pos))
        if at < 0:
          if count < min: return -1
          break
      let next = item.fastParseOn(ctx.at(at))
      if next < 0:
        if count < min: return -1
        break
      if next == pos and count >= min: break
      pos = next
      inc count
    pos
  p.overBoth(item, sep)
  p

proc starSeparated*[S, R, T](item: Parser[S, R], sep: Parser[S, T]): Parser[S, Separated[R, T]] =
  item.repeatSeparated(sep, 0)
proc plusSeparated*[S, R, T](item: Parser[S, R], sep: Parser[S, T]): Parser[S, Separated[R, T]] =
  item.repeatSeparated(sep, 1)
proc timesSeparated*[S, R, T](item: Parser[S, R], sep: Parser[S, T],
                              n: int): Parser[S, Separated[R, T]] =
  item.repeatSeparated(sep, n, n)

proc foldLeft*[R, T](list: Separated[R, T], fn: (R, T, R) -> R): R =
  ## `((e0 sep0 e1) sep1 e2) …`; needs an element.
  result = list.elements[0]
  for i, sep in list.separators: result = fn(result, sep, list.elements[i + 1])

proc foldRight*[R, T](list: Separated[R, T], fn: (R, T, R) -> R): R =
  ## `e0 sep0 (e1 sep1 (e2 …))`; needs an element.
  result = list.elements[^1]
  for i in countdown(list.separators.high, 0):
    result = fn(list.elements[i], list.separators[i], result)

# ---------------------------------------------------------------------------
# One delegate, its result read anew

proc keepStop(stop, start: int): int = stop
  ## The default fast path of `through`: a named proc, since the JS
  ## backend emits a lambda default of a generic inside its first caller.

proc through[S, D, R](p: Parser[S, D], read: (var Result[D], Context[S]) -> Result[R],
                      fast: (int, int) -> int = keepStop): Parser[S, R] =
  ## Callers instantiate it explicitly: Nim 2.2.12 does not infer `D`
  ## through the `var` parameter.
  var p = p
  let t = Parser[S, R](expected: p.expected)
  t.parseFn = proc (ctx: Context[S]): Result[R] =
    var r = p.parseOn(ctx)
    read(r, ctx)
  t.fastFn = (ctx: Context[S]) => fast(p.fastParseOn(ctx), ctx.pos)
  t.over(p)
  t

proc optional*[S, R](p: Parser[S, R]): Parser[S, Option[R]] =
  through[S, R, Option[R]](p, (r: var Result[R], ctx: Context[S]) -> Result[Option[R]] =>
    (if r.isSuccess: succeed(some(move(r.val)), r.pos) else: succeed(none(R), ctx.pos)),
    (stop, start: int) => max(stop, start))

proc optional*[S, R](p: Parser[S, R], value: R): Parser[S, R] =
  ## `p`, or `value` where `p` does not match.
  through[S, R, R](p, (r: var Result[R], ctx: Context[S]) -> Result[R] =>
    (if r.isSuccess: move(r) else: succeed(value, ctx.pos)),
    (stop, start: int) => max(stop, start))

proc map*[S, A, B](p: Parser[S, A], fn: (A) -> B): Parser[S, B] =
  ## `fn` is taken as pure: the fast path skips it. It is handed a copy of
  ## the value; a lambda with a `sink` parameter is handed the value itself.
  through[S, A, B](p, (r: var Result[A], ctx: Context[S]) -> Result[B] =>
    (if r.isSuccess: succeed(fn(r.val), r.pos) else: failedAs(B, r)))

proc map*[S, A, B](p: Parser[S, A], fn: (sink A) -> B): Parser[S, B] =
  through[S, A, B](p, (r: var Result[A], ctx: Context[S]) -> Result[B] =>
    (if r.isSuccess: succeed(fn(move(r.val)), r.pos) else: failedAs(B, r)))

proc pick*[S, T](p: Parser[S, T], i: static int): Parser[S, typeof(default(T)[i])] =
  ## One value of a tuple, moved out. `map(t => t[i])` copies it.
  through[S, T, typeof(default(T)[i])](p,
    (r: var Result[T], ctx: Context[S]) -> Result[typeof(default(T)[i])] =>
      (if r.isSuccess: succeed(move(r.val[i]), r.pos)
       else: failedAs(typeof(default(T)[i]), r)))

proc elements*[S, R, T](p: Parser[S, Separated[R, T]]): Parser[S, seq[R]] =
  ## The elements of a separated list, moved out.
  through[S, Separated[R, T], seq[R]](p,
    (r: var Result[Separated[R, T]], ctx: Context[S]) -> Result[seq[R]] =>
      (if r.isSuccess: succeed(move(r.val.elements), r.pos) else: failedAs(seq[R], r)))

proc delimited*[S, A, B, C](open: Parser[S, A], close: Parser[S, C],
                            inside: Parser[S, B]): Parser[S, B] =
  ## `inside` between `open` and `close`, keeping only its value.
  sequence((open, inside, close)).pick(1)

proc `==>`*[S, A, B](p: Parser[S, A], fn: (A) -> B): Parser[S, B] = p.map(fn)

proc token*[S, R](p: Parser[S, R]): Parser[S, Token[R]] =
  through[S, R, Token[R]](p, proc (r: var Result[R], ctx: Context[S]): Result[Token[R]] =
    if r.isSuccess:
      succeed(Token[R](value: move(r.val), input: ctx.input, start: ctx.pos, stop: r.pos), r.pos)
    else: failedAs(Token[R], r))

proc ahead*[S, R](p: Parser[S, R]): Parser[S, R] =
  ## Positive lookahead: `p`'s value, no input consumed.
  through[S, R, R](p, (r: var Result[R], ctx: Context[S]) -> Result[R] =>
    (if r.isSuccess: succeed(move(r.val), ctx.pos) else: move(r)),
    (stop, start: int) => (if stop < 0: -1 else: start))

proc where*[S, R](p: Parser[S, R], pred: (R) -> bool, expected: string): Parser[S, R] =
  ## `p`'s value where `pred` holds; otherwise a failure where `p` ended,
  ## the furthest point the judged span reached.
  var p = p
  let w = Parser[S, R](expected: expected)
  w.parseFn = proc (ctx: Context[S]): Result[R] =
    let r = p.parseOn(ctx)
    if r.isSuccess and not pred(r.val): judged[S, R](w, ctx.at(r.pos)) else: r
  w.fastFn = w.recognising
  w.over(p)
  w

proc callCC*[S, D, R](p: Parser[S, D],
                      handler: (Parser[S, D], Context[S]) -> Result[R]): Parser[S, R] =
  ## `handler` is handed `p` and decides whether, how often and with what
  ## to run it: tracing, profiling, memoisation.
  var p = p
  let c = Parser[S, R](expected: p.expected)
  c.parseFn = (ctx: Context[S]) => handler(p, ctx)
  c.fastFn = c.recognising
  c.over(p)
  c

# flatten, skip and negative lookahead only recognise their delegate

proc flatten*[S](p: SourceParser[S], expected = ""): Parser[S, S] =
  ## The stretch of source `p` consumed; `p` builds nothing and its
  ## failures are reported as this node's.
  var p = p
  result = leaf[S, S](if expected.len > 0: expected else: p.expected,
                      (ctx: Context[S]) => p.fastParseOn(ctx),
                      (ctx: Context[S], stop: int) => ctx.input.source[ctx.pos ..< stop])
  result.over(p)

proc skip*[S](p: SourceParser[S], expected = ""): Parser[S, Nothing] =
  var p = p
  result = leaf[S, Nothing](if expected.len > 0: expected else: p.expected,
                            (ctx: Context[S]) => p.fastParseOn(ctx),
                            (ctx: Context[S], stop: int) => Nothing())
  result.over(p)

proc notAhead*[S](p: SourceParser[S], expected = ""): Parser[S, Nothing] =
  var p = p
  result = leaf[S, Nothing](if expected.len > 0: expected else: "not " & p.expected,
                            (ctx: Context[S]) => (if p.fastParseOn(ctx) < 0: ctx.pos else: -1),
                            (ctx: Context[S], stop: int) => Nothing())
  result.over(p)

proc neg*[S](p: SourceParser[S]): Parser[S, typeof(default(S)[0])] =
  ## Anything but `p`: one element where `p` does not match.
  var p = p
  result = leaf[S, typeof(default(S)[0])]("not " & p.expected,
    (ctx: Context[S]) => (if ctx.pos < ctx.input.stop and p.fastParseOn(ctx) < 0: ctx.pos + 1
                          else: -1),
    (ctx: Context[S], stop: int) => ctx.input.source[ctx.pos])
  result.over(p)

# ---------------------------------------------------------------------------
# Trimming: `left` and `right` are skipped as often as they match

proc skipAll[S](trimmer: SourceParser[S], ctx: Context[S]): int =
  result = ctx.pos
  while true:
    let next = trimmer.fastParseOn(ctx.at(result))
    if next < 0 or next == result: return
    result = next

proc trim*[S, R](p: Parser[S, R], left, right: SourceParser[S]): Parser[S, R] =
  var (p, left, right) = (p, left, right)
  let t = Parser[S, R](expected: p.expected)
  t.parseFn = proc (ctx: Context[S]): Result[R] =
    var r = p.parseOn(ctx.at(left.skipAll(ctx)))
    if r.isSuccess: succeed(move(r.val), right.skipAll(ctx.at(r.pos))) else: move(r)
  t.fastFn = proc (ctx: Context[S]): int =
    let pos = p.fastParseOn(ctx.at(left.skipAll(ctx)))
    if pos < 0: -1 else: right.skipAll(ctx.at(pos))
  t.childrenFn = () => kids(p, left, right)
  t.replaceFn = proc (source, target: ParserBase) =
    swapIn(p, source, target)
    swapIn(left, source, target)
    swapIn(right, source, target)
  t

proc trim*[S, R](p: Parser[S, R], ws: SourceParser[S]): Parser[S, R] = p.trim(ws, ws)

# ---------------------------------------------------------------------------
# Forward references: `undefined` then `define`; `resolve` removes them

type SettableParser*[S, R] = ref object of Parser[S, R]
  target: Parser[S, R]

proc nesting[S, R](p: Parser[S, R]): Parser[S, R] =
  ## `p` as one level of nesting, failing past `MaxDepth`.
  var p = p
  let
    n = Parser[S, R](expected: p.expected)
    deep = ParserBase(expected: "shallower nesting")
  n.parseFn = proc (ctx: Context[S]): Result[R] =
    if ctx.input.run.depth >= MaxDepth: return fail[S, R](deep, ctx)
    inc ctx.input.run.depth
    result = p.parseOn(ctx)
    dec ctx.input.run.depth
  n.fastFn = proc (ctx: Context[S]): int =
    if ctx.input.run.depth >= MaxDepth: return -1
    inc ctx.input.run.depth
    result = p.fastParseOn(ctx)
    dec ctx.input.run.depth
  n.over(p)
  n

proc undefined*[S, R](name = ""): SettableParser[S, R] =
  ## A placeholder that fails until it is `define`d.
  let s = SettableParser[S, R](name: name, expected: name, isRef: true)
  var standIn: Parser[S, R]
  s.target = failure[S, R](if name.len > 0: name else: "undefined parser")
  s.parseFn = (ctx: Context[S]) => s.target.parseOn(ctx)
  s.fastFn = (ctx: Context[S]) => s.target.fastParseOn(ctx)
  s.over(s.target)
  s.nestFn = proc (target: ParserBase): ParserBase =
    if standIn.isNil: standIn = nesting(Parser[S, R](target))
    standIn
  s

proc define*[S, R](p: SettableParser[S, R], target: Parser[S, R]) = p.target = target

proc containsOrIncl(seen: var seq[ParserBase], p: ParserBase): bool =
  result = p in seen
  if not result: seen.add p

template withSeen(body: untyped) =
  ## `body` with a `seen` set of nodes. The VM cannot hash a ref, so
  ## there it is a seq.
  when nimvm:
    block:
      var seen {.inject.}: seq[ParserBase]
      body
  else:
    block:
      var seen {.inject.}: HashSet[ParserBase]
      body

proc allParsers*(root: ParserBase): seq[ParserBase] =
  ## Every node reachable from `root`, once each.
  withSeen:
    var todo = @[root]
    while todo.len > 0:
      let p = todo.pop
      if not seen.containsOrIncl p:
        result.add p
        todo.add p.children

proc deref(p: ParserBase): ParserBase =
  result = p
  withSeen:
    while result.isRef:
      if seen.containsOrIncl result:
        raise newException(ValueError, "reference cycle with no parser: " & p.name)
      result = result.children[0]

proc resolved(p: ParserBase): ParserBase =
  let t = p.deref
  if t == p: p else: p.nestFn(t)

proc resolve*[S, R](root: Parser[S, R]): Parser[S, R] =
  ## Rewire every parent past its forward references, leaving a node that
  ## counts the nesting where each placeholder was. Cycles stay.
  for p in root.allParsers:
    for c in p.children:
      let r = c.resolved
      if r != c: p.replace(c, r)
  Parser[S, R](root.resolved)

# ---------------------------------------------------------------------------
# Entry points

proc parse*[S, R](p: Parser[S, R], source: sink S): Result[R] =
  ## A failure reports the furthest position any node reached. A source
  ## module may give `newInput` for its source, to say how positions print.
  mixin newInput
  let input = newInput(source)
  result = p.parseOn(Context[S](input: input))
  if not result.isSuccess:
    if input.run.nodes.len > 0:
      result.failed = input.run.nodes[^1]
      result.pos = input.run.pos
    result.input = input

proc accepts*[S](p: SourceParser[S], source: sink S): bool =
  mixin newInput
  p.fastParseOn(Context[S](input: newInput(source))) >= 0

proc complete*[S, R](p: Parser[S, R]): Parser[S, R] = (p & endOfInput[S]()).pick(0)
