## A PetitParser port, after the Dart version. A node's behaviour is a set
## of closures over its own state, so the graph protocol (`children`,
## `replace`, `fastParseOn`) is untyped and only `parseOn` knows the result
## type. Two parse paths: `parseOn` builds values; `fastParseOn` only
## recognises, answering the new position or -1, and allocates nothing
## (greedy repetition excepted: it keeps the positions it may back up to).
## One `Input` per parse keeps the furthest failure and every node that
## failed there, for "expected one of" errors.

import std/[options, sets, hashes, strutils, setutils, macros, sugar]
export options

const MaxDepth* {.intdefine.} = 1000
  ## Nested references under way before a parse fails. A placeholder,
  ## once resolved, counts one level each time it is entered.

type
  Input* = ref object
    text*: string
    stop*: int
    depth*: int
    furthestPos*: int
    furthestNodes*: seq[ParserBase]

  Context* = object
    input*: Input
    pos*: int

  ParseError* = object of CatchableError

  ParserBase* = ref object of RootObj
    name*, expected*: string
    isRef: bool
    childrenFn: () -> seq[ParserBase]
    replaceFn: (ParserBase, ParserBase) -> void
    fastFn: (Context) -> int
    nestFn: (ParserBase) -> ParserBase   ## a placeholder's counting stand-in

  Parser*[R] = ref object of ParserBase
    parseFn: (Context) -> Result[R]

  Result*[R] = object
    pos*: int
    case isSuccess*: bool
    of true: val: R
    of false:
      failed*: ParserBase
      input*: Input          ## set by `parse`, so `message` can explain

  Nothing* = object

  Token*[R] = object
    value*: R
    input*: Input
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

proc lineCol*(text: string, pos: int): (int, int) =
  let before = text[0 ..< min(pos, text.len)]
  (before.count('\n') + 1, pos - before.rfind('\n'))

proc message*[R](r: Result[R]): string =
  if r.isSuccess:
    raise newException(ParseError, "tried to read the message of a successful result")
  var expected: seq[string]
  for n in (if r.input.isNil: @[r.failed] else: r.input.furthestNodes):
    if n.expected notin expected: expected.add n.expected
  var where = $r.pos
  if not r.input.isNil:
    let (line, col) = lineCol(r.input.text, r.pos)
    where = $line & ":" & $col
  let what = if expected.len == 1: expected[0] else: "one of " & expected.join(", ")
  "expected " & what & " at " & where

# ---------------------------------------------------------------------------
# Core protocol

proc hash*(p: ParserBase): Hash = hash(cast[pointer](p))

proc newInput*(text: sink string): Input =
  result = Input(text: text)
  result.stop = result.text.len

template at*(ctx: Context, newPos: int): Context =
  Context(input: ctx.input, pos: newPos)

proc succeed*[R](value: sink R, pos: int): Result[R] {.inline.} =
  Result[R](isSuccess: true, val: value, pos: pos)

proc record(input: Input, node: ParserBase, pos: int) =
  if pos > input.furthestPos:
    input.furthestPos = pos
    input.furthestNodes.setLen 0
  if pos == input.furthestPos and node notin input.furthestNodes:
    input.furthestNodes.add node

proc fail*[R](node: ParserBase, ctx: Context): Result[R] =
  ## A failure of `node` where `ctx` stands, remembered for the message.
  ctx.input.record(node, ctx.pos)
  Result[R](isSuccess: false, failed: node, pos: ctx.pos)

template failedAs*(T: typedesc, r: untyped): untyped =
  ## `r`'s failure as a `Result[T]`, for a handler answering another type.
  Result[T](isSuccess: false, failed: r.failed, pos: r.pos)

proc parseOn*[R](p: Parser[R], ctx: Context): Result[R] {.inline.} = p.parseFn(ctx)
proc fastParseOn*(p: ParserBase, ctx: Context): int {.inline.} = p.fastFn(ctx)

proc children*(p: ParserBase): seq[ParserBase] =
  if not p.childrenFn.isNil: result = p.childrenFn()

proc replace*(p, source, target: ParserBase) =
  if not p.replaceFn.isNil: p.replaceFn(source, target)

proc same(a, b: ParserBase): bool = a == b
proc kids(ps: varargs[ParserBase]): seq[ParserBase] = @ps

template swapIn(field, source, target: untyped) =
  if same(field, source):
    when typeof(field) is Parser: field = typeof(field)(target)
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

proc recognising[R](p: Parser[R]): (Context) -> int =
  ## The fast path of a node whose value decides whether it matches.
  proc (ctx: Context): int =
    let r = p.parseOn(ctx)
    if r.isSuccess: r.pos else: -1

proc resultTypeOf[R](p: Parser[R]): R = discard

proc named*[R](p: Parser[R], name: string): Parser[R] =
  p.name = name
  p.expected = name
  p

# ---------------------------------------------------------------------------
# Leaves: a recogniser and how to read what it matched

proc leaf[R](expected: string, step: (Context) -> int, value: (Context, int) -> R): Parser[R] =
  let p = Parser[R](expected: expected, fastFn: step)
  p.parseFn = proc (ctx: Context): Result[R] =
    let stop = step(ctx)
    if stop < 0: fail[R](p, ctx) else: succeed(value(ctx, stop), stop)
  p

proc one[E: char | byte](es: set[E], expected: string): Parser[E] =
  leaf[E](expected,
    (ctx: Context) => (if ctx.pos < ctx.input.stop and
                          E(ctx.input.text[ctx.pos]) in es: ctx.pos + 1 else: -1),
    (ctx: Context, stop: int) => E(ctx.input.text[ctx.pos]))

proc chars*(cs: set[char], expected: string): Parser[char] = one(cs, expected)
proc chars*(cs, expected: string): Parser[char] = one(cs.toSet, expected)
proc noneOf*(cs, expected: string): Parser[char] = one(cs.toSet.complement, expected)
proc bytes*(bs: set[byte], expected: string): Parser[byte] = one(bs, expected)
proc ch*(c: char): Parser[char] = one({c}, "'" & c & "'")
proc ch*(b: byte): Parser[byte] = one({b}, "0x" & b.toHex)
proc between*(lo, hi: char): Parser[char] = one({lo .. hi}, "'" & lo & "'..'" & hi & "'")

proc pattern*(spec: string): Parser[char] =
  ## A character class: "a-zA-Z_", or negated "^0-9".
  let negated = spec.startsWith '^'
  var
    cs: set[char]
    i = negated.ord
  while i < spec.len:
    if i + 2 < spec.len and spec[i + 1] == '-':
      cs.incl {spec[i] .. spec[i + 2]}
      i += 3
    else:
      cs.incl spec[i]
      inc i
  chars(if negated: cs.complement else: cs, "[" & spec & "]")

proc anyChar*(): Parser[char] = chars(fullSet(char), "any character")
proc anyByte*(): Parser[byte] = bytes(fullSet(byte), "any byte")
proc digit*(): Parser[char] = chars(Digits, "digit")
proc letter*(): Parser[char] = chars(Letters, "letter")
proc lowercase*(): Parser[char] = chars({'a' .. 'z'}, "lowercase letter")
proc uppercase*(): Parser[char] = chars({'A' .. 'Z'}, "uppercase letter")
proc word*(): Parser[char] = chars(Letters + Digits + {'_'}, "letter or digit")
proc whitespace*(): Parser[char] = chars(Whitespace, "whitespace")

proc toText(data: openArray[byte]): string =
  result = newString(data.len)
  for i, b in data: result[i] = b.char

proc continuesWith(ctx: Context, lit: string): bool =
  ctx.pos + lit.len <= ctx.input.stop and ctx.input.text.continuesWith(lit, ctx.pos)

proc str*(lit: string): Parser[string] =
  leaf[string]("'" & lit & "'",
    (ctx: Context) => (if ctx.continuesWith(lit): ctx.pos + lit.len else: -1),
    (ctx: Context, stop: int) => lit)

proc str*(lit: openArray[byte]): Parser[string] = str(lit.toText)

proc continuesWithIgnoreCase(ctx: Context, lit: string): bool =
  if ctx.pos + lit.len > ctx.input.stop: return false
  for i, c in lit:
    if ctx.input.text[ctx.pos + i].toLowerAscii != c.toLowerAscii: return false
  true

proc strIgnoreCase*(lit: string): Parser[string] =
  ## `lit` in any ASCII case; the value is the input as written.
  leaf[string]("'" & lit & "'",
    (ctx: Context) => (if ctx.continuesWithIgnoreCase(lit): ctx.pos + lit.len else: -1),
    (ctx: Context, stop: int) => ctx.input.text[ctx.pos ..< stop])

proc newline*(): Parser[string] =
  leaf[string]("newline",
    proc (ctx: Context): int =
      if ctx.continuesWith("\r\n"): ctx.pos + 2
      elif ctx.pos < ctx.input.stop and ctx.input.text[ctx.pos] in {'\n', '\r'}: ctx.pos + 1
      else: -1,
    (ctx: Context, stop: int) => ctx.input.text[ctx.pos ..< stop])

proc endOfInput*(): Parser[Nothing] =
  leaf[Nothing]("end of input",
    (ctx: Context) => (if ctx.pos >= ctx.input.stop: ctx.pos else: -1),
    (ctx: Context, stop: int) => Nothing())

proc epsilon*(): Parser[Nothing] =
  ## Matches nothing, always.
  leaf[Nothing]("nothing", (ctx: Context) => ctx.pos, (ctx: Context, stop: int) => Nothing())

proc epsilon*[T](value: T): Parser[T] =
  leaf[T]("nothing", (ctx: Context) => ctx.pos, (ctx: Context, stop: int) => value)

proc failure*[R](expected: string): Parser[R] =
  ## Fails, always, expecting `expected`.
  leaf[R](expected, (ctx: Context) => -1, (ctx: Context, stop: int) => default(R))

proc position*(): Parser[int] =
  ## The position reached, consuming nothing.
  leaf[int]("position", (ctx: Context) => ctx.pos, (ctx: Context, stop: int) => ctx.pos)

# ---------------------------------------------------------------------------
# Sequence: a tuple of parsers answers the tuple of their values

macro sequence*(parsers: tuple): untyped =
  ## `sequence((a, b, c))` is `a` then `b` then `c`, answering `(A, B, C)`.
  let
    given = genSym(nskLet, "given")
    ps = genSym(nskVar, "parsers")
    node = genSym(nskLet, "node")
    R = genSym(nskType, "R")
    (pos, ctx) = (ident"pos", ident"ctx")
    (source, target) = (ident"source", ident"target")
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
    slots.add nnkBracketExpr.newTree(bindSym"Parser", newCall(bindSym"typeof", t))
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
    var `ps`: `slots`
    `takes`
    type `R` = typeof(`types`)
    let `node` = Parser[`R`](expected: `names`.join(" then "))
    `node`.parseFn = proc (`ctx`: Context): Result[`R`] =
      var `pos` = `ctx`.pos
      `parse`
      succeed(`values`, `pos`)
    `node`.fastFn = proc (`ctx`: Context): int =
      var `pos` = `ctx`.pos
      `fast`
      `pos`
    `node`.childrenFn = () => `kids`
    `node`.replaceFn = proc (`source`, `target`: ParserBase) = `swaps`
    `node`

proc `&`*[A, B](a: Parser[A], b: Parser[B]): Parser[(A, B)] = sequence((a, b))

# ---------------------------------------------------------------------------
# Ordered choice: the first alternative that succeeds

type ChoiceParser*[R] = ref object of Parser[R]
  alts: seq[Parser[R]]

proc oneOf(names: seq[string]): string =
  case names.len
  of 0: "no alternative"
  of 1: names[0]
  else: "one of " & names.join(", ")

proc choice*[R](alts: varargs[Parser[R]]): Parser[R] =
  var names: seq[string]
  for a in alts:
    if a.expected notin names: names.add a.expected
  let c = ChoiceParser[R](alts: @alts, expected: names.oneOf)
  c.parseFn = proc (ctx: Context): Result[R] =
    for alt in c.alts:
      result = alt.parseOn(ctx)
      if result.isSuccess: return
    if c.alts.len == 0: result = fail[R](c, ctx)
  c.fastFn = proc (ctx: Context): int =
    for alt in c.alts:
      let pos = alt.fastParseOn(ctx)
      if pos >= 0: return pos
    -1
  c.childrenFn = proc (): seq[ParserBase] =
    for alt in c.alts: result.add alt
  c.replaceFn = proc (source, target: ParserBase) =
    for alt in c.alts.mitems: swapIn(alt, source, target)
  c

proc `/`*[R](a, b: Parser[R]): Parser[R] =
  ## `a / b / c` is one flat choice; a named choice stays a unit.
  var alts: seq[Parser[R]]
  for x in [a, b]:
    if x of ChoiceParser[R] and x.name.len == 0: alts.add ChoiceParser[R](x).alts
    else: alts.add x
  choice(alts)

# ---------------------------------------------------------------------------
# Repetition. `max` < 0 is unbounded. An item that consumes nothing ends
# the run once `min` is met, so a nullable item cannot loop.

proc repeat*[R](item: Parser[R], min: int, max = -1): Parser[seq[R]] =
  ## Possessive: as many items as match, never giving input back.
  assert max < 0 or min <= max
  var item = item
  let p = Parser[seq[R]](expected: item.expected)
  p.parseFn = proc (ctx: Context): Result[seq[R]] =
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
  p.fastFn = proc (ctx: Context): int =
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

proc star*[R](item: Parser[R]): Parser[seq[R]] = item.repeat(0)
proc plus*[R](item: Parser[R]): Parser[seq[R]] = item.repeat(1)
proc times*[R](item: Parser[R], n: int): Parser[seq[R]] = item.repeat(n, n)

proc repeatLazy*[R](item: Parser[R], limit: ParserBase, min: int, max = -1): Parser[seq[R]] =
  ## Items until `limit` matches, as few as possible; `limit` is not consumed.
  assert max < 0 or min <= max
  var (item, limit) = (item, limit)
  let p = Parser[seq[R]](expected: item.expected)
  p.parseFn = proc (ctx: Context): Result[seq[R]] =
    var
      values: seq[R]
      pos = ctx.pos
    while values.len < min or limit.fastParseOn(ctx.at(pos)) < 0:
      if values.len >= min and max >= 0 and values.len >= max:
        return fail[seq[R]](limit, ctx.at(pos))
      var r = item.parseOn(ctx.at(pos))
      if not r.isSuccess: return failedAs(seq[R], r)
      if r.pos == pos and values.len >= min: return fail[seq[R]](limit, ctx.at(pos))
      values.add move(r.val)
      pos = r.pos
    succeed(values, pos)
  p.fastFn = proc (ctx: Context): int =
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

proc starLazy*[R](item: Parser[R], limit: ParserBase): Parser[seq[R]] = item.repeatLazy(limit, 0)
proc plusLazy*[R](item: Parser[R], limit: ParserBase): Parser[seq[R]] = item.repeatLazy(limit, 1)

proc repeatGreedy*[R](item: Parser[R], limit: ParserBase, min: int, max = -1): Parser[seq[R]] =
  ## As many items as match, then back up until `limit` matches after them.
  assert max < 0 or min <= max
  var (item, limit) = (item, limit)
  let p = Parser[seq[R]](expected: item.expected)
  p.parseFn = proc (ctx: Context): Result[seq[R]] =
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
      if stops.len == 1: return fail[seq[R]](limit, ctx.at(stops[0]))
      discard stops.pop
      discard values.pop
    succeed(values, stops[^1])
  p.fastFn = proc (ctx: Context): int =
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

proc starGreedy*[R](item: Parser[R], limit: ParserBase): Parser[seq[R]] =
  item.repeatGreedy(limit, 0)
proc plusGreedy*[R](item: Parser[R], limit: ParserBase): Parser[seq[R]] =
  item.repeatGreedy(limit, 1)

proc repeatSeparated*[R, S](item: Parser[R], sep: Parser[S], min: int,
                            max = -1): Parser[Separated[R, S]] =
  ## Items with `sep` between them; a trailing `sep` is left unconsumed.
  assert max < 0 or min <= max
  var (item, sep) = (item, sep)
  let p = Parser[Separated[R, S]](expected: item.expected)
  p.parseFn = proc (ctx: Context): Result[Separated[R, S]] =
    var
      list: Separated[R, S]
      pos = ctx.pos
    while max < 0 or list.elements.len < max:
      var
        at = pos
        s: Result[S]
      if list.elements.len > 0:
        s = sep.parseOn(ctx.at(pos))
        if not s.isSuccess:
          if list.elements.len < min: return failedAs(Separated[R, S], s)
          break
        at = s.pos
      var r = item.parseOn(ctx.at(at))
      if not r.isSuccess:
        if list.elements.len < min: return failedAs(Separated[R, S], r)
        break
      if r.pos == pos and list.elements.len >= min: break
      if list.elements.len > 0: list.separators.add move(s.val)
      list.elements.add move(r.val)
      pos = r.pos
    succeed(list, pos)
  p.fastFn = proc (ctx: Context): int =
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

proc starSeparated*[R, S](item: Parser[R], sep: Parser[S]): Parser[Separated[R, S]] =
  item.repeatSeparated(sep, 0)
proc plusSeparated*[R, S](item: Parser[R], sep: Parser[S]): Parser[Separated[R, S]] =
  item.repeatSeparated(sep, 1)
proc timesSeparated*[R, S](item: Parser[R], sep: Parser[S], n: int): Parser[Separated[R, S]] =
  item.repeatSeparated(sep, n, n)

proc foldLeft*[R, S](list: Separated[R, S], fn: (R, S, R) -> R): R =
  ## `((e0 sep0 e1) sep1 e2) …`; needs an element.
  result = list.elements[0]
  for i, sep in list.separators: result = fn(result, sep, list.elements[i + 1])

proc foldRight*[R, S](list: Separated[R, S], fn: (R, S, R) -> R): R =
  ## `e0 sep0 (e1 sep1 (e2 …))`; needs an element.
  result = list.elements[^1]
  for i in countdown(list.separators.high, 0):
    result = fn(list.elements[i], list.separators[i], result)

# ---------------------------------------------------------------------------
# One delegate, its result read anew

proc keepStop(stop, start: int): int = stop
  ## The default fast path of `through`: a named proc, since the JS
  ## backend emits a lambda default of a generic inside its first caller.

proc through[D, R](p: Parser[D], read: (var Result[D], Context) -> Result[R],
                   fast: (int, int) -> int = keepStop): Parser[R] =
  ## Callers instantiate it explicitly: Nim 2.2.12 does not infer `D`
  ## through the `var` parameter.
  var p = p
  let t = Parser[R](expected: p.expected)
  t.parseFn = proc (ctx: Context): Result[R] =
    var r = p.parseOn(ctx)
    read(r, ctx)
  t.fastFn = (ctx: Context) => fast(p.fastParseOn(ctx), ctx.pos)
  t.over(p)
  t

proc optional*[R](p: Parser[R]): Parser[Option[R]] =
  through[R, Option[R]](p, (r: var Result[R], ctx: Context) -> Result[Option[R]] =>
    (if r.isSuccess: succeed(some(move(r.val)), r.pos) else: succeed(none(R), ctx.pos)),
    (stop, start: int) => max(stop, start))

proc optional*[R](p: Parser[R], value: R): Parser[R] =
  ## `p`, or `value` where `p` does not match.
  through[R, R](p, (r: var Result[R], ctx: Context) -> Result[R] =>
    (if r.isSuccess: move(r) else: succeed(value, ctx.pos)),
    (stop, start: int) => max(stop, start))

proc map*[A, B](p: Parser[A], fn: (A) -> B): Parser[B] =
  ## `fn` is taken as pure: the fast path skips it. It is handed a copy of
  ## the value; a lambda with a `sink` parameter is handed the value itself.
  through[A, B](p, (r: var Result[A], ctx: Context) -> Result[B] =>
    (if r.isSuccess: succeed(fn(r.val), r.pos) else: failedAs(B, r)))

proc map*[A, B](p: Parser[A], fn: (sink A) -> B): Parser[B] =
  through[A, B](p, (r: var Result[A], ctx: Context) -> Result[B] =>
    (if r.isSuccess: succeed(fn(move(r.val)), r.pos) else: failedAs(B, r)))

proc pick*[T: tuple](p: Parser[T], i: static int): Parser[typeof(default(T)[i])] =
  ## One value of a tuple, moved out. `map(t => t[i])` copies it.
  through[T, typeof(default(T)[i])](p, (r: var Result[T], ctx: Context) -> Result[typeof(default(T)[i])] =>
    (if r.isSuccess: succeed(move(r.val[i]), r.pos)
     else: failedAs(typeof(default(T)[i]), r)))

proc elements*[R, S](p: Parser[Separated[R, S]]): Parser[seq[R]] =
  ## The elements of a separated list, moved out.
  through[Separated[R, S], seq[R]](p, (r: var Result[Separated[R, S]], ctx: Context) -> Result[seq[R]] =>
    (if r.isSuccess: succeed(move(r.val.elements), r.pos) else: failedAs(seq[R], r)))

proc delimited*[A, B, C](open: Parser[A], close: Parser[C], inside: Parser[B]): Parser[B] =
  ## `inside` between `open` and `close`, keeping only its value.
  sequence((open, inside, close)).pick(1)

proc `==>`*[A, B](p: Parser[A], fn: (A) -> B): Parser[B] = p.map(fn)

proc token*[R](p: Parser[R]): Parser[Token[R]] =
  through[R, Token[R]](p, proc (r: var Result[R], ctx: Context): Result[Token[R]] =
    if r.isSuccess:
      succeed(Token[R](value: move(r.val), input: ctx.input, start: ctx.pos, stop: r.pos), r.pos)
    else: failedAs(Token[R], r))

proc text*[R](t: Token[R]): string = t.input.text[t.start ..< t.stop]

proc ahead*[R](p: Parser[R]): Parser[R] =
  ## Positive lookahead: `p`'s value, no input consumed.
  through[R, R](p, (r: var Result[R], ctx: Context) -> Result[R] =>
    (if r.isSuccess: succeed(move(r.val), ctx.pos) else: move(r)),
    (stop, start: int) => (if stop < 0: -1 else: start))

proc where*[R](p: Parser[R], pred: (R) -> bool, expected: string): Parser[R] =
  ## `p`'s value where `pred` holds; otherwise a failure where `p` ended,
  ## the furthest point the judged span reached.
  var p = p
  let w = Parser[R](expected: expected)
  w.parseFn = proc (ctx: Context): Result[R] =
    let r = p.parseOn(ctx)
    if r.isSuccess and not pred(r.val): fail[R](w, ctx.at(r.pos)) else: r
  w.fastFn = w.recognising
  w.over(p)
  w

proc callCC*[D, R](p: Parser[D], handler: (Parser[D], Context) -> Result[R]): Parser[R] =
  ## `handler` is handed `p` and decides whether, how often and with what
  ## to run it: tracing, profiling, memoisation.
  var p = p
  let c = Parser[R](expected: p.expected)
  c.parseFn = (ctx: Context) => handler(p, ctx)
  c.fastFn = c.recognising
  c.over(p)
  c

# flatten, skip and negative lookahead only recognise their delegate

proc flatten*(p: ParserBase, expected = ""): Parser[string] =
  ## The input `p` consumed, as text; `p` builds nothing and its failures
  ## are reported as this node's.
  var p = p
  result = leaf[string](if expected.len > 0: expected else: p.expected,
                        (ctx: Context) => p.fastParseOn(ctx),
                        (ctx: Context, stop: int) => ctx.input.text[ctx.pos ..< stop])
  result.over(p)

proc skip*(p: ParserBase, expected = ""): Parser[Nothing] =
  var p = p
  result = leaf[Nothing](if expected.len > 0: expected else: p.expected,
                         (ctx: Context) => p.fastParseOn(ctx),
                         (ctx: Context, stop: int) => Nothing())
  result.over(p)

proc notAhead*(p: ParserBase, expected = ""): Parser[Nothing] =
  var p = p
  result = leaf[Nothing](if expected.len > 0: expected else: "not " & p.expected,
                         (ctx: Context) => (if p.fastParseOn(ctx) < 0: ctx.pos else: -1),
                         (ctx: Context, stop: int) => Nothing())
  result.over(p)

proc neg*(p: ParserBase, E: typedesc[char | byte] = char): Parser[E] =
  ## Anything but `p`: one `E` where `p` does not match.
  var p = p
  result = leaf[E]("not " & p.expected,
    (ctx: Context) => (if ctx.pos < ctx.input.stop and p.fastParseOn(ctx) < 0: ctx.pos + 1
                       else: -1),
    (ctx: Context, stop: int) => E(ctx.input.text[ctx.pos]))
  result.over(p)

# ---------------------------------------------------------------------------
# Trimming: `left` and `right` are skipped as often as they match

proc skipAll(trimmer: ParserBase, ctx: Context): int =
  result = ctx.pos
  while true:
    let next = trimmer.fastParseOn(ctx.at(result))
    if next < 0 or next == result: return
    result = next

proc trim*[R](p: Parser[R], left, right: ParserBase): Parser[R] =
  var (p, left, right) = (p, left, right)
  let t = Parser[R](expected: p.expected)
  t.parseFn = proc (ctx: Context): Result[R] =
    var r = p.parseOn(ctx.at(left.skipAll(ctx)))
    if r.isSuccess: succeed(move(r.val), right.skipAll(ctx.at(r.pos))) else: move(r)
  t.fastFn = proc (ctx: Context): int =
    let pos = p.fastParseOn(ctx.at(left.skipAll(ctx)))
    if pos < 0: -1 else: right.skipAll(ctx.at(pos))
  t.childrenFn = () => kids(p, left, right)
  t.replaceFn = proc (source, target: ParserBase) =
    swapIn(p, source, target)
    swapIn(left, source, target)
    swapIn(right, source, target)
  t

proc trim*[R](p: Parser[R], ws: ParserBase = whitespace()): Parser[R] = p.trim(ws, ws)

# ---------------------------------------------------------------------------
# Forward references: `undefined` then `define`; `resolve` removes them

type SettableParser*[R] = ref object of Parser[R]
  target: Parser[R]

proc nesting[R](p: Parser[R]): Parser[R] =
  ## `p` as one level of nesting, failing past `MaxDepth`.
  var p = p
  let
    n = Parser[R](expected: p.expected)
    deep = ParserBase(expected: "shallower nesting")
  n.parseFn = proc (ctx: Context): Result[R] =
    if ctx.input.depth >= MaxDepth: return fail[R](deep, ctx)
    inc ctx.input.depth
    result = p.parseOn(ctx)
    dec ctx.input.depth
  n.fastFn = proc (ctx: Context): int =
    if ctx.input.depth >= MaxDepth: return -1
    inc ctx.input.depth
    result = p.fastParseOn(ctx)
    dec ctx.input.depth
  n.over(p)
  n

proc undefined*[R](name = ""): SettableParser[R] =
  ## A placeholder that fails until it is `define`d.
  let s = SettableParser[R](name: name, expected: name, isRef: true)
  var standIn: Parser[R]
  s.target = failure[R](if name.len > 0: name else: "undefined parser")
  s.parseFn = (ctx: Context) => s.target.parseOn(ctx)
  s.fastFn = (ctx: Context) => s.target.fastParseOn(ctx)
  s.over(s.target)
  s.nestFn = proc (target: ParserBase): ParserBase =
    if standIn.isNil: standIn = nesting(Parser[R](target))
    standIn
  s

proc define*[R](p: SettableParser[R], target: Parser[R]) = p.target = target

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

proc resolve*[R](root: Parser[R]): Parser[R] =
  ## Rewire every parent past its forward references, leaving a node that
  ## counts the nesting where each placeholder was. Cycles stay.
  for p in root.allParsers:
    for c in p.children:
      let r = c.resolved
      if r != c: p.replace(c, r)
  Parser[R](root.resolved)

# ---------------------------------------------------------------------------
# Entry points

proc parse*[R](p: Parser[R], text: sink string): Result[R] =
  ## A failure reports the furthest position any node reached.
  let input = newInput(text)
  result = p.parseOn(Context(input: input))
  if not result.isSuccess:
    if input.furthestNodes.len > 0:
      result.failed = input.furthestNodes[^1]
      result.pos = input.furthestPos
    result.input = input

proc parse*[R](p: Parser[R], data: openArray[byte]): Result[R] = p.parse(data.toText)

proc accepts*(p: ParserBase, text: string): bool =
  p.fastParseOn(Context(input: newInput(text))) >= 0

proc accepts*(p: ParserBase, data: openArray[byte]): bool = p.accepts(data.toText)

proc complete*[R](p: Parser[R]): Parser[R] = (p & endOfInput()).pick(0)