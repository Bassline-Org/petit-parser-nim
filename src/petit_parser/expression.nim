## Operator-precedence grammars from a table, after Dart's ExpressionBuilder.
## Primitives are the operands; each group is one level over the groups
## before it, tightest first. `build` wires wrappers (parentheses and the
## like) back to the whole expression and answers one parser.

import std/sugar
import ./parser

type
  Group*[S, R] = ref object
    loopback: Parser[S, R]
    wrappers: seq[Parser[S, R]]
    prefixes, postfixes: seq[Parser[S, (sink R) -> R]]
    lefts, rights: seq[Parser[S, (sink R, sink R) -> R]]

  ExpressionBuilder*[S, R] = ref object
    loopback: SettableParser[S, R]
    primitives: seq[Parser[S, R]]
    groups: seq[Group[S, R]]

proc newExpressionBuilder*[S, R](): ExpressionBuilder[S, R] =
  ExpressionBuilder[S, R](loopback: undefined[S, R]("expression"))

proc primitive*[S, R](b: ExpressionBuilder[S, R], p: Parser[S, R]) = b.primitives.add p

proc group*[S, R](b: ExpressionBuilder[S, R]): Group[S, R] =
  result = Group[S, R](loopback: b.loopback)
  b.groups.add result

# Each action has a sink param version & a normal proc version

proc wrapper*[S, R, L, T](g: Group[S, R], left: Parser[S, L], right: Parser[S, T],
                          action: (L, sink R, T) -> R): Group[S, R] {.discardable.} =
  ## `left`, the whole expression, `right`.
  g.wrappers.add sequence((left, g.loopback, right)).map((t: sink (L, R, T)) => action(t[0], t[1], t[2]))
  g

proc wrapper*[S, R, L, T](g: Group[S, R], left: Parser[S, L], right: Parser[S, T],
                          action: (L, R, T) -> R): Group[S, R] {.discardable.} =
  g.wrapper(left, right, (l: L, a: sink R, r: T) => action(l, a, r))

proc prefix*[S, R, O](g: Group[S, R], op: Parser[S, O], action: (O, sink R) -> R): Group[S, R] {.discardable.} =
  g.prefixes.add op.map((o: O) => ((a: sink R) => action(o, a)))
  g

proc prefix*[S, R, O](g: Group[S, R], op: Parser[S, O], action: (O, R) -> R): Group[S, R] {.discardable.} =
  g.prefix(op, (o: O, a: sink R) => action(o, a))

proc postfix*[S, R, O](g: Group[S, R], op: Parser[S, O], action: (sink R, O) -> R): Group[S, R] {.discardable.} =
  g.postfixes.add op.map((o: O) => ((a: sink R) => action(a, o)))
  g

proc postfix*[S, R, O](g: Group[S, R], op: Parser[S, O], action: (R, O) -> R): Group[S, R] {.discardable.} =
  g.postfix(op, (a: sink R, o: O) => action(a, o))

proc left*[S, R, O](g: Group[S, R], op: Parser[S, O], action: (sink R, O, sink R) -> R): Group[S, R] {.discardable.} =
  ## Left-associative: `a op b op c` is `(a op b) op c`.
  g.lefts.add op.map((o: O) => ((a, b: sink R) => action(a, o, b)))
  g

proc left*[S, R, O](g: Group[S, R], op: Parser[S, O], action: (R, O, R) -> R): Group[S, R] {.discardable.} =
  g.left(op, (a: sink R, o: O, b: sink R) => action(a, o, b))

proc right*[S, R, O](g: Group[S, R], op: Parser[S, O], action: (sink R, O, sink R) -> R): Group[S, R] {.discardable.} =
  ## Right-associative: `a op b op c` is `a op (b op c)`.
  g.rights.add op.map((o: O) => ((a, b: sink R) => action(a, o, b)))
  g

proc right*[S, R, O](g: Group[S, R], op: Parser[S, O], action: (R, O, R) -> R): Group[S, R] {.discardable.} =
  g.right(op, (a: sink R, o: O, b: sink R) => action(a, o, b))

proc applyPrefixes[R](t: sink (seq[(sink R) -> R], R)): R =
  result = move t[1]
  for i in countdown(t[0].high, 0): result = t[0][i](result)

proc applyPostfixes[R](t: sink (R, seq[(sink R) -> R])): R =
  result = move t[0]
  for f in t[1]: result = f(result)

proc applyBinary[R](a: sink R, f: (sink R, sink R) -> R, b: sink R): R = f(a, b)

proc build[S, R](g: Group[S, R], inner: Parser[S, R]): Parser[S, R] =
  result = inner
  if g.wrappers.len > 0: result = choice(@[result] & g.wrappers)
  if g.prefixes.len > 0:
    result = sequence((choice(g.prefixes).star, result)).map(applyPrefixes[R])
  if g.postfixes.len > 0:
    result = sequence((result, choice(g.postfixes).star)).map(applyPostfixes[R])
  if g.rights.len > 0:
    let terms = result.plusSeparated(choice(g.rights))
    result = terms.map((l: sink Separated[R, (sink R, sink R) -> R]) => l.foldRight(applyBinary[R]))
  if g.lefts.len > 0:
    let terms = result.plusSeparated(choice(g.lefts))
    result = terms.map((l: sink Separated[R, (sink R, sink R) -> R]) => l.foldLeft(applyBinary[R]))

proc build*[S, R](b: ExpressionBuilder[S, R]): Parser[S, R] =
  ## The expression parser, its forward references resolved.
  result = choice(b.primitives)
  for g in b.groups: result = g.build(result)
  b.loopback.define(result)
  result = result.resolve
