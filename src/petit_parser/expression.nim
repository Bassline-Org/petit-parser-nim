## Operator-precedence grammars from a table, after Dart's ExpressionBuilder.
## Primitives are the operands; each group is one level over the groups
## before it, tightest first. `build` wires wrappers (parentheses and the
## like) back to the whole expression and answers one parser.

import std/sugar
import ./parser

type
  Group*[R] = ref object
    loopback: Parser[R]
    wrappers: seq[Parser[R]]
    prefixes, postfixes: seq[Parser[(R) -> R]]
    lefts, rights: seq[Parser[(R, R) -> R]]

  ExpressionBuilder*[R] = ref object
    loopback: SettableParser[R]
    primitives: seq[Parser[R]]
    groups: seq[Group[R]]

proc newExpressionBuilder*[R](): ExpressionBuilder[R] =
  ExpressionBuilder[R](loopback: undefined[R]("expression"))

proc primitive*[R](b: ExpressionBuilder[R], p: Parser[R]) = b.primitives.add p

proc group*[R](b: ExpressionBuilder[R]): Group[R] =
  result = Group[R](loopback: b.loopback)
  b.groups.add result

proc wrapper*[R, L, T](g: Group[R], left: Parser[L], right: Parser[T],
                       action: (L, R, T) -> R): Group[R] {.discardable.} =
  ## `left`, the whole expression, `right`.
  g.wrappers.add sequence((left, g.loopback, right)).map((t: (L, R, T)) => action(t[0], t[1], t[2]))
  g

proc prefix*[R, O](g: Group[R], op: Parser[O], action: (O, R) -> R): Group[R] {.discardable.} =
  g.prefixes.add op.map((o: O) => ((a: R) => action(o, a)))
  g

proc postfix*[R, O](g: Group[R], op: Parser[O], action: (R, O) -> R): Group[R] {.discardable.} =
  g.postfixes.add op.map((o: O) => ((a: R) => action(a, o)))
  g

proc left*[R, O](g: Group[R], op: Parser[O], action: (R, O, R) -> R): Group[R] {.discardable.} =
  ## Left-associative: `a op b op c` is `(a op b) op c`.
  g.lefts.add op.map((o: O) => ((a, b: R) => action(a, o, b)))
  g

proc right*[R, O](g: Group[R], op: Parser[O], action: (R, O, R) -> R): Group[R] {.discardable.} =
  ## Right-associative: `a op b op c` is `a op (b op c)`.
  g.rights.add op.map((o: O) => ((a, b: R) => action(a, o, b)))
  g

proc applyPrefixes[R](t: (seq[(R) -> R], R)): R =
  result = t[1]
  for i in countdown(t[0].high, 0): result = t[0][i](result)

proc applyPostfixes[R](t: (R, seq[(R) -> R])): R =
  result = t[0]
  for f in t[1]: result = f(result)

proc applyBinary[R](a: R, f: (R, R) -> R, b: R): R = f(a, b)

proc build[R](g: Group[R], inner: Parser[R]): Parser[R] =
  result = inner
  if g.wrappers.len > 0: result = choice(@[result] & g.wrappers)
  if g.prefixes.len > 0:
    result = sequence((choice(g.prefixes).star, result)).map(applyPrefixes[R])
  if g.postfixes.len > 0:
    result = sequence((result, choice(g.postfixes).star)).map(applyPostfixes[R])
  if g.rights.len > 0:
    let terms = result.plusSeparated(choice(g.rights))
    result = terms.map((l: Separated[R, (R, R) -> R]) => l.foldRight(applyBinary[R]))
  if g.lefts.len > 0:
    let terms = result.plusSeparated(choice(g.lefts))
    result = terms.map((l: Separated[R, (R, R) -> R]) => l.foldLeft(applyBinary[R]))

proc build*[R](b: ExpressionBuilder[R]): Parser[R] =
  ## The expression parser, its forward references resolved.
  result = choice(b.primitives)
  for g in b.groups: result = g.build(result)
  b.loopback.define(result)
  result = result.resolve
