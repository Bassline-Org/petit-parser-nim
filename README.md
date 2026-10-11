# petit-parser

A nim clone of the [PetitParser](https://github.com/petitparser) implementation for [Dart](https://github.com/petitparser/dart-petitparser).

The website describes it better than I could

>PetitParser makes writing parsers fast, enjoyable, and fully type-safe
> 
>Instead of configuring external code generators or writing cryptic regular expressions, PetitParser models grammars directly as composable objects in your programming language. Assemble small, specialized parsers as modular building blocks to model everything from configuration formats to full programming languages.

```nim
import petit_parser

let number = digit().plus.flatten("number").trim.map((s: string) => parseInt(s))
let list = number.plusSeparated(ch(',').trim).complete
echo list.parse("1, 2, 3").value.elements # @[1, 2, 3]
echo list.parse("1, 2,").message          # expected number at 1:6
```

```nim
# importing the json grammar
import petit_parser/grammar/json

let
  p = jsonParser()
  src = """ {"foo": "bar"} """

echo p.parse(src) # does the thing
```

## Grammars

There are currently two grammars available via `import petit_parser/grammar/<a-grammar>`.

- `json`

  Implements a (effectively untested) json parser following RFC 8259. It keeps numbers
as strings and decodes unicode strings.

- `sexp`

  Implements an extremely naiive sexp grammar with the atoms, strings, 
lists, quoting, and `;` comments.

- `bassline_text`

  Reads the bassline textual syntax into a light tree. Numbers are kept
as spelled, bytes as bytes, and text is decoded. `basslineParser` reads one value
and `basslineDocument` reads any number of them. The tests run the
shared bassline corpus against it.

- `bassline_ce`

  Reads bassline's canonical binary encoding into the same tree, without
validating it. Lengths are taken as stated and integers, utf-8, order
and duplicates are not checked. `ceParser` reads one value and
`ceDocument` reads a `.blb` file. The tests decode the corpus and check
it against the text.

- `extended_bassline_text`

  The text syntax with dialect blocks. `lang NAME [[ … ]]` reads the
block with the parser registered as NAME and puts its value where the
block stands, so another notation can be written inside bassline text
and still read as values. `extendedParser(dialects)` and
`extendedDocument(dialects)` take a `Dialects` table of name to
`Parser[BlNode]`. `standardDialects()` holds `sexp` and `json`.

  ```nim
  var dialects = standardDialects()
  dialects["words"] = word().plus.flatten("word").map(sym).trim.star.map(list)
  let p = extendedParser(dialects)
  echo p.parse("(q lang words [[ hello world ]] lang json [[ {\"a\": [1, 2]} ]])").value
  ```

  The block is a Lua long bracket. `[=[ … ]=]` at any level of `=` holds
content with `]]` in it, and a block inside a block needs a higher
level. `lang` is reserved, so the symbol has to be written `'lang'`. A
mark after the block, `lang sexp [[ a ]]!`, marks its value.

  A dialect is any `Parser[BlNode]`. It runs on the document itself with
the input cut at the closing bracket, so `endOfInput` matches there, a
failure inside reports its position in the document, and a dialect that
stops short fails with `the end of the block`. Resolve a dialect before
registering it. The parser also runs at compile time, so a document with
blocks can be read into a constant.

## Using the parsers

A parser is a value. Combining parsers gives you a new parser. Call
`p.parse(text)` to get a `Result`. It has `isSuccess`, `value`, `pos` and
`message`. Reading `value` on a failed result raises `ParseError`.
`p.accepts(text)` only checks that the input matches and builds nothing.
Both take a `string` or an `openArray[byte]`.

Finish a document parser with `complete`. Without it a parser that
matches a prefix of the input succeeds and the rest is ignored.

```nim
let r = (digit().plus & endOfInput()).parse("12x")
if not r.isSuccess: echo r.message   # expected one of digit, end of input at 1:3
```

### Characters

| Parser | Matches |
|---|---|
| `ch('a')`, `ch(0xA0'u8)` | one character, or one byte |
| `chars({'a'..'z'}, "lower")`, `chars("+-", "sign")` | one character from a set or a string |
| `noneOf("\"\\", "character")` | one character not in the string |
| `between('a', 'f')` | one character in a range |
| `pattern("a-zA-Z_")`, `pattern("^0-9")` | a character class, `^` negates it |
| `anyChar()`, `digit()`, `letter()`, `lowercase()`, `uppercase()`, `word()`, `whitespace()` | the usual classes, `word` is letters, digits and `_` |
| `bytes({0x00'u8 .. 0x7F'u8}, "ascii")`, `anyByte()` | the byte versions |

The `expected` argument is the name used in error messages, so use the
name of the thing the grammar wants ("digit", "sign") rather than a
description of the characters. Every call makes a new parser node.

### Literals and markers

| Parser | Returns |
|---|---|
| `str("let")`, `str([0xFF'u8])` | the literal |
| `strIgnoreCase("select")` | the input as written |
| `newline()` | `\r\n`, `\n` or `\r` |
| `endOfInput()` | `Nothing`, and only matches at the end |
| `epsilon()`, `epsilon(value)` | consumes nothing and always succeeds |
| `failure[R]("expected …")` | always fails |
| `position()` | the current position, consumes nothing |

### Sequence and choice

`a & b` returns the tuple `(A, B)`. `sequence((a, b, c))` does the same
for any number of parsers and returns `(A, B, C)`. `delimited(open, close,
inside)` runs all three and keeps only the value of `inside`.

`a / b / c` is ordered choice. The alternatives need the same result type.
The first one that matches wins and the others are never tried for that
input, so put the more specific alternative first (`str("<=") /
str("<")`). `/` flattens into one choice node. A `named` choice is kept as
a unit.

### Repetition

`star`, `plus`, `times(n)` and `repeat(min, max)` are possessive. They
take every item that matches and never give one back. An item that
consumes nothing ends the run, so `optional(x).star` cannot loop forever.

`starLazy(limit)`, `plusLazy` and `repeatLazy(limit, min, max)` take as
few items as possible and stop where `limit` matches. `limit` is not
consumed. Use these for "everything up to the delimiter" when the item
could also match the delimiter, for example
`anyChar().starLazy(str("*/"))`.

`starGreedy(limit)`, `plusGreedy` and `repeatGreedy` take as many items
as possible and then back up until `limit` matches after them. You will
not need these often. They keep every position they may have to return to.

`starSeparated(sep)`, `plusSeparated`, `timesSeparated(sep, n)` and
`repeatSeparated(sep, min, max)` read lists with separators between the
items. They return a `Separated` with `elements` and `separators`. A
trailing separator is left unconsumed. `foldLeft` and `foldRight` reduce
one with a `(a, sep, b) -> a` function, so
`term.plusSeparated(op).map(l => l.foldLeft(apply))` is a left
associative operator level.

### Reading values

`p.map(fn)` or `p ==> fn` transforms the value. `fn` is assumed to be pure
and is skipped when the parser is only recognising. `fn` gets a copy of the
value. `pick(i)` takes one value out of a tuple without copying it, so
prefer it to `map(t => t[i])`, and `elements` does the same for a
separated list.

`flatten` returns the text that `p` consumed as a string and does not
build any of `p`'s values. `flatten("number")` gives it a name for
messages. Use it instead of `plus` and `join` for runs of characters.
Since `p` only runs as a recogniser, a failure inside it is reported as
this node's failure, at the position where it started.

`skip` consumes what `p` consumes and returns `Nothing`. Use it for the
parts of a tuple you do not want.

`token` wraps the value in a `Token` with `start`, `stop` and `text`.

`where(pred, "expected …")` keeps the value when `pred` holds and fails
otherwise. The failure is reported where `p` ended, so it is the
furthest failure and shows in the message.

`optional` returns an `Option`. `optional(p, default)` returns `R` and
uses `default` when `p` does not match.

`trim()` skips whitespace on both sides. `trim(ws)` and `trim(left,
right)` take any recogniser and apply it as many times as it matches, so
`trim(whitespace().skip / comment)` skips comments as well.

### Lookahead

`ahead(p)` returns `p`'s value and consumes nothing.

`notAhead(p)` succeeds with `Nothing` where `p` does not match.

`neg(p)` is "anything but `p`". It fails if `p` matches and otherwise
consumes one character and returns it. `neg(p, byte)` does the same for
a byte. `neg(ch('"')).star.flatten` reads a string body.

### Recursion

A production that refers to itself, or to one that is defined later,
starts out as `undefined`. Until `define` it fails with its name. Call
`define` once its parts exist. `resolve` then takes the placeholder out
of the graph and leaves a node that counts how deep the references nest.
Past `MaxDepth` levels (1000, set with `-d:MaxDepth=…`) the parse fails
with `expected shallower nesting` instead of running out of stack. In a
debug build Nim's own call depth limit of 2000 calls is hit first, at
about 200 levels of the bassline grammar.

```nim
let value = undefined[int]("value")
let parens = delimited(ch('('), ch(')'), value)
value.define(digit().map(c => ord(c) - ord('0')) / parens)
let grammar = value.complete.resolve
```

`define` needs the placeholder itself, so keep `value` unwrapped and
apply `trim` or `map` where it is used rather than where it is declared.
Left recursion like `value.define(value & …)` loops forever. Use
`ExpressionBuilder` for grammars with that shape.

### Names and messages

`named("number")` sets a node's name and the word used for it in
messages. A failure reports the furthest position any node reached and
everything that was expected there, without duplicates, like `expected
one of ')', '+' at 1:11`. Wrappers that cannot fail on their own (`map`,
`optional`, the repetitions) use the name of their delegate. `flatten` and
`skip` do the same unless you give them a name. An unnamed choice is
described by its alternatives, `one of digit, '-'`, and an unnamed
sequence by its parts, `'-' then digit`.

### Operator precedence

`ExpressionBuilder` builds a precedence climbing grammar from a table.
Groups go from the tightest binding to the loosest. `wrapper` is for
parentheses and `left` and `right` set the associativity.

```nim
let b = newExpressionBuilder[int]()
b.primitive(digit().plus.flatten.trim.map(s => parseInt(s)))
b.group.wrapper(ch('(').trim, ch(')').trim, (l: char, v: int, r: char) => v)
b.group.prefix(ch('-').trim, (op: char, a: int) => -a)
b.group.right(ch('^').trim, (a: int, op: char, b: int) => a ^ b)
b.group.left(ch('*').trim, (a: int, op: char, b: int) => a * b)
b.group.left(ch('+').trim, (a: int, op: char, b: int) => a + b)
let calc = b.build.complete
```

### Extending

`callCC(handler)` gives `handler` the delegate parser along with the
current `Context`. The handler can run it with `parseOn`, skip it, run
it somewhere else or run it more than once. This is how you write
tracing, profiling, memoisation and dispatch on what was just read. `succeed(value, pos)` and `fail[R](node, ctx)` build results
and `failedAs(T, r)` carries a failure over to another result type. A
handler may set `Input.stop` to make the rest of the input end early for
a delegate, which is how dialect blocks are read. `children`, `replace`
and `allParsers` are the graph protocol that `resolve` is built on.

### How it runs

This is recursive descent over a PEG. Choice is ordered, repetition is
possessive, there is no memoisation and left recursion is not detected.
Each node has two paths. `parseOn` builds values and `fastParseOn` only
recognises and allocates nothing, except for greedy repetition.
`flatten`, `skip`, `notAhead`, `neg`, trimmers and repetition limits run
their delegate on the fast path.

## Tests

```sh
atlas-run tests
# or if you use nimble
nimble test
```

## License

MIT