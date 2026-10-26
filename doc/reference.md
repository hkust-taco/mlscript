# MLscript Language Reference

This document is a best-effort reference for the MLscript programming language
as found in the `hkmc2` branch of this repository,
which is an evolving language that has not stabilized just yet.

---

## Table of Contents

1. [File Format and Test Directives](#1-file-format-and-test-directives)
2. [Comments and Whitespace](#2-comments-and-whitespace)
3. [Literals](#3-literals)
4. [Variables and Bindings](#4-variables-and-bindings)
5. [Functions](#5-functions)
6. [Operators](#6-operators)
7. [Classes and Data Types](#7-classes-and-data-types)
8. [Objects, Modules, and Companions](#8-objects-modules-and-companions)
9. [Records and Tuples](#9-records-and-tuples)
10. [Arrays](#10-arrays)
11. [The Ultimate Conditional Syntax (UCS)](#11-the-ultimate-conditional-syntax-ucs)
12. [Algebraic Effects and Handlers](#12-algebraic-effects-and-handlers)
13. [Context Parameters (Type Classes)](#13-context-parameters-type-classes)
14. [Types and Type Aliases](#14-types-and-type-aliases)
15. [Modules, Imports, and Namespaces](#15-modules-imports-and-namespaces)
16. [Flow Inference and Leading Dot Access](#16-flow-inference-and-leading-dot-access)
17. [Indentation and Block Syntax](#17-indentation-and-block-syntax)
18. [Miscellaneous](#18-miscellaneous)
19. [Built-in Types and Prelude](#19-built-in-types-and-prelude)
20. [Compiler Debugging](#20-compiler-debugging)

---

## 1. File Format and Test Directives

The repository contains two kinds of MLscript files:

* **Compilation files**, in `hkmc2/shared/src/test/mlscript-compile/`, which are compiled to JavaScript `.mls` modules.
* **Diff-test files**, in `hkmc2/shared/src/test/mlscript/`, which contain both source code and *golden test output*.
  Lines beginning with `//│` are compiler output that is updated automatically — not source code.
  Regular `//` comment lines are source code.
  Diff-test blocks are separated by empty lines and tested one after the other.

The latter kind of files supports test-mode directives that control how the tests are run and what output is expected.
These are not part of the language syntax.
They must appear at the start of a block or at the very start of the file
(in which case they apply to the entire file).

Some examples:

| Directive | Meaning |
|---|---|
| `:js` | Run block in JS mode |
| `:wasm` | Run block in WASM mode |
| `:sjs` | Show generated JavaScript code |
| `:wat` | Show generated WebAssembly Text format |
| `:e` | Expect compilation error |
| `:pe` | Expect parse error |
| `:re` | Expect runtime error |
| `:w` | Expect warning |
| `:sjs` | Show generated JavaScript |
| `:pt` | Show parsed tree |
| `:expect <val>` | Assert the result equals `<val>` |
| `:fixme` | Known broken feature |
| `:todo` | Planned but not yet implemented |
| `:silent` | Suppress output |
| `:effectHandlers` | Enable effect handler support |
| `:flow` | Enable flow inference for resolution |
| `:lift` | Enable function and class lifting |

Some of the other available commands are documented in
.github/skills/hkmc2-difftests/references/commands-and-policies.md.

---

## 2. Comments and Whitespace

```mlscript
// This is a regular comment (source code)
```

Multi-line comments are not supported; use consecutive `//` lines.

MLscript is **indentation-sensitive**. An indented block creates a continuation of the enclosing expression. Explicit blocks use `{}`. Semicolons `;` sequence *expressions* (not statements) on one line:

```mlscript
1; id(2)
```

Statements are separated by commas `,`,
but commas can be omitted at the end of lines:

```mlscript
let x = 1, x + 1
// same as
let x = 1
x + 1

// Alternative syntax for *local* `let`, also supported:
let x = 1 in
  x + 1
// `x` is not visible after the `in` block
```

---

## 3. Literals

```mlscript
42          // Integer literal
3.14        // Floating-point literal
"hello"     // String literal
true        // Boolean literal
false       // Boolean literal
()          // Unit literal (empty tuple/record)
null        // Null
undefined   // Undefined
```

**String escape sequences:**
```mlscript
"\n"             // newline
"\t"             // tab
"\\"             // backslash
"\""             // double-quote
"\u0068"         // Unicode escape (4 hex digits)
"\u{1F600}"      // Unicode code-point escape (variable length)
```

**Tick-quoted identifiers become string literals:**
```mlscript
'hello         // equivalent to "hello"
r.'fieldName   // field access using symbol literal
```

**Arrays:**
```mlscript
[1, 2, 3]
[1, ...xs, 4]   // spread syntax
```

**Sequences:**
```mlscript
[1, 2, 3]
[1, ..xs, 4]   // "lazy spread" syntax, which builds/analyzes a sequence lazily
```

---

## 4. Variables and Bindings

### Immutable Binding (`let`)

```mlscript
let x = 42
let x = 1 in x + 1       // scoped let
```

`let` creates local definitions:
```mlscript
let x = 1
let y = 2
x + y
```

Multiple bindings under one `let`:
```mlscript
let
  x = 1
  y = 2
```

Lets support shadowing and "compound shadowing":
```mlscript
let x = 1
let x = x + 1   // shadows previous x, can refer to it
let x += 1      // same as above; no mutation is performed
```

### Mutable Value (`mut val`)

```mlscript
mut val x = 42
set x = 100          // assignment
set x += 1           // compound assignment
set x -= 1
set x *= 2
set x /= 2
```

Multiple assignments:
```mlscript
set
  x += 1
  y += 2
```

### Top-Level Value (`val`)

```mlscript
val x = 42
```

Inside classes/modules, `val` creates accessible fields:
```mlscript
class Foo with
  val x = 1
  mut val y = 2
```

### Local Values Inside Functions

```mlscript
fun foo() =
  val result = compute()
  result + 1
```

---

## 5. Functions

### Basic Function Definition

```mlscript
fun foo(x) = x + 1
fun add(x, y) = x + y
```

### Multiple Parameter Lists (Curried)

```mlscript
fun add(x)(y) = x + y
add(1)(2)               // = 3
```

### Generic Functions

```mlscript
fun id[A](x: A): A = x
fun map[A, B](f: A -> B)(xs: List[A]): List[B] = ...
```

### Type-Annotated Parameters and Return Types

```mlscript
fun foo(x: Int): Int = x + 1
fun bar(x: Int, y: Str): Bool = x > 0
```

### Optional Parameters

A parameter followed by `?` is optional: callers may omit its argument, which is then `null`.

```mlscript
fun greet(name: Str, greeting?: Str) =
  (if greeting is null then "Hello, " else greeting + ", ") + name
print \ greet("Ana")             // prints: Hello, Ana
print \ greet("Ana", "Hi")       // prints: Hi, Ana
```

The annotation of an optional parameter includes `null`: `greeting?: Str` has type `Str | null`.
The `?` must directly follow the parameter: `y ?` and `y ?: Str` are not optional parameters.

Optional parameters follow required ones.
Function, lambda, and constructor parameters can be optional;
context parameters (`using`) and variadic parameters cannot.

Direct calls must supply every required argument, and no more arguments than the function accepts.
A function that receives extra arguments might ignore them at runtime (unspecified behavior).

### Variadic Parameters

A parameter prefixed with `...` collects any number of arguments into an array.
Parameters may follow it; they receive the last arguments.

```mlscript
fun f(...xs) = xs
f(1, 2, 3)               // = [1, 2, 3]
fun g(x, ...xs, y) = [x, xs, y]
g(1, 2, 3, 4)            // = [1, [2, 3], 4]
g(1, 2)                  // = [1, [], 2]
```

The required parameters take the first and last arguments, the optional parameters take the remaining
ones from left to right, and the variadic parameter collects the rest:

```mlscript
fun h(x, y?, ...xs, z) = [x, y, xs, z]
h(1, 2)                  // = [1, undefined, [], 2]
h(1, 2, 3)               // = [1, 2, [], 3]
h(1, 2, 3, 4, 5)         // = [1, 2, [3, 4], 5]
```

A parameter list has at most one variadic parameter, and the parameters following it must be required.
Class parameters cannot be variadic.

### Droppable Parameters

`drop` marks a parameter that implementations may ignore and may even omit to specify.
In a function type, it lets the functions passed for it leave out that parameter:

```mlscript
fun app(f: (Int, drop Int) -> Int) = f(1, 2)
app(x => x)              // = 1
app((x, i) => x + i)     // = 3
```

A variadic parameter can also be droppable, as in `(Int, drop ...Array[Int]) -> Int`.
Callers of a definition such as `fun first(x, drop y) = x` must still pass the argument of `y`.
Only function and lambda parameters can be droppable.

### Recursive Functions

Functions can make recursive calls:
```mlscript
fun fact(n) =
  if n <= 1 then 1 else n * fact(n - 1)
```

Mutual recursion is permitted among `fun` definitions in the same block
or through method calls.

### Trailing arguments

The `\` keyword, which binds very strongly on the left and very loosely on the right, can be used to provide extra arguments in a call. Representative examples:

```fs
tuple() \ 1 + 1
== tuple(1 + 1)

// Also allowed:
tuple \ 1 + 1
== tuple(1 + 1)

tuple(1, 2) \ 3
== tuple(1, 2, 3)

tuple(1)
  \ 2
== tuple(1, 2)

tuple
  \ 1
  \ 2
 == tuple(1, 2)
```

Operator applications also extend this way: `+(1) \ 2` and `{ + 1 } \ 2` both mean `+(1, 2)`;
`{ a + b } \ c` means `+(a, b, c)`. Parentheses keep the call result separate: `(+ 1) \ 2` calls that result.
The left-precedence of `\` is very high: `a + f \ x` means `a + f(x)`.

### Lambdas

```mlscript
x => x + 1
(x, y) => x + y
() => 42
=> 42                 // also a zero-argument lambda
```

### Underscore lambda shorthand

Each `_` becomes a new anonymous parameter (left to right).

Only a few places can introduce underscore lambdas:
* the RHS of the `\` keyword;
* the RHS of any operator that ends with `>` (except the builtin `>`), in both prefix and infix applications;
* symmetrically, the LHS of any operator that begins with `<` (except the builtins `<` and `<=`)

For example, `%> _ + 1` means `%>(x => x + 1)`. In an explicit call, use `%>(=> _ + 1)` to introduce that lambda.

This means we can write things like
```fs
42 |> _ + 1

_.getKey <|
  let r = result()
  print(r)
  r.field

number
  |> _ + 1
  |> Math.pow(_, 2)
  .toHexString

xs.map \ _ + 1

xs.reduce \ f(_) + _

xs.foldLeft(0) \ getValue(_) + _
==
xs.foldLeft(0, (x, y) => getValue(x) + y)

xs.foldLeft(0) \ getValue(_.key) + _
==
xs.foldLeft(0, (x, y) => getValue(x.key) + y)

f >> g(_) + 1
```

Moreover, `=>` can be used in prefix position, which lets the parameter list be inferred implicitly:

```fs
xs.map(=> _ + 1)

let f =
  => _ + 1
xs.map(f)

// This is admittedly a bit strange-looking, but we quickly get used to it:
let f = => _ + 1 in xs.map(f)
```

An explicit prefix `=>` always creates a lambda. If it contains no `_` placeholders,
the lambda takes zero arguments: `=> new C()` constructs a fresh instance whenever
called. Implicit delimiter positions such as `f \ expr` and `value |> expr` keep
expressions without placeholders eager.

A bare `new C` partially applies a constructor when `C` has a parameter list.
If its only list accepts zero arguments (including an all-optional list), the
compiler warns: write `new C()` to construct the instance, or `=> new C()` for
an explicit zero-argument factory. A class declared without parameter lists
still constructs immediately with `new C`.

### More examples

```fs
xs
  .map \ _ + 1
  .map \ _ * 2

xs
  .map \ x =>
    print(x)
    doThings(x)
  .filter \ _ < 100

xs.groupMapReduce
  \ _.key
  \ _.value
  \ _ + _

getValue(...)
  !> print(_.someField)  // `!>` is Scala's `tap`
  |> _.someOtherField
```

### Function Declarations (without definition)

```mlscript
fun foo: Int -> Int         // declares signature only
declare fun parseInt(str: Str, radix: Int): Int
```

### Operator Functions

Define a function with a symbolic name:
```mlscript
fun (++) concat(a, b) = a + b
fun (**) pow(a, b) = Math.pow(a, b)
fun (:::) appendAll[A](a, b): A = a + b
```

Use the symbolic name as an infix operator:
```mlscript
"hello" ++ " world"
2 ** 10
```

Operators can also be used as ordinary identifiers:
```mlscript
(++) of "a", "b"
++("a", "b")
+(2, 3)             // = 5
```

Whitespace before the operands are allowed in prefix position, as in `let sum = + (2, 3)`;
on a new line after an expression, it enables [infix continuation](#newline-operator-rules).

Symbolic operator identifiers also support prefix application with one operand,
using the same right precedence as in infix position.
Curly and indented blocks provide a single operand; explicit calls and type arguments retain ordinary call syntax.

A parenthesized infix RHS with multiple expressions supplies multiple arguments: `a op (b, c)` means `op(a, b, c)`.
A single parenthesized expression keeps its grouping, and `a op ()` passes the unit value: `op(a, ())`.
Precedence is unaffected: `1 + (2) * 3` means `1 + (2 * 3)`.
Parentheses cannot sequence expressions, so `(2, 3)` alone and `1 + (2, 3) * 4` are rejected;
use braces for a sequenced operand, as in `1 + ({2, 3})`.

```mlscript
fun (%>) wrap(x) = [x]
let a = %> 1 + 2 * 3 // %>(1 + 2 * 3)
let b = %> foo(1)    // %>(foo(1))
let c = %>
  e                  // %> { e }
```

### Function Application Syntaxes

```mlscript
f(x)             // standard call
f(x, y)          // multi-arg call
f of x, y        // `of` keyword: f(x, y)
f @ x            // `@` operator: left-associative application, f(x)
x |> f           // pipe forward: f(x)
f <| x           // pipe backward: f(x)
x !> f           // tap/tee: f(x) and returns x, ie, `let tmp = x in f(tmp); tmp`
x \f(args)       // receiver syntax: f(x, args)
x f(args)        // "juxtaposition" syntax: f(x, args) – will probably be removed in the future
f(1, 2, a: 3, 4, b: 5)  // named argument (becomes record, as in f(1, 2, 4, {a: 3, b: 5}))
f(using x)       // pass context/implicit argument
```

### `case` — Anonymous Pattern-Matching Function

`case` creates a function that pattern-matches its argument:

```mlscript
case x then x      // identity function: x => x
case { x then x }

case
  Some(v) then v
  None    then 0

val isDefined = case
  Some then true
  None then false

1 |> case x then x    // = 1
```

### Return

```mlscript
fun foo(x) =
  if x do
    return 42
  0
```

`return` is only valid inside function bodies (not at top level or inside lambdas).

```mlscript
fun f =
  print("reachable")
  return
  print("unreachable")
```

---

## 6. Operators

### Standard Operators

```mlscript
+  -  *  /  %       // arithmetic
==  !=  ===  !==    // equality (== is deep structural, === is strict/reference)
<  <=  >  >=        // comparison
&&  ||              // short-circuit boolean (strict boolean inputs)
and  or  not        // boolean keywords
```

Note: `==` is a deep structural equality (compares arrays and class fields recursively), while `===` is JavaScript strict equality.

### Comma-Operators

Prefix a comma before an operator to apply it to the entire LHS:
```mlscript
2 + 2 ,* 3        // = (2 + 2) * 3 = 12
// or
2 + 2 , * 3
```
This can also be laid out on several lines, where as usual the comma is optional at the end of the line:
```mlscript
2 + 2
* 3
// NOTE: different from
2 + 2
  * 3
```

### Pipe and Application Operators (from Predef)

| Operator | Name | Behavior |
|---|---|---|
| `\|>` | pipe | `x \|> f` = `f(x)` |
| `<\|` | reverse pipe | `f <\| x` = `f(x)` |
| `!>` | tap/tee | `x !> f` = `(f(x); x)` |
| `@` | apply | `f @ x` = `f(x)` |
| `>>` | andThen | `(f >> g)(x)` = `g(f(x))` |
| `<<` | compose | `(f << g)(x)` = `f(g(x))` |
| `\` | passTo | `x \f(a)` = `f(x, a)` |
| `.>` | pipeIntoHi | high-precedence `\|>` |
| `<.` | pipeFromHi | high-precedence `<\|` |

### Newline Operator Rules

At the same indentation, an operator at the start of a line continues the preceding expression when followed by a space,
line break, or curly/indented block. In all other cases, it starts a new prefix expression.
This rule applies uniformly to symbolic operators; indented continuations need no separating space:
```mlscript
2
+2          // separate prefix expression, yielding 2

2
+ 2         // infix continuation, yielding 4

2
  +2        // indented continuation, yielding 4

2
  + 2        // same

2
  + 2
  * 3       // operator split: indented operators at the same level
```

Operator split — operands at the same indent form branches:
```mlscript
if x >
  0 then true
  1 then "gt1"
// means: branches (x > 0) and (x > 1)
```

---

## 7. Classes and Data Types

### Basic Class

```mlscript
class Foo
class Foo()
class Foo(x: Int)
class Foo(x: Int, y: Str)
class Foo[A]
class Foo[A](x: A)
class Foo(x)(y)              // multiple parameter lists
```

### Data Class

`data class` provides structural equality, auto-generated `toString`, and field access:

```mlscript
data class Pair(fst, snd)
data class Some[T](value: T)
```

### Abstract Class

```mlscript
abstract class Option[T]: Some[T] | None
abstract class List[out T]: Cons[T] | Nil
```

Abstract classes can list their subtypes after `:`.

### Class with Body

```mlscript
class Counter with
  mut val count = 0
  fun increment() = set count += 1
  fun get() = count

class Foo(x: Int) with
  val doubled = x * 2
  fun show() = "Foo(" + String(x) + ")"
```

### Field Visibility

```mlscript
class Foo(x)            // x is private (not accessible outside)
class Foo(val x)        // x is a public immutable field
class Foo(mut val x)    // x is a public mutable field
class Foo(x, val y, mut val z)  // mixed
```

### Inheritance

```mlscript
class Bar(y) extends Foo(y * 2)
data class Baz(z) extends Bar(z * 1) with
  fun show() = "Baz"

abstract class Option[T]: Some[T] | None
data class Some[T](value: T) extends Option[T]
object None extends Option[Nothing]
```

Under new resolution, classes, objects, and modules without an explicit parent
inherit Object's declared member interface. Explicit parents and members declared
on the receiver take precedence.

### Class with Multiple Parameter Lists

```mlscript
class Foo(x)(y)
class Foo()(val x)      // auxiliary parameter list for public field
```

### Virtual Methods

```mlscript
abstract class Shape with
  virtual fun area: Num

class Circle(radius: Num) extends Shape with
  fun area = Math.PI * radius * radius
```

### Covariant/Contravariant Type Parameters

```mlscript
abstract class List[out T]       // covariant
abstract class Consumer[in T]    // contravariant
```

### Instantiation

```mlscript
new Foo          // create (static class required)
new Foo()        // with empty args
new Foo(1, 2)    // with args
new mut Foo      // mutable instance (not frozen)
new! c           // dynamic instantiation (class value at runtime)
new Foo(...xs)   // spread args
```

---

## 8. Objects, Modules, and Companions

### Singleton Object

```mlscript
object Foo
object Foo extends Bar
object Foo with
  val x = 42
  fun greet() = "Hello!"
```

### Module

A *module* is like a namespace / companion object:

```mlscript
module Foo with
  val x = 1
  fun f(y) = y + x

module Foo with ...    // module with lazy/deferred body
```

### Companion Pattern

A class and a module can share the same name. The module becomes the companion:

```mlscript
class Stack[A]
module Stack with
  fun empty[A](): Stack[A] = Nil
  data class (::) Cons[A](head: A, tail: Stack[A])
  object Nil
```

Access companion members with `.`:
```mlscript
Stack.empty()
Stack.Cons(1, Stack.Nil)
```

### Module-Typed Parameters and Values

```mlscript
fun f(module m: M) = m.foo()
val v: module M = M
fun f(): module M = M
```

### Extending Modules

Modules cannot extend classes. Objects can extend classes.

---

## 9. Records and Tuples

### Record Literals

```mlscript
{a: 1, b: 2}          // immutable (frozen) record
mut {a: 1, b: 2}      // mutable record
(a: 1, b: 2)          // record in parentheses (same thing)
```

### Field Access

```mlscript
r.field              // standard field access
r."fieldName"        // string-key field access
r.'fieldName         // tick-quoted field access
r.(expr)             // dynamic field access (expression result as key)
r!field              // dynamic field access using `!` (string "field")
r!("fieldName")      // dynamic field access with string
!(r)                 // accesses `.value` field (legacy BbML syntax)
```

### Record Puns

Short-hand for `field: field`:

```mlscript
(:a)              // equivalent to (a: a)
{:a, :b}          // equivalent to {a: a, b: b}
:x                // in block record context: creates field x: x
```

### Setting Record Fields

```mlscript
set r.field = v
set r."name" = v
```

### Then-Record Syntax

In `if` expressions, `field: value` creates a record:
```mlscript
if true then success: 42             // = {success: 42}
if true then success: 42 else failure: "oops"
```

### Records as Named Arguments

Named arguments compile to record literals:
```mlscript
f(a: 0)              // calls f({a: 0})
f of a: 0, b: 1      // calls f({a: 0, b: 1})
```

With positional and named arguments mixed, positional values are followed by
one record containing the named fields. Expressions still evaluate in source
order, and later occurrences of a named field overwrite earlier ones.
Here `a: expression` is a field value, not a type annotation.

---

## 10. Arrays

```mlscript
[1, 2, 3]            // array literal
mut [1, 2, 3]        // mutable array

xs.[0]               // index access (uses .at() internally)
xs![0]               // dynamic index access
xs.(0)               // dynamic index access
set xs.[0] = v       // index assignment
```

Under new resolution, `xs.[i]` is checked like the array's methods: `xs` must be
an array, and the result has its element type. A dynamic access such as `xs![i]`
is only checked at runtime, and so are operations on its result.

**Spread syntax:**
```mlscript
[1, ..xs, 4]         // lazy spread — xs is expanded in the middle
[..xs]               // all of xs – does not do anything
[...xs]              // JS-style spread (expands into a JS array)
```

**Array methods** (from Predef/Iter):
```mlscript
xs.push(v)
xs.pop()
xs.length
xs.at(i)
xs.concat(ys)
xs.map(f)
xs.filter(f)
xs.forEach(f)
```

**Varargs / rest parameters:**
```mlscript
fun f(...xs) = xs        // xs is an array
fun g(x, ...rest) = rest
f(1, 2, 3)               // xs = [1, 2, 3]
```

See [Variadic Parameters](#variadic-parameters).

Under new resolution, an annotation on a rest parameter describes the whole rest
array. Tuple values support precise zero-based projections such as `xs.0` and
inherit the declared Array interface.

Mutable array literals collect element shapes from their initializer and later
writes. Statically resolved element reads are checked against all those shapes.
For example,
after `let xs = mut [First(1)]` followed by `xs.push(Second(2))`, resolution
considers both `First` and `Second` when checking `xs.0`, even though the runtime
value at index 0 is still a `First`. Overwriting or removing an element does not
remove its shape from consideration. Resolution does not track individual
positions or the array's length.

An explicit annotation such as `Array[Base]` makes element reads use the members
declared by `Base`. Storing a `Child` that extends `Base` does not permit access
to `Child`-only members through that annotation.

Array callbacks such as `map` receive the element, index, and array. The index and
array parameters are [droppable](#droppable-parameters), so callbacks may take only
the element: `xs.map(x => x + 1)`. `reduce` also passes the accumulator first, and must
be given an initial value: `xs.reduce((acc, x) => acc + x, 0)`. Without one,
JavaScript uses the first element as the initial accumulator, which the declared
signature does not describe.

---

## 11. The Ultimate Conditional Syntax (UCS)

The UCS is MLscript's unified `if`/`while`/`case` expression supporting pattern matching, guards, and multi-way branching. It replaces traditional `match`/`switch` constructs.

### Basic `if` Expression

```mlscript
if condition then expr1 else expr2

// Indented form:
if condition then
  expr1
else
  expr2
```

### `if` with Pattern Branches (`is`)

```mlscript
if x is
  Some(v) then v
  None    then 0
```

Inline:
```mlscript
if x is Some(v) then v else 0
```

### Multi-Way `if` (Without Scrutinee)

```mlscript
if
  x > 0  then "positive"
  x == 0 then "zero"
  else        "negative"
```

### `and` Guards

```mlscript
if x is
  Some(v) and v > 0 then "positive"
  Some(v) and v < 0 then "negative"
  Some(_)           then "zero"
  None              then "absent"
```

Nested `and` with sub-branching:
```mlscript
if x is
  Some(v) and
    v > 0 then "positive"
    v < 0 then "negative"
    _     then "zero"
  None then "absent"
```

### Cross-Scrutinee Matching

```mlscript
if x is
  Left(xv) and y is Left(yv) then xv + yv
  Right(xv) and y is Right(yv) then xv * yv
  None and y is None then 0
```

### `do` Consequent

`do` is like `then` but does not return a value and does not require exhaustiveness; it is used for side effects.
The overall expression continues on the next line:

```mlscript
if x do
  print("executed")

if x is
  Some(0) do set x = None
  Some(v) and v % 2 == 0 do set x = Some(v / 2)
x
```

NOTE: misusing `then` here won't work, as `then` reuqires exhaustiveness:

```mlscript
if x then  // will crash with Match Error when `x` is not true
  print("executed")
```

### `else` Clause

```mlscript
if x is
  Foo then 1
  Bar then 2
  else 3          // default case

// Inline:
fun f(x) = if x is Some(v) then v else 0
```

### Operator Split

Pattern-match on the result of an expression with different operators:

```mlscript
if x >
  0 then "positive"
  1 then "greater than 1"
```

Equivalent to `(x > 0) then ...` and `(x > 1) then ...`.

```mlscript
if (1 + 2)
  * 3 === 12 then 0
  * 4 === 12 then 1
```

### `while` Loop with UCS

```mlscript
while condition do
  body

while xs is
  head :: tail do
    process(head)
    set xs = tail
```

### Interleaved `let` in UCS

`let` bindings can be interleaved between branches:

```mlscript
if
  let tp1_n = normalize(tp1)
  tp1_n is Bot then Bot
  let tp2_n = normalize(tp2)
  tp2_n is Bot then Bot
  let m = merge(tp1_n, tp2_n)
  m is Some(tp) then tp
  m is None     then glb(tp1_n, tp2_n)
```

### `case` — Implicit Scrutinee

`case` is like `if ... is ...` but takes its scrutinee as an argument (it creates a function):

```mlscript
fun length = case
  Nil        then 0
  Cons(_, t) then 1 + length(t)

// Equivalent to:
fun length(xs) = if xs is
  Nil        then 0
  Cons(_, t) then 1 + length(t)
```

Inline `case`:
```mlscript
1 |> case x then x + 1
```

### Constructor Patterns

```mlscript
if x is Some(v) then v else 0
if x is Cons(h, t) then h else ...
if x is Pair(fst, snd) then fst + snd
```

### Literal Patterns

```mlscript
if x is
  0     then "zero"
  1     then "one"
  "foo" then "foo string"
  true  then "yes"
  false then "no"
```

### Wildcard Pattern

```mlscript
if x is
  Some(v) then v
  _       then 0
```

### Tuple / Array Patterns

```mlscript
if xs is
  []        then 0
  [x]       then x + 1
  [x, y]    then x + y
  [x, y, z] then x + y + z
```

Rest spread in tuple patterns:
```mlscript
if xs is
  [..ys]       then ys          // all elements into ys
  [x, ..ys, z] then x + z       // head, spread, tail
  [..]         then "non-empty"
```

### Record Patterns

```mlscript
if r is
  { x: a, y: b } then a + b

// Pun syntax:
if r is
  { :x, :y } then x + y

// Nested:
if r is
  { x: { :y, z: t } } then y + t

// String and tick-quoted keys:
if r is { "x": x } then x
if r is { 'x: x } then x
```

### `as` Pattern Alias

With `newResolution` enabled, capitalization distinguishes binding from matching:
`p as name` binds the result of `p` to the lowercase name, even if that name is
already in scope. `p as Name` matches the result of `p` against the uppercase
constructor name; it does not introduce a binding. Constructor names follow the
usual lookup rules, including selective and wildcard opens. An unknown uppercase
name is an error.

```mlscript
fun map(f) = case
  Some(x as n) then Some(f(n))
  None as n    then n

fun foo = case
  Some(Some(a as b) as c) as d then [a, b, c, d]
```

### Conjunction Pattern (`&`)

Matches a value against multiple patterns simultaneously:

```mlscript
if v is A & B then ...      // v must be both A and B

fun suffixes(l) = if l is
  Nil then Cons(Nil, Nil)
  l & (_ :: tl) then l :: suffixes(tl)
```

### Disjunction Pattern (`|`)

```mlscript
fun foo(x) = x is Pair | Int
// matches if x is either a Pair or an Int

fun foo(x) = x is
  Pair | Int    // same as above, indented
```

### `where` Guard

```mlscript
fun orderedPair(p) = p is
  Pair(a, b) where a <= b

fun foo(p) = p is
  Pair(a, b) where
    let c = a
    a == 0
```

### Named Pattern (`is t` Capture)

```mlscript
if id(0) is t then t   // binds result of id(0) to t
```

### `pattern` Definitions

```mlscript
pattern Positive = ((Int as x) where x > 0) => x
pattern OrderedPair = (Pair(a, b) where a < b) => b - a
pattern Bin = | 0 | 1
```

The `=> result` part is the *extractor* — what gets bound when the pattern succeeds:
```mlscript
Pair(1, 2) is OrderedPair as 1    // true, and result = 1
```

Patterns with combined constructors:
```mlscript
pattern OrderedPairLike = (Pair(a, b) | [a, b] where a < b) => b - a
```

### Coverage Checking

MLscript checks for exhaustiveness of abstract class hierarchies:

```mlscript
abstract class Term: Abs | App | Var
// Matching on Term must cover Abs, App, Var
```

Missing cases produce compilation errors with `:e`.

### `refined` Keyword in Patterns

```mlscript
if term is refined(Term) and term is
  Abs(_, _) then true
  Var(_)    then false
  App(_, _) then false
```

### `@compile` Annotation on Patterns

The `@compile` annotation forces compile-time expansion of a pattern:

```mlscript
open annotations { compile }
fun foo(x) = if x is @compile Box then "yes" else "no"
fun foo(x) = if x is @compile 42 then "yes" else "no"
```

---

## 12. Algebraic Effects and Handlers

MLscript supports algebraic effects and handlers, enabled with `:effectHandlers` directive.

### Defining Effect Classes

Effect classes declare *operations* that can be performed:

```mlscript
abstract class Effect with
  fun perform(arg: Str): Str

abstract class Generator with
  fun produce(result): ()

class Logger with
  fun info(s: Str): ()
```

### Handling Effects

`handle h = EffectClass with { fun op(args)(k) = ... }` creates a handler `h`. The continuation `k` represents the rest of the computation:

```mlscript
handle h = Effect with
  fun perform(arg)(k) = k(arg)   // resume with arg
h.perform("k")
```

Abandoning the continuation (aborting):
```mlscript
handle h = Effect with
  fun perform(arg)(k) = "b"     // discard continuation
h.perform("t")
```

Invoking continuation multiple times (multi-shot):
```mlscript
handle h = Logger with
  fun info(s)(k) =
    print(s)
    k()
    k()         // call continuation twice
h.info("a")
```

### Handler with Body Scope (`in`)

```mlscript
handle h = Effect with
  fun perform(arg)(k) =
    let v = k(arg)
    result = result + arg
    v
in
  h.perform("1")
  h.perform("2")
  h.perform("3")
```

### Performing Effects

```mlscript
h.perform("hello")
```

### Nested Handlers

```mlscript
handle h1 = Effect with
  fun f(x)(k) = ...
handle h2 = Effect with
  fun f(x)(k) = ...
// h1 and h2 are now in scope
g(h1, h2)
```

### Generators (Example)

```mlscript
abstract class Generator with
  fun produce(result): ()

fun permutations_foreach(l, f) =
  handle gen = Generator with
    fun produce(result)(resume) =
      f(result)
      resume(())
  permutations(gen, l)

permutations_foreach([1, 2, 3], print)
```

### Non-Local Returns

```mlscript
fun foo(x) =
  (() => return 100)()
  print("Bad")         // unreachable
foo()
```

`return` inside a lambda captures the enclosing function's return.

---

## 13. Context Parameters (Type Classes)

MLscript has context parameters (`using`) which enable type-class-style programming.

### Introducing Context Instances (`using ... = ...`)

```mlscript
using Int = 42
using Foo[Int] = new IntFoo()
using Str = "hello"
```

### Functions with Context Parameters

```mlscript
module M with
  fun foo(using Int) = use[Int]
  fun bar(using n: Int): Int = n
  fun baz(using foo: Int, bar: Str) = ...
```

### Named Context Parameters

```mlscript
fun f(using someInt: Int) = someInt
using Int as i = 24
```

### Multiple Context Parameter Lists

```mlscript
fun f(using Int)(using Str) = ...
fun g(x: Int)(using Str) = ...
```

### Summon / `use[T]`

Retrieve the current context instance of type `T`:

```mlscript
fun use[T](using instance: T) = instance  // defined in Predef

using Int = 42
use[Int]                  // = 42
use[Str]                  // error if not in scope
```

### Class Context Parameters

Classes can take context parameters:
```mlscript
class Foo(using Int) with
  fun foo = use[Int]
  fun bar = summon

using Int = 99
Foo                       // creates Foo with context Int = 99
Foo.foo                   // = 99
```

Public context field:
```mlscript
class Foo(using val n: Int)
Foo.n      // = the context Int value
```

### Type Class Example (Monoid)

```mlscript
abstract class Monoid[T] with
  fun combine(a: T, b: T): T
  fun empty: T

object IntAddMonoid extends Monoid[Int] with
  fun combine(a: Int, b: Int): Int = a + b
  fun empty: Int = 0

using Monoid[Int] = IntAddMonoid
```

---

## 14. Types and Type Aliases

### Type Aliases

```mlscript
type Foo = Int
type Pair[A, B] = { fst: A, snd: B }
type Option[A] = Some[A] | None
type Result[A, B] = Ok[A] | Error[B]
```

### Union Types

```mlscript
type Expr = Lit | Add | Sub
abstract class Shape: Circle | Rectangle | Triangle
```

### Intersection/Conjunction in Types

```mlscript
type T = A & B
```

### Type Annotations

```mlscript
let x: Int = 42
fun f(x: Int): Str = String(x)
val v: Option[Int] = Some(1)
```


### Spreads

Argument and array spreads follow the JavaScript iteration protocol:
`value[Symbol.iterator]().next().value`. Arrays, strings, native collections,
and user iterables use the same resolution path. Precise tuple spreads
retain their fixed positions.


### Resolution

The resolution pass of the compiler finds targets for names, members, and calls, and catches some obvious mistakes.
It does so by taking into account the declared types of values and parameters
and by tracking the flow of values through the current compilation unit,
stopping at the unit's exposed public interface (to support separate and scalable compilation).
This pass is mandatory and affects the program's runtime behavior,
unlike type checking, which is optional.

**Resolution is a best-effort process, not a replacement for type checking.**
Successful resolution does not establish type safety, even in strict mode.
Type checking is meant to run as a later pass, but is not yet implemented.

Resolution is "loose" and "lenient" by default: while it rejects unresolved references,
it allows references that are ambiguous (see: loose) and uncertain (see: lenient).
Optionally, one can enable
* **strict** resolution, under which all references must be resolved to exactly one source target.
  For example, `(xs: (List | Str)) => xs.length` is rejected:
  while `List` and `Str` both have a `length` member,
  and while that member could be selected dynamically under, eg, JS compilation,
  the two members are unrelated, so the access could not be compiled directly
  with more static backends like WASM.
  On the other hand, `(xs: (Cons | Nil)) => xs.length` works,
  provided that `Cons` and `Nil` are both subtypes of a common abstract class `List` that declares `length`.
* **eager** resolution: unlike lenient resolution, it does not discard receiver shapes that do not have the selected member.
  This moves resolution a bit closer to type checking, but still does not guarantee type safety.
  Resolution is lenient by default because it is quite approximate,
  so it will often get spurious candidate receivers that are only present due to its approximate tracking of flow.

Strict resolution is currently required by backends like WASM,
although smarter compilation strategies could allow more lenient resolution in the future
(an ambiguous selection can often be compiled into a match with unambiguous selections in its branches).

`@annotations.jsSymbol(path)` gives a public method a source name for the JavaScript property
key denoted by `path`. The path must consist of modules and immutable `val`s,
and end in a `val` annotated with `@annotations.fresh`. This marker is a contract
that the val owns a unique symbol; the resolver does not prove freshness.

```mlscript
module Keys {
  @fresh val read = Symbol("read")
}
class Reader {
  @jsSymbol(Keys.read) fun read() = 42
}
```

The method is stored at `Keys.read`, and both `reader.read()` and
`reader.(Keys.read)()` select that property. An override must retain both the
inherited source name and the same key. Giving an inherited key a different
source name is a collision, as is defining two methods with the same key in one
class. Distinct receiver paths are significant for fresh instance fields.

Currently, selecting a member on an escaped instance is unsupported when the
caller cannot access its local key: the compiler needs a runtime witness for
that particular key. Resolution diagnoses such accesses at the use site before
constructing a reference to the unavailable key. Closures that capture the key
remain valid, as do keys available through an imported file, including its
private file-level vals. The key must not be hoisted and shared between factory
invocations. `slop/JsSymbol.mls` records these cases.

A key path that accesses a private member of a class or module in another file
is rejected at the selection site. Such members use private accessor symbols
local to their defining file; they do not use the file-level private export ABI.

Compilation files check that their exposed functions and values do not make a closed-world assumption. A public `fun read(x) = x.a` needs an interface for
`x` even if local callers all provide `{a: 1}`. A private helper can use local
inference, but returning it or storing it in an exposed record or tuple makes its
interface subject to the same check. Callable result annotations provide the
declared parameter interface when checking returned functions.

Generic parameters remain opaque regardless of strict mode, visibility, or local
callers. For example, `private fun read[A](x: A) = x.a` is invalid because `A`
does not supply member `a`, even when every call supplies a record with that field.
Explicit and inferred type arguments still substitute into result interfaces:
an identity function with parameter and result type `A` preserves its caller's type.

### Dynamic Values

JavaScript imports (including package imports), `globalThis`, and explicit dynamic
selection or instantiation introduce dynamic values. Ordinary selections and
calls on those values are checked at runtime and produce dynamic values.
Use `value as dyn` for an explicit dynamic result or `fun useValue(x: dyn)`
for a dynamic parameter. Type aliases can also denote `dyn`; dynamic construction
uses `new!`.

These rules apply in both strict and non-strict resolution. A value whose interface
is unknown is not automatically dynamic. If inference includes both a dynamic
candidate and a known candidate with an invalid operation, the known error is
still reported. Dynamic values also do not remove the need for an unambiguous
class or type identity in constructor patterns, class projections, or type references.

### Generic Type Parameters

Covariant, contravariant, invariant:
```mlscript
class Container[out A]     // covariant
class Consumer[in A]       // contravariant
class Ref[A]               // invariant
```

Bounded type parameters:
```mlscript
fun f[A <: Num](x: A): A = x
```

Under new resolution, supplying a type argument affects both inputs and outputs.
For an invariant `Array[A]`, supplying `Int` means that lower bounds of `A` are
checked against `Int`, and upper bounds must accept `Int`. Passing an ordinary
integer value to `x: A` instead contributes only a lower bound; it does not fix
all uses of `A` to `Int`.

Use-site type arguments have input and output parts:

| Argument | Input | Output |
| --- | --- | --- |
| `S` | `S` | `S` |
| `in T` | `T` | `Any` |
| `out U` | `Nothing` | `U` |
| `in T out U` | `T` | `U` |

For an unqualified argument, the declaration's `in` or `out` annotation selects
the corresponding form. An explicitly written use-site variance supplies its own
parts. Substitution selects the output part in positive positions and the input
part in negative positions. Function inputs and type-argument input parts reverse
polarity; results and type-argument output parts preserve it. An invariant argument
must be interpreted in both polarities before substitution selects its bounds.
For example, a method input `Box[T]` on `Receiver[in Child out Base]` becomes
`Box[in Base out Child]` when `Box` is invariant. Declaration-site `in` reverses
polarity just like a written input part; declaration-site `out` preserves it.

Each explicit generic parameter is instantiated once at the expression that
specializes or invokes its definition: `f[T]`, a by-name reference/selection, or
otherwise the first term application. Stored specializations and later curried
argument lists share that instantiation. A by-name reference invokes its body even
without parentheses, so later uses of its result share any state it created.
An ordinary reference to a function with parameter lists can retain its generic
scheme until specialization or invocation.

Missing parameter/result annotations use inference. Omitted generic arguments
likewise count as inference holes rather than anonymous generic parameters; written
parts continue to restrict the interface. Currently an omitted argument inside a
shared annotation or alias can mix inferred types from different callers. These
annotations therefore do not always preserve the precision of a wholly unannotated
parameter. Concrete type-mismatch diagnostics are also incomplete during the
new-resolution migration.

Type-argument inference approximates a union in an expected type by propagating
constraints into every component. An intersection in an actual type contributes
each component separately: `L1 & L2 <: R` installs both `L1 <: R` and `L2 <: R`.
Resolution uses these approximations to collect member targets without searching
alternative constraint sets. Ordinary member
lookup still combines the fields of record intersections.

### Structural Record Types

```mlscript
type Point = { x: Num, y: Num }
```

Under new resolution, recursive type aliases must be guarded: every recursive
cycle must pass through a record, tuple, function arrow, or nominal type.
`type Loop = Loop` and `type Choice[A] = A | Choice[A]` are rejected, even when
unused. Alias applications follow the guards in the alias body: a wrapper defined
as `type Wrap[A] = {next: A}` permits `type Loop = Wrap[Loop]`.

Recursive structural types must also have a finite graph representation of their
unfolding. The current check conservatively rejects constructor-bearing cycles
between used type parameters, after alias and union/intersection normalization.
For example:

```mlscript
type Chain[A] = {value: A, next: Chain[A]}
type Reset[A] = {value: A, next: Reset[Array[Int]]}
type Saturating[A] = {value: A, next: Saturating[A | Int]}
type Growing[A] = {value: A, next: Growing[Array[A]]}
```

The first three are supported. `Growing[Int]` would expose `Int`, `Array[Int]`,
`Array[Array[Int]]`, and so on, and is rejected. The check also rejects some finite
types whose regularity depends on variance or relationships between recursive
arguments. Its diagnostic indicates a limitation of the current check.

### Function Types

```mlscript
type Transformer[A, B] = A -> B
type BinOp[A] = (A, A) -> A
type Callback = (Int, Int?) -> Int              // optional parameter
type Labeled = (x: Int, y?: Int) -> Int         // named parameters
type Step = (Int, drop Int) -> Int              // droppable parameter
type Join = (Str, ...Array[Str], Str) -> Str    // variadic parameter
```

Function type parameters follow the rules of
[optional](#optional-parameters), [variadic](#variadic-parameters), and [droppable](#droppable-parameters)
function parameters. Parameter names in function types are labels only: they do not affect compatibility.

A function passed where a function type is expected must accept the arguments that the type passes:
- it may leave out trailing droppable parameters, including a droppable variadic parameter,
  but no other parameters;
- it may not require an argument that the type marks as optional;
- its additional parameters must be optional, and are then `undefined`;
- it may collect several arguments in a variadic parameter.

```mlscript
fun app(f: (Int, Int?) -> Int) = f(1)
app((x, y?) => x)        // ok
app((x, y) => x)         // error: `y` is required, but its argument may be omitted
app(x => x)              // error: the optional parameter is not droppable
```

A separate signature, as in `fun f: (Int, Int?) -> Int` followed by `fun f(x, y?) = x`,
must agree with the definition on which parameters are required, optional, and variadic.

### `forall` (Universal Quantification)

```mlscript
fun id: forall 'a: 'a -> 'a
```

### `declare` Types and Classes

Declare external (JavaScript) types without providing an implementation:

```mlscript
declare type Any
declare type Nothing
declare class Error
declare class Array[T]
declare module Math with
  fun abs: Num -> Num
  val PI: Num
declare fun parseInt(str: Str, radix: Int): Int
```

---

## 15. Modules, Imports, and Namespaces

### Importing Files

```mlscript
import "./Option.mls"
import "./Stack.mls"
import "../../mlscript-compile/Iter.mls"
```

### Opening Modules

Bring module members into scope:

```mlscript
open Option
open Stack { Cons, Nil }           // selective open
open Iter                          // open all members
do open M; ...                     // locally open
```

With `newResolution` enabled, wildcard opens are consulted only when a name has
no explicit binding in the current scope or any enclosing scope. Explicit
bindings include local variables, parameters, member definitions, imports, and
selective opens such as `open Stack { Cons, Nil }`. An inner wildcard open does
not shadow an explicit binding in an outer scope. Moving a wildcard open before
or after an explicit binding does not give it priority over that binding.

For example, inside the function below, `x` refers to the explicitly bound `x`,
even though `M` also provides a member named `x`:

```mlscript
val x = 1
module M { val x = 2; val y = 3 }
fun example() =
  open M
  x + y                            // explicit x; y from M
```

When no explicit binding exists, lookup considers the wildcard opens visible at
that occurrence. These rules apply to the name itself, before choosing its term,
class, or pattern interpretation, so an explicit binding also takes precedence
over an overloaded class or function supplied by a wildcard open.

If wildcard lookup finds several distinct members with the requested name, the
reference is ambiguous; the order of the opens does not choose a winner.

### `open M in` Scope

```mlscript
M.{expr}                     // evaluate expr with M in scope
M.{foo Foo::m()}             // member projection in module scope
```

### Module Declarations

```mlscript
declare module q with
  val x
  fun f: Int -> Int
```

### Member Projections (`::`)

Unbound method reference (like `Class.method` in other languages):

```mlscript
Foo::method                  // unbound method reference
Foo::method(instance, args)  // call with explicit receiver
instance Foo::method(args)   // receiver-first syntax
instance.Foo#method()        // hash syntax (inside open scope)
```

### `open annotations { compile }`

Open the `annotations` module to use the `@compile` annotation in patterns:

```mlscript
open annotations { compile }
fun foo(x) = if x is @compile Box then "yes" else "no"
```

---

## 16. Flow Inference and Leading Dot Access

Flow types (`:flow` mode) enable type inference with a structural/flow-sensitive type system.

### Leading Dot Access (Flow Values)

In flow mode, a leading dot creates a *flow value* that resolves its type from context:

```mlscript
:flow

class A with
  fun b = new A

module A with
  fun a = new A

fun f(x: A) = x

f(.a)            // .a resolves to A.a because f expects A
f(.a.b)          // chains: A.a then .b
f(.a.c(1).b)
```

This allows passing module values implicitly when the expected type is known.

---

## 17. Indentation and Block Syntax

MLscript uses indentation to delimit blocks. Rules:

### Indented Block After Expression

An indented continuation after an expression is parsed as part of that expression:

```mlscript
fun foo(x) =
  x + 1           // body of foo

class Foo with
  val x = 1       // field of Foo
  fun f() = x     // method of Foo
```

### Explicit Blocks with `{}`

```mlscript
fun foo(x) = { x + 1 }
class Foo with { val x = 1; fun f() = x }
```

### Keyword Stutters — Multiple Definitions

```mlscript
let
  x = 1
  y = 2

fun
  min(x, y) = if x < y then x else y
  max(x, y) = if x > y then x else y

@inline
fun
  min(x, y) = if x < y then x else y
  max(x, y) = if x > y then x else y

object
  A extends Foo
  B extends Foo

abstract
  class Foo(a)
  class Bar(b)
```

### Operator Continuations

See [Newline Operator Rules](#newline-operator-rules) for the spacing distinction between continuations and new prefix expressions.

```mlscript
2
  + 2             // = 4
```

### Dot Selections on New Lines

```mlscript
[1, 2, 3]
  .map \ _ + 1
  .filter \ _ > 1
```

### `|. ` for piping the first argument

```mlscript
42
  |. inc()          // inc(42)
  |. inc()          // inc(inc(42))

// parses as
((42
  |. inc)()
  |. inc)()
```

### Parenthesis Matching

Closing parenthesis must match the indentation of the opening:

```mlscript
print(
  "A"
)               // OK

print of
  (
    "A"
  )             // OK

print of
  (
    "A"
)               // PARSE ERROR: mismatched closing indent
```

---

## 18. Miscellaneous

### Assertions

```mlscript
assert true
assert xs is Array
```

Adding an `else` clause to `assert` allows a form of early exit (from the enclosing syntactic block):
```mlscript
assert arg is [l, r] else arg

fun foo(x) =
  assert x is Some(value) else None
  // ...
  Some(x + 1)
// equivalent to:
fun foo(x) =
  if x is Some(value) then
    // ...
    Some(x + 1)
  else
    None

fun bar(x) =
  ...
  while ... do
    assert x is Some(value) else return None
  ...
```

### Drop / Do

```mlscript
drop expr           // evaluate and discard the result
do expr             // execute unit-returning expression as a statement
```

### Throw

```mlscript
throw Error("message")
throw new TypeError("bad type")
```

The `(??)` operator from Predef:
```mlscript
(??) "Not implemented"    // throws Error("Not implemented: ...")
```

### Dynamic Instantiation

```mlscript
new! c              // instantiate class value c at runtime
```

### Identifier Escaping

Escape keywords or non-standard identifiers using `id"..."`:

```mlscript
id"fun"             // the identifier `fun` (escaped keyword)
id"with"            // the identifier `with`
```

This is used for interop (e.g., `xs.id"with"(...)` calls the JS method `.with(...)`).

### `set` Inside Pattern Matching

```mlscript
set r.field = v
set xs.[0] = v
set x += 1
```

### Annotations

Annotations start with `@` and precede a definition:

```mlscript
@tailrec fun fact_n(n, acc) = ...
@inline fun f(x) = ...
@Freezed(-273.15) class AbsoluteZero
@inline let x = 0
@Test 1 + 2          // @Test annotates (1 + 2), not 1
```

Multiple annotations:
```mlscript
@inline @tailrec fun fib(n) = ...
```

Annotations on blocks:
```mlscript
@inline
fun
  min(x, y) = if x < y then x else y
  max(x, y) = if x > y then x else y
```

Currently, most user-defined annotations have no effect (they produce a warning). The built-in `@compile` annotation for patterns is meaningful.

### The `forall`/`virtual`/`abstract` Modifiers

```mlscript
virtual fun area: Num            // must be overridden
abstract class Shape             // cannot be instantiated
```

### `open ... in ...` (Explicit Selections)

```mlscript
M.{expr}                 // evaluate expr with M's members in scope
```

### Cyclic Value Definitions

Mutually recursive values are supported at the top level (the runtime handles initialization order).

### `source` module

Access current source location at compile time:

```mlscript
source.line
source.name
source.file
```

### The `js` module

Low-level JavaScript operations:
```mlscript
js.bitand(a, b)
js.bitor(a, b)
js.shl(a, b)
js.try_catch(f)
```

---

## 19. Built-in Types and Prelude

### Primitive Types

| Type | Description |
|---|---|
| `Bool` | Boolean (`true` / `false`) |
| `Int` | Integer |
| `Num` | Floating-point number |
| `Str` | String |
| `Any` | Top type |
| `Nothing` | Bottom type |
| `untyped` | Escape hatch for untyped values |

### Standard Classes

| Class | Description |
|---|---|
| `Array[T]` | Mutable array |
| `Set[V]` | Set |
| `Map[K, V]` | Map |
| `Error`, `TypeError`, `RangeError` | Errors |
| `Object` | Base object |
| `Function` | Function |
| `String` | String constructor |
| `Number` | Number constructor |
| `RegExp` | Regular expression |
| `Date` | Date |
| `Promise` | Promise |

### Math Module

```mlscript
Math.PI
Math.abs(x)
Math.floor(x)
Math.ceil(x)
Math.sqrt(x)
Math.pow(x, y)
Math.min(x, y)
Math.max(x, y)
Math.random()
Math.log(x)
Math.sin(x); Math.cos(x); Math.tan(x)
```

### Predef Functions

Imported automatically when `open Predef` is used (or when `import "./Predef.mls"` is present):

```mlscript
fun id(x) = x
fun print(...xs) = ...          // prints with rendering
fun tuple(...xs) = xs           // creates array from args
fun mkSet(...xs) = new Set(xs)

// Equality
fun (==) equals(a, b): Bool     // deep structural equality
fun (!=) nequals(a, b): Bool

// Function composition
fun (>>) andThen(f, g)(x) = g(f(x))
fun (<<) compose(f, g)(x) = f(g(x))

// Pipe operators
fun (|>) pipeInto(x, f) = f(x)
fun (<|) pipeFrom(f, x) = f(x)
fun (!>) tap(x, f) = f(x); x
fun (>>=) bind(x, f) = ...  // not in Predef but common pattern

// Context
fun use[T](using instance: T) = instance

// Errors
fun (??) notImplemented(msg) = throw Error("Not implemented: " + msg)

// Effect handler entry
fun enterHandleBlock(handler, body) = ...
```

### List (Stack) Module

```mlscript
import "./Stack.mls"
open Stack

type Stack[A] = Cons[A] | Nil
data class (::) Cons[A](head: A, tail: Stack[A])
object Nil

// Constructing:
1 :: 2 :: 3 :: Nil              // Cons(1, Cons(2, Cons(3, Nil)))

// Functions:
Stack.isEmpty(xs)
Stack.reverse(xs)
Stack.fromArray(arr)
Stack.toArray(xs)
Stack.filter(xs, f)
Stack.zip(xs, ys)
xs ::: ys                       // concat
xs :+ y                         // append single element
```

### Option Module

```mlscript
import "./Option.mls"
open Option { Some, None }

type Option[A] = Some[A] | None
data class Some[T](value)
object None

Option.isDefined(x)
Option.getOrElse(opt, default)
Option.flatMap(opt, f)
Option.unsafe.get(opt)
```

### Iter Module

```mlscript
import "./Iter.mls"
open Iter

class Iterable(mk)           // wraps an iterator-factory
class Iterator(next)         // wraps a next-function

xs mapping(f)                // lazy map
xs filtering(pred)           // lazy filter
xs toArray()                 // force to array
xs toStack()                 // force to Stack

// Fluent/receiver style:
[1, 2, 3]
  \Iter.mapping(x => x + 1)
  \Iter.toStack()
```

### StrOps Module

```mlscript
import "./StrOps.mls"
open StrOps

(~) concat2(a, b)            // string concat with ~ operator
concat(...xs)                // join multiple strings
from(value)                  // convert to string
parenthesizedIf(x, cond)     // wrap in parens if cond
```

---

## 20. Compiler Debugging

The compiler can report what it does in each of its phases, and show the intermediate programs it produces.
This is configured in the source code, either for a whole file with the `#dbg` directive,
or for individual definitions with the `@dbg` annotation.
The output is meant for compiler developers: its format is not stable and may change at any time.

### Debugging Aspects

Each argument of `#dbg` or `@dbg` enables or disables one *aspect*.
The following aspects trace a phase of the compiler:

| Aspect | Traces |
|---|---|
| `elaboration` | elaboration of syntax trees into terms |
| `lowering` | lowering of terms into the intermediate representation (IR) |
| `optimizations` | the optimization passes run on the IR |

With the new name resolution (`#lang(0.3.x)`), names are resolved during elaboration,
so `elaboration` traces name resolution as well.

Parser tracing is available through the diff-test command `:dp`.
Source directives are read after parsing and cannot enable parser tracing.

The following aspects display a program representation, without tracing:

| Aspect | Displays |
|---|---|
| `showParsedTree` | the syntax tree produced by the parser |
| `showElaboratedTree` | the elaborated term, as a tree |
| `showElaboratedTerm` | the elaborated term, in readable form |
| `showLoweredTree` | the IR produced by lowering, as a tree |
| `showIR` | the IR produced by lowering, in readable form |
| `showOptimizedIR` | the IR after optimizations, in readable form |

Finally, `showUids` (enabled by default) controls whether traces show the unique identifiers of symbols.
Disabling it makes traces easier to compare across compiler runs.
UIDs are local to a compilation unit, so imported symbols use disambiguated names without numeric UIDs.

### Syntax

An aspect is enabled by writing its name as a quoted identifier,
or enabled or disabled by giving it a Boolean value:

```mlscript
#dbg('lowering)                         // enable an aspect
#dbg(elaboration: true, showIR: true)   // enable aspects explicitly
#dbg(showUids: false)                   // disable an aspect
```

Unknown aspects and non-Boolean values are reported as errors.

### Output Destination

Debugging output is written to the standard output by default, which `out: StdIO` selects explicitly.
The `out: File(...)` argument writes it to a file instead:

```mlscript
#dbg('lowering, out: File("lowering.log"))
```

As for imports, a relative `File` path is resolved against the directory of the file
in which the `#dbg` directive or `@dbg` annotation is written, and an absolute path is used as is.
The first time the compiler writes to a file during a compilation session, it replaces the file's previous contents;
it then appends all later output, including the output of other files compiled in the same session,
such as imported files.
Output from concurrent compilations to the same file may be interleaved.

Any other destination is reported as an error.

### The `#dbg` Directive

The `#dbg` directive configures debugging for the file in which it appears, and must appear at its top level:

```mlscript
#dbg('elaboration, 'showOptimizedIR, out: File("debug.log"))

fun f(x) = x + 1
```

Several `#dbg` directives may set different aspects.
Currently, debugging settings apply to the whole file regardless of where the directive appears,
so if several directives set the same aspect, the last one takes effect.

### The `@dbg` Annotation

The `@dbg` annotation takes the same arguments as `#dbg`,
but only applies them to the definition it annotates.
It can annotate functions, methods, values, classes, modules, and objects:

```mlscript
@dbg('elaboration, 'showIR, showUids: false)
fun selected(x) = x + 1

fun unrelated(x) = x   // not traced, not displayed
```

Annotations combine with the file's settings:
for example, `@dbg(lowering: false)` stops a lowering trace enabled by `#dbg` for the annotated definition.
They also apply to the definitions nested in the annotated definition,
which can override them with their own `@dbg` annotations:

```mlscript
@dbg('lowering, out: File("lowering.log"))
fun traced() =
  fun helper() = 1                        // traced to lowering.log
  @dbg(lowering: false) fun muted() = 2   // not traced
  helper() + muted()
```

The statements that follow an annotated definition are not affected by its annotation.
The lowering trace of an annotated class also covers the evaluation of its superclass, if any,
and its companion module, if any, which is compiled together with the class.

The `optimizations` aspect cannot be selected per definition, as optimization passes process whole files.
Setting it in `@dbg` produces a warning and has no effect; use `#dbg` instead.

Currently, the destination selected by an enclosing `@dbg` annotation only applies to traces:
the displays requested by the annotation of a nested definition use the file's destination.

---

## Appendix: Grammar Summary

```
program   ::= stmt*
stmt      ::= def | expr | import | open
def       ::= val_def | fun_def | class_def | obj_def | mod_def | type_def | pattern_def | decl
val_def   ::= ['mut'] 'val' name ['=' expr]
fun_def   ::= 'fun' [annot] ['(' op ')'] name params* [':' type] '=' expr
class_def ::= ['abstract'|'data'] 'class' name typarams? params* ['extends' ...] ['with' block]
obj_def   ::= 'object' name ['extends' ...] ['with' block]
mod_def   ::= 'module' name ['with' block | '...']
type_def  ::= 'type' name typarams? '=' type
pattern   ::= 'pattern' name '=' pat ['=> expr']
decl      ::= 'declare' def

expr      ::= literal | name | app | lambda | if | case | while
            | let | set | 'return' | 'throw' | 'drop' | 'do'
            | 'new' [mut] class args | 'handle' | 'using'
            | annotation expr | prefix | infix | block

if        ::= 'if' scrutinee? branches
branches  ::= branch+
branch    ::= pattern ('then'|'do') expr

case      ::= 'case' branches
while     ::= 'while' cond_branches 'do' body

pattern   ::= '_' | literal | name | ctor_pat | tuple_pat | record_pat
            | pat '&' pat | pat '|' pat | pat 'as' name | pat 'where' expr
```

---

*This reference is derived from the MLscript (hkmc2) test files. For the most up-to-date information, see the test files in `hkmc2/shared/src/test/mlscript/`.*
