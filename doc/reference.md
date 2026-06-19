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

### Multi-Body `fun`

Multiple functions can be defined under a single `fun` keyword:

```mlscript
fun
  min(x, y) = if x < y then x else y
  max(x, y) = if x > y then x else y
```

### Recursive Functions

Functions are recursive by default:
```mlscript
fun fact(n) =
  if n <= 1 then 1 else n * fact(n - 1)
```

Mutual recursion uses sequential `fun` definitions in the same block.

### Lambdas

```mlscript
x => x + 1
(x, y) => x + y
() => 42
```

**Underscore lambda shorthand** — each `_` becomes a new anonymous parameter (left to right):
```mlscript
_ + 1            // x => x + 1
_ + _            // (x, y) => x + y
_.f(0, _, 2)     // (x, y) => x.f(0, y, 2)
```

**Lambdas in block position:**
```mlscript
{_ + 1}          // x => x + 1
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

**Block as function argument** (using `@`):
```mlscript
test @ {_ + 1}      // passes lambda {_ + 1} to test
test @              // indented block as arg
  _ + 1
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

### Operator Precedence

Operator sections with `_`:
```mlscript
(_ + 1)           // right section: x => x + 1
(1 + _)           // left section:  y => 1 + y
```

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

An operator at the start of a new line continues the previous expression:
```mlscript
2
  + 2       // = 4

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

### Multiple `object`/`module` Declarations Under One Keyword

```mlscript
object
  A extends Foo
  B extends Foo
```

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

---

## 10. Arrays

```mlscript
[1, 2, 3]            // array literal
mut [1, 2, 3]        // mutable array

xs.[0]               // index access (uses .at() internally)
xs.(0)               // dynamic index access
set xs.[0] = v       // index assignment
```

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

### Structural Record Types

```mlscript
type Point = { x: Num, y: Num }
```

### Function Types

```mlscript
type Transformer[A, B] = A -> B
type BinOp[A] = (A, A) -> A
```

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

### Operator on New Line = Continuation

```mlscript
2
  + 2             // = 4
```

### Dot Selections on New Lines

```mlscript
[1, 2, 3]
  .map(_ + 1)
  .filter(_ > 1)
```

### Backslash `\` at Start of Line

```mlscript
42
  \inc()          // inc(42)
  \inc()          // inc(inc(42))
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
            | annotation expr | infix | block

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
