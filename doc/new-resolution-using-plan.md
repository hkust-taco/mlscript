NOTE: This is an implementation plan (a working document), not reference documentation.
Once the work lands, its user-facing rules belong in `reference.md` and its implementation
invariants in `new-resolution-design.md`; this file should then be deleted.


# Contextual `using` parameters under new resolution

## 0. Status

| Part | Status |
| --- | --- |
| Decisions D1–D4 (§2) | Confirmed by the user. |
| Language rules in §3.1–§3.7 | Approved by the user, including the extensions and deviations in §3.9. |
| Derived instances (§3.8) | Approved by the user, including the `using fun` syntax and the divergence check. |
| Provider heads, parameter-query consultation keys, and recursive instance agreement (§3.1, §3.3, §3.8) | Confirmed by the user. |
| Contextual lambda literals and direct lambda calls (§3.1) | Revised by the user, superseding the earlier Scala-style rule. No value holds an uncompleted contextual function: a contextual lambda is completed where it is written, with a warning that suggests a `fun` definition. Function types with `using` lists are rejected; contextual function types are future work. |
| Deferred completion edges (Codex's §4.2 proposal of the Phase 2 checkpoint) | Rejected: the restored invariant (§3.1) makes them unnecessary (§4.2). |

Line numbers in this document are approximate; search by the function names given.


## 1. Goal

New resolution (`#lang(0.3.x)`, diff tests starting with `:.`) currently ignores `using` parameter
clauses: no contextual argument is inserted, so `make(3)` in `newres/LexerMigration.mls` evaluates
to a function. The legacy resolver (`Resolver.scala`, `ICtx`) supports them with a scoped
instance environment and an ad hoc type comparison. This work adds contextual-argument resolution
to new resolution with a different design:

- candidates come from lexically visible instances and from the **implicit namespaces** of the
  queried type, reusing the implicit-namespace machinery of PR #582;
- matching is type-based but simple: it compares type heads and checks the **shape flows** of
  type-argument positions, without type inference, backtracking, or specificity-based disambiguation;
- instances are resolved at the end of the block's elaboration, in source order, together with
  the settlement of references without explicit bindings (`settleUnboundReferences`);
- it supports type classes, including **derived instances** (Phase 6).

Non-goals:
- changing the legacy resolver or the behavior of `0.2.x` files and legacy diff tests;
- instance selection based on inferred types, specificity, or trial and backtracking;
- contextual (implicit) function types, as in `fun foo(arg: (using Int) -> Int)`, which would
  let callers pass contextual functions as arguments. They may be added later, with a mechanism
  that is unrelated to the completion of sites; this plan only rejects them (§3.1).


## 2. Confirmed decisions

- **D1. Lexical instances first, with shadowing.** Instances bound by enclosing `using` parameters
  and by `using T = e` declarations (visible from the end of the declaration onward) are
  candidates. Inner scopes and later declarations shadow outer and earlier ones. Implicit
  namespaces are consulted only if no lexical candidate matches.
- **D2. Namespaces provide `using` members.** A `using T = e` or `using T as name = e` declaration
  in a module or object body becomes a member of that module or object. Only such declarations are
  instance candidates; ordinary `val`s and objects of a matching type are not.
- **D3. Matching requires every flow to be compatible.** A candidate argument `S` matches a query
  position `T` if and only if every value reaching `T`'s position may be a value of `S`. If no value
  reaches the position, every `S` matches it. Values that arrive after selection and that `S` does not
  accept are errors.
- **D4. Derived instances are in scope.** Instances with their own type parameters and `using`
  clauses are supported, with the syntax of §3.8.


## 3. Language rules (new resolution only)

### 3.1 Contextual sites

A **contextual site** is a point where a callee value is consumed. There are two kinds:

1. **Value sites.** These are expressions in a value position: a term, a selection receiver, an
   argument, a result, a scrutinee, or a spread operand. The expression must be one of:
   - a reference, a selection, a leading-dot selection, or a `super` reference;
   - a contextual lambda literal (see below);
   - an application, type application, or `new` instantiation whose head is (recursively) one of
     these or a lambda literal.

   It must not itself be the head of an application or a type application.
   - In `M.f[Int](1)(2)`, only the outermost application is a value site.
   - In `M.f.g`, the receiver `M.f` is a value site.
   - A lambda literal whose parameter list is a `using` list is a *contextual lambda*. In a value
     position, it is itself a value site, so it is completed where it is written, like any other
     contextual callee.
     - With `using Int = 7`, `let get = (using n: Int) => n` binds `get` to `7`, not to a function.
     - Such a lambda is therefore useless, and the compiler warns about it (§3.7). A reusable
       contextual function is a `fun` definition: `fun get(using n: Int) = n`.
   - Direct lambda calls follow the same rules as named calls; the lambda is then an application
     head. With `using Int = 7`:
     - `((using n: Int) => (x: Int) => n + x)(3)` evaluates to `10`;
     - `((x: Int) => (using n: Int) => x + n)(3)` evaluates to `10`, because the inner contextual
       lambda is a value site in the outer lambda's body;
     - `((using n: Int) => n)(using 9)` evaluates to `9`.

     Every contextual lambda in these examples gets the same warning.
2. **Application heads.** These are the heads of applications whose argument list is written with
   ordinary parentheses (not `using`). In `f(1)`, `f` is an application head; in `f(using x)`,
   `f` is not.

A site **completes** every callee that flow reveals at it. A callee is a function definition, a
contextual lambda, a method, or a class constructor. Flow can reveal it at the site in any way,
for example:

- a reference;
- a member selected through a receiver whose class flow determines;
- several targets of one selection, such as overrides, which must share a calling convention
  (see below).

Only explicitly dynamic accesses (`!`, `.[…]`, dynamic receivers) are exempt. Callees can become
known incrementally, so a site completes each callee as it arrives (§3.6).

For each callee, consider its parameter lists that remain after the explicitly applied ones.
Explicit `using` lists, written `f(using a)`, count as applied.

- **Supply.** If the next remaining list is a `using` list, resolve instances for it and supply them.
  Repeat for each following `using` list.
- **Abstract (eta-expansion; value sites only).** This applies when the next remaining list is an
  ordinary list and some later list is a `using` list:
  - abstract over the ordinary list, as the legacy resolver does (`let f1 = foo` with
    `fun foo()(using Int)` yields `() => foo()(i)`), and continue with the following lists;
  - resolve every instance at the site;
  - the callee is applied once the expansion receives its last ordinary list.
- **Application heads.** An application head only supplies the leading `using` lists. The written
  ordinary list then applies to the next ordinary list (§3.9, X1).
- Otherwise, the value flows on unchanged.

**Calling conventions.** The *contextual calling convention* of a callable is, for each of its
parameter lists in order, whether the list is a `using` list, together with the number of
parameters of each `using` list.

- **Rule.** All the members that one reference or selection resolves to must have the same
  convention. This holds for every reference, whether or not anything is supplied there, because
  lowering emits one calling sequence for all of its targets.
- **Examples.** `x.foo` where `x` can be an `A` or a `B`, but only `A.foo` has a `using` list, is
  rejected. So is a site whose callees disagree on their `using` clauses.
- **Overrides.** Overrides already agree, because `OverrideLayout` rejects overrides that do not
  preserve contextual parameter lists. Unrelated members with the same name can disagree.
- **Reporting.** The mismatch is reported once, at the reference, as soon as its second
  incompatible target is recorded. It does not wait for settlement.

**Several callees.** A site is lowered once, so it supplies the same argument lists to all of its
callees. Each callee's queries are resolved separately, in that callee's own call activation.

- **Same convention.** All callees at a site have the same contextual calling convention (see
  above), so they have the same Supply and Abstract steps.
- **Same selection.** For each supplied parameter, every callee's query must select the same
  candidate. For an instance function (§3.8), agreement includes the function and, recursively,
  the candidates selected for all its nested `using` arguments. A later callee is checked against
  the earlier selections at every level; none of those selections changes.
  For example, queries `Show[List[Int]]` and `Show[List[Str]]` can select the same `list` instance
  function but different element instances. That is a selection mismatch: one generated argument
  cannot supply both constructions merely because their outer function is the same.
- **Errors.** A convention mismatch, a selection mismatch, or a contextual callee together with a
  dynamic callee at the same site is an error.

**Invariant: no value holds an uncompleted contextual function.** Every value site completes the
callees that flow reveals there, and contextual lambdas are value sites themselves. So a callee
whose next remaining list is a `using` list never flows out of a value site:

- variables, fields, parameters, tuple and record elements, and function results never hold
  one;
- a value that reaches a site through a variable, a parameter, or a generic type parameter is
  never a contextual callee, so passing it through needs no completion.

The implementation relies on this invariant and asserts it (§4.2). Contextual callees reach sites
only through references and selections that denote a definition, and through contextual lambda
literals. This includes a member selected through a receiver whose class only some activation
reveals, such as `x.m` with `x: A`: that selection is itself the site, and §3.6 governs callees
that reach it late.

There are no contextual function types, so a contextual function cannot be passed as an argument.
A `using` parameter list in a function type, such as `fun foo(arg: (using Int) -> Int)`, is an
error (§3.7). Contextual function types may be added later, with a different mechanism (§1).

### 3.2 Queries

Each parameter of a supplied `using` list is a **query**. The **query type** `Q` is the parameter's
type annotation, interpreted at the site: the callee's type parameters denote the instances of the
site's call, including explicit type arguments (`use[Int]`). After expanding aliases, `Q` is one
of the following:

- a **named query** `N[Q1, …, Qn]` (`n ≥ 0`), where `N` is a class, object, or class-like
  primitive. This includes type parameters that are bound by explicit type arguments to named
  types: `use[Int]` queries `Int`;
- a **parameter query**: a type parameter that has no explicit type argument;
- anything else (unions, intersections, functions, records, tuples, literal types): this is an
  error, "Contextual parameter types must be named types or type parameters".

Instance declarations (`using T = e`) are restricted the same way: `T` must be a named type
(the legacy `using Int -> Int` and `using 42` cases become errors).

The queries of a site are decided **one at a time**: clause by clause, and left to right within a
clause. Each selected argument is published into its parameter before the next query is decided,
so earlier selections can determine later queries. For example, with
`fun foo[A](using Foo[A], A)` and the only `Foo` instance being `Foo[Baz]`, selecting `Foo[Baz]`
makes `Baz` flow into `A`, so the second query has a candidate.

### 3.3 Candidates

**Lexical candidates** (D1) are visible from the site. They are ordered in **tiers** from the
innermost tier outward:

- each `using` declaration in an enclosing block (statement sequence, module, object, or class
  body) is its own tier. It is visible from the end of its declaration to the end of the block,
  and later declarations come first;
- the `using` parameters of one parameter clause form one tier. This covers enclosing functions,
  methods, lambdas, and class constructors; class `using` parameters are visible in the class body
  and in its methods;
- inner scopes come before outer scopes.

**Namespace candidates** (D2) form one final tier. They are found as follows:

- **Instance members.** In new resolution, a `using` declaration directly in a module or object
  body becomes a member of it:
  - `using T as name = e` is an ordinary member named `name`;
  - anonymous `using T = e` gets a deterministic synthesized name that source code cannot write.
    It replaces the legacy `instance$<tree.toString>` hack, which stays for `0.2.x`.

  Accessibility follows the member's visibility (`private using …`) through `visibleFrom`, as for
  name lookups. `using` declarations in class bodies and in other blocks are lexical only.
- **Which namespaces.** These are the implicit namespaces of `Q`, computed by the existing
  `typeNamespaces` walk (aliases as written, companion, then the declaring module, then parents or
  alias bodies, under the first-provider rule), with one extension for instance queries:
  - a named query also consults the namespaces of its type arguments, recursively. For a written
    argument, these are its type's namespaces; for an argument whose type is a type parameter,
    they are the namespaces of the values reaching it, as `valueNamespaces` computes them
    ("If `T` is of the form `List[S]`, also look into the implicit namespace of `S`");
  - a parameter query consults the namespaces of the values reaching the parameter.
- **"Provides" (first-provider rule).** For a named query `N[Q1, …, Qn]`, a namespace provides
  when it declares an accessible instance whose head, after alias expansion, is `N` or a subclass
  of `N`. This includes an instance-function result type (§3.8). For example, a `Foo` companion
  containing only `using IntFoo = …`, where `IntFoo extends Foo[Int]`, provides for `Foo[Int]`.
  Argument compatibility does not determine whether a namespace provides: an instance with a
  qualifying head still cuts off the walk when its arguments do not match the query.
  For a parameter query, a namespace provides when it declares an accessible instance whose head
  is the class or alias that named this namespace.
- **Consultation keys.** A provider decision depends only on declarations for the given query
  and triggering class or alias, never on the values at query positions. A named query decides
  once per namespace. A parameter query decides once per **(namespace, triggering class or
  alias)** pair, because different definitions can name the same declaring module. For example,
  if `M` declares `A`, `B extends A`, and an instance of `A`, consulting `M` through `B` finds no
  provider, but consulting it through parent `A` finds that instance. The first negative answer
  must not suppress the second consultation. Both use the same cached instance-member index of
  `M`. Name requests retain their existing per-namespace consultation and behavior.

### 3.4 Matching (D3)

A candidate has a **candidate type** `C`:

- for a lexical `using` parameter, its annotation;
- for a `using T = e` declaration, `T`;
- for an instance function, its result type, with the function's own type parameters left free (§3.8).

The candidate **matches** under these rules:

- **Named query** `N[Q1…Qn]`: after alias expansion, `C`'s class is `N` or a subclass of `N`.
  Let `C1…Cn` be the arguments of `N` as `C` sees them through its inheritance chain: for
  `class IntFoo extends Foo[Int]`, a candidate of type `IntFoo` has the arguments `[Int]` for the
  query head `Foo`. Then each `Ci` must *accept the values at* `Qi`'s position. A superclass
  candidate does not match: a `Semigroup[Int]` is not a `Monoid[Int]`.
- **Parameter query**: `C` accepts the values reaching the parameter. If no value reaches it, the
  query is **undetermined** and is an error. It does not match vacuously, because a vacuous match
  would select an arbitrary instance of any type, such as the latest declared one. The legacy
  resolver reports this case as "Illegal query for an unspecified type variable".

`S` **accepts the values at a position** when every value `v` observed there, in every activation,
**may be a value of** `S`. With no values, `S` accepts (vacuously). "May be a value of" is defined
as follows:

- `S` is `Any`/top, or a type parameter of an enclosing definition: yes.
- `v`'s class is unknown: yes. This covers unknown, dynamic, opaque, and erroneous values,
  namespace probes, and the values of type parameters (`RigidTypeShape`).
- `S` has head class `H`: `v` must be a nominal instance, a declared-type instance view, or a
  primitive literal of `H` or of a subclass of `H`. Then `S`'s arguments must recursively accept
  the values at `v`'s corresponding type-argument positions, as far as `v`'s view exposes them
  (for example, `NominalInstanceView.bindings`). Where it exposes none, the arguments accept.
- `S` is a union: some component accepts. `S` is an intersection: every component accepts.
- Other forms (functions, records, tuples): yes for now; record this with a `:todo` test.

Matching never ranks candidates. If a subclass candidate and a head-class candidate both match
in the same tier, that is an ambiguity (§3.5).

**Generic bodies need no special rule; shadowing (D1) handles them.** Consider
`fun sum[A](xs: List[A])(using Monoid[A]) = fold(xs)`. The lexical `Monoid[A]` matches the query
of `fold`, because its argument `A` accepts every value. It is in an inner tier, so it shadows
every namespace instance.

Without a lexical instance, as in `fun total[A](xs: List[A]) = fold(xs)`, the position values are
`A`'s values. These include the values of `total`'s callers, which flow into its body as they do
for member resolution. So a namespace instance `Monoid[Int]` can be selected while every caller
passes `Int`s. A later caller passing `Str`s then causes a late-value error (§3.6).

### 3.5 Selection

Tiers are tried in order. The first tier with at least one matching candidate decides:

- exactly one match: it is **selected**;
- several matches: **ambiguity** error, listing them.

If no tier matches, it is a **missing-instance** error. Shadowing (D1) applies only among matching
candidates. For example, a later `using Bar[Str]` does not hide an earlier `using Bar[Int]` from a
query whose position only receives `Int` values (`ctx/TrickyResolution.mls`).

The selected candidate's value is supplied as the argument:

- a lexical candidate: a reference to it, exactly as if written at the site, with the same
  `Capture`s;
- a namespace candidate: a selection of the member through `AccessPath.valuePath` from the site's
  scope;
- an instance function: an application of it (§3.8).

### 3.6 Timing and order

- Sites are recorded during elaboration in **post-order**: a site is recorded when its term is
  complete, after the references and sites it contains. An application head is recorded
  immediately before the site of its application. Sites share **one ordered worklist** with the
  references without explicit bindings. Do not sort by source location.
- `settleUnboundReferences` processes the worklist in order, before interface exposure and block
  completion (`Elaborator.topLevel`, `Elaborator.importFrom`):
  - a reference falls back to its wildcard opens, as today;
  - a site decides its pending queries.

  Both kinds of entries propagate synchronously before the next entry is processed. Diagnostics of
  unbound references stay in the existing second pass.
- Until its decision, a site delivers no completed value for a contextual callable. Ordinary values
  reaching the site flow on immediately.
- After the decision:
  - **Activations.** The same decision applies to every later delivery of the same callable in other
    activations, such as a generic body instantiated by a later call; these must not be decided
    again.
  - **Late callees.** A callee can reach a site after the site's turn but before block completion.
    If the site has decided nothing yet, it decides at arrival. Otherwise, the new callee's queries
    are checked against the existing selections (§3.1, several callees), which never change.
    Completed blocks cannot gain new targets.
  - **Late values.** A value that reaches a decided query position and that the selected candidate
    does not accept is an error. The selection never changes.
  - **Late namespaces.** A namespace revealed after the decision that provides a candidate which
    would match in the namespace tier is reported, as `lateNamespace` does for names, but only when
    the decision came from the namespace tier or found nothing.

### 3.7 Diagnostics

All diagnostics are user-facing: use source names and locations, never debug output (AGENTS.md).
Suggested messages:

- *Missing*: "No instance found for contextual parameter 'm' of type Monoid[Int]."
  - "The contextual parameter is declared here." (pointing at the parameter)
  - Up to a few rejected candidates with the same head, each with the value that it does not
    accept: "This instance of type Monoid[Str] does not accept this value of type parameter 'T'."
  - The consulted namespaces that provide nothing, phrased as in `settleUnboundReferences`.
- *Ambiguous*: "Ambiguous instances for contextual parameter 'x' of type Foo[T]." Each candidate
  is listed with its location and its origin (lexical, or `Module` namespace).
- *Undetermined*: "Cannot determine the type of contextual parameter 'instance': type parameter
  'T' has no explicit type argument and no value reaches it."
- *Unsupported query or declaration type*: see §3.2.
- *Contextual lambda* (warning, at the lambda's `using` parameter list): "This lambda's contextual
  parameters are supplied where it is written, so it never produces a contextual function." A
  note suggests the alternative: "Use a 'fun' definition to define a contextual function." The
  warning applies to every lambda literal whose parameter list is a `using` list, including
  directly applied ones. It is new-resolution only.
- *Contextual function type* (error, at the `using` list): "Function types cannot have 'using'
  parameter lists." If the parser or the elaborator already rejects this syntax, keep the existing
  error and add a test.
- *Calling-convention mismatch*: "This reference resolves to members with different contextual
  parameter lists." Each member is listed with its parameter lists' declaration. Use the same
  message for the callees of a site.
- *Callee selection mismatch*: "The callees of this call require different instances for
  contextual parameter 'm'." Each callee's selection is listed. For derived instances, identify
  the differing nested selections and the instance functions that require them.
- *Dynamic callee*: "Contextual arguments cannot be supplied to a dynamically accessed callee
  together with these contextual callees."
- *Late value*: "This value reaches the type of contextual parameter 'm' after its instance was
  selected; the selected instance of type Monoid[Int] does not accept it."
- *Late namespace*: modeled on `lateNamespace`.
- *Divergence* (Phase 6): see §3.8.

### 3.8 Derived instances (Phase 6). Status: **approved**

A `using` modifier on `fun` declares an **instance function**.

```mlscript
abstract class Show[A] with
  fun show(x: A): Str
module Show with
  object ShowInt extends Show[Int] with
    fun show(x) = x.toString()
  using Show[Int] = ShowInt
  class ShowList[A](elem: Show[A]) extends Show[List[A]] with
    fun show(xs) = "[" + xs.map(elem.show).join(", ") + "]"
  using fun list[A](using elem: Show[A]): Show[List[A]] = ShowList(elem)

fun display[A](x: A)(using s: Show[A]) = s.show(x)
display(List(1, 2)) // supplies Show.list(using Show.ShowInt)
```

Rules:

- **Form.** `using fun name[A…](using …)…: R = body`:
  - a name is required;
  - a result annotation `R` is required, and it must be a named type;
  - every parameter list must be a `using` list (there may be none);
  - type parameters are allowed.

  It appears wherever `using T = e` can: as a namespace member of a module or object, or lexically
  in a block. The parser most likely already produces `TermDef(Ins, TermDef(Fun, …))` here; check
  this, and reject the other `using <definition>` forms.
- **Matching.** It is a candidate with candidate type `R`. Its own type parameters accept every value.
- **Selection.** Selecting it does the following:
  1. instantiates it at a synthesized call site inside the enclosing site;
  2. feeds each value at the query's position `Qi` into the corresponding position of `R`, through
     the ordinary type-argument inference used for arguments (`inferTypeArguments`), which binds the
     function's type parameters. For example, the elements of the `List` values bind `A`;
  3. resolves the function's `using` lists as **nested queries** of the same site, with the same
     scope and rules. They are decided depth-first, before the next query of the enclosing site;
  4. supplies the application's result as the argument.
- **Several callees.** Apply §3.1's agreement rule recursively to the selected function and its
  nested arguments. Each callee uses its own query bindings; equality of the outer function
  alone does not establish agreement on the generated argument.
- **Divergence.** An instance function is not a match for a nested query for which it would
  diverge (see below). There is no depth limit.

**Divergence check.** This follows Scala 3's check (`checkDivergence` in
`compiler/src/dotty/tools/dotc/typer/Implicits.scala`), which differs from Scala 2's in three ways:

- it compares a query only with the earlier queries that use the *same candidate*, whereas Scala 2's
  specification compares it with the types of all open implicit searches;
- it records the size and covering set of each open search's type when the search opens. Without
  this, nested searches that instantiate type variables would make earlier entries grow and mask
  divergence;
- a divergent candidate is an ordinary failed candidate, rather than an error that aborts the
  whole search.

Scala's query types are concrete: their arguments are inferred types. Our query positions are
determined by flow, so the check uses the type that the values at each position exhibit.

- **Observed type.** The *observed type* of a set of values is the union of the observed types of
  its values, or the wildcard `?` if the set is empty or contains a value of unknown class.
  - The observed type of a value of class `C` is `C` applied to the observed types of the values
    at its type-argument positions, as far as its view exposes them, and `?` for the others.
  - When the computation reaches a value that is already on its current path, that value
    contributes `?`, so observed types are finite even for cyclic flows.
- **Flow type.** The *flow type* of a query is its query type, in which each position is replaced
  by the observed type of the values at it. A written position such as `List[Int]` is observed
  through its instance views, so it reads `List[Int]`.
  - The flow type is computed when the query is decided, and it is not updated afterwards, as
    Scala 3 caches open search types.
  - Its *size* is its number of class and `?` occurrences. Its *covering set* is the set of
    classes that occur in it.
  - Flow types are compared structurally, with unions treated as sets and `?` equal to `?`. This
    corresponds to Scala's comparison of types after wildcard approximation.
- **Derivation path.** The derivation path of a nested query consists of the queries above it in
  the same derivation, from the site's root query down. Each has its flow type and the instance
  function selected for it.
- **Rule.** An instance function `f` *diverges* for a nested query `q` when some query `q'` on
  `q`'s derivation path selected `f`, has the same covering set as `q`, and either is smaller
  than `q` or has an equal flow type. When `f` diverges, it does not match `q`.

  Selection then proceeds among the remaining matches (§3.5). This is still no backtracking: the
  check filters candidates before selection, and a decided query never changes. In particular,
  when a nested query has no remaining match, it is a missing-instance error for the site.
  Scala 3 would instead try another candidate for the enclosing query. That missing-instance
  error adds a note for each candidate excluded by divergence, with the derivation path,
  outermost first: each query's flow type and the instance function selected for it.

Examples, with a namespace instance for `Show[Int]`:

- `list` on values of observed type `List[List[Int]]`: the queries are `Show[List[List[Int]]]`
  (size 4), then `Show[List[Int]]` (size 3), then `Show[Int]`. The sizes shrink, so this does not
  diverge.
- `using fun loop[A](using Show[A]): Show[A]` on `Int` values: its nested query `Show[Int]` has the
  flow type of the query that selected `loop`, so `loop` diverges. The `Show[Int]` instance is
  selected instead.
- `using fun bad[A](using Show[List[A]]): Show[A]` on `Int` values:
  - the queries are `Show[Int]`, then `Show[List[Int]]`. Their covering sets differ, so `bad`
    can be selected again;
  - the next query is `Show[List[List[Int]]]`, which has the same covering set as
    `Show[List[Int]]` and is larger, so `bad` diverges there. No other candidate matches, so this
    is a missing-instance error.
- A pair instance that swaps its arguments, on `Pair[Int, Str]` values, repeats the root's flow
  type after two steps and then diverges.
- An instance for `class Rose(kids: List[Rose])` that requires `Show[List[Rose]]` cycles through
  `Show[Rose]` with an equal flow type and diverges. Scala 3 can tie such recursive knots with
  by-name implicit parameters; supporting that would be a separate extension.

**Termination.** There are finitely many classes and instance functions, so there are finitely
many pairs of an instance function and a covering set. Along a derivation path, the queries that
share such a pair have non-increasing sizes and pairwise distinct flow types. For a fixed size and
covering set, there are finitely many flow types. So every derivation path is finite. Document
this argument in the implementation.

### 3.9 Extensions and deviations from the legacy resolver

- **X1.** Leading `using` lists are supplied at application heads: `f(1)` with
  `fun f(using Int)(x: Int)`. The legacy resolver mis-applies the written list to the `using` list.
- **X2.** Queries that involve type parameters are resolved through flows. Several legacy `:todo`
  cases, such as `ctx/CascadingTypeClasses.mls` and `ctx/TrickyResolution.mls`, are expected to
  succeed.
- **X3.** Ambiguity is an error within a tier: the parameters of one clause, or the namespace tier.
  This includes a subclass candidate together with a head-class candidate, because nothing ranks
  candidates by specificity. The legacy resolver picked the first match.
- **X4.** Eta-expansion evaluates the site's operands (receiver and explicit arguments) **once, at
  the site**, in source order. The legacy resolver re-evaluated the whole reference on each call of
  the expansion. When lowering binds a receiver, it must keep method receivers bound: never
  produce a debound method value.
- **X5.** Unsupported query and declaration types are errors. The legacy resolver crashed with
  "not-yet implemented type".
- **X6.** Instances in modules and objects are members (D2). The legacy resolver never makes
  instances members.
- **X7.** The value-compatibility consequence of D3 applies to positions. With `T := Int`,
  `Monoid[Num]` matches `Monoid[T]` if `Int` values are `Num` values, so in the same tier it is
  ambiguous with `Monoid[Int]`. At the top level, the candidate's class must be the query head or a
  subclass of it (§3.4).
- **X8.** Every callee that flow reveals is completed (§3.1), including members selected through
  flow-typed receivers and several overriding targets. The legacy resolver only completes callees
  whose definitions it knows statically.
- **X9.** A contextual lambda is completed where it is written, with a warning (§3.1, §3.7). The
  legacy resolver never completes lambdas, so a contextual lambda there stays a function that only
  receives explicit arguments.


## 4. Architecture

These are recommendations. Deviate only with a stated reason in the commit message and an update
to this section. Escalate (see §7) if a principle in §3 cannot be met.

### 4.1 Elaborator

- **Instance members (D2).** Make `using` declarations owned by the enclosing module or object, in
  new resolution only: see the `if (k is Ins) then N else ctx.outer.inner` owner computation in the
  term-definition case of the elaborator's block processing. Synthesize anonymous names: see
  `Tree.scala` around `case typ if k == Ins` and search for how other synthesized members are
  named. Keep `0.2.x` unchanged.
  - **Implementation adjustment (Phase 1).** Allocate anonymous names in `BlockImpl`'s cached
    new-resolution binding table. `Tree.name` is read while parsing, before the language
    configuration is available, and its legacy names can group distinct anonymous declarations
    together. The new table gives each declaration its own symbol, while lexical and member
    name maps exclude those anonymous bindings. Escaped identifiers can spell any string, so
    merely choosing an unusual spelling would not enforce source inaccessibility. Blocks with
    no anonymous instances reuse their existing symbols; legacy binding tables stay unchanged.
    JavaScript stores public anonymous values in a per-namespace table under a symbol key.
    String properties would collide with inherited named or anonymous fields; the table gives
    anonymous declarations a distinct runtime binding space as well as a distinct source space.
- **Instance index.** Give each module or object definition a cached list of its instance members
  (declaration, candidate type, visibility). Namespace lookup must not scan bodies repeatedly.
  All queries and triggering classes or aliases reuse this one index per module or object.
- **Lexical instance environment.** `Ctx` carries a persistent (shared) list of tiers. The
  following push a tier:
  - a `using` parameter clause, when its body is elaborated: function, method, lambda, or class body;
  - each `using` declaration, for the statements after it.

  Each entry records the symbol and its candidate type annotation. The environment must not be
  copied per site: share the list.
- **Site roles.** Distinguish application heads from value positions in
  `Elaborator.Interpretation`. Today `applicationHead` returns `Trm`. Add a role or a flag, keeping
  `implicitNamespacing` unchanged for heads. Record value sites and application heads (§3.1) with
  their `SrcScope` and lexical instance environment, in the worklist order of §3.6.
- **Instance functions (Phase 6).** Elaborate `using fun` per §3.8.

### 4.2 Resolver

- **Phase 2 interception blocker (resolved).** The Phase 2 checkpoint's `listenContextual`
  expands each value with `listenInstanceViewsOrProbe` and forwards the resulting *view* even when
  the value requires no contextual arguments. Expanding `InstanceShape(A)` to its current views
  discards the reference to `A` before the caller's substitution reaches it, so a later
  substitution cannot recover it. This breaks programs without any `using` clause. A reduced
  excerpt of the failing imported-inference test:

  ```mlscript
  // Generic.mls, compiled first under new resolution
  module Generic with
    fun identity[A](x: A) = x

  // A separate importing file, also under new resolution
  import "./Generic.mls"
  class Item(val first: Int)
  Generic.identity(Item(1)).first
  ```

  - **Fix.** Use views only to classify a value; never forward a view in place of the value. A
    value that needs no completion is forwarded exactly as the site received it, with its marks,
    annotations, declared types, and pending substitutions. Only contextual callees are held for
    their completion.
  - **Why this is complete.** The checkpoint asked whether a later substitution could reveal a
    contextual callee in a value that a site already forwarded, leaving that site with a
    completion obligation. Under the invariant of §3.1, it cannot: no value holds an uncompleted
    contextual function, so a type parameter's values never include one. A contextual callee
    revealed only in some activation can only reach a site that *selects* it, for example `x.m`
    with `x: A`. That selection is itself the site, and the rules of §3.1 and §3.6 for several
    and late callees govern it. No obligation travels with values through bindings, returns,
    aggregates, captures, or imports.
  - **Assertions.** Assert the invariant with `softAssert`. Check that values published into
    variable, field, and parameter hosts and into completion outputs never have a leading `using`
    list. This is a check of the shape's remaining parameter lists, so it is cheap.
- **Rejected: deferred completion edges.** The checkpoint's proposal of a `Complete(site, input)`
  resolver graph operation, transported through generic flow, is not adopted. It is unnecessary
  under the invariant of §3.1. It would also have made a generic body's generated code depend on
  what its callers pass, and it would have treated local and imported generic functions
  differently, because imported code is frozen. Contextual lambdas are completed where they are
  written, so the proposal's `let saved = x` example cannot arise: `x` never holds a contextual
  lambda.
- **Interception.** The completion must apply however the site's value is consumed. Two existing
  paths need care:
  1. `listen` forwards `SymShape`s through compound terms: block results, labels, `try`, and
     annotations;
  2. `listenValue` converts symbol shapes into definition shapes (`fromSymbol`), at the
     *consumer*.

  Prefer materializing a site's values at the site itself, with the site's own role (`receiver`
  or not). Then forward each shape that needs no completion unchanged, as the site received it and
  never as one of its views (see the resolved blocker above). Hold the contextual callables,
  together with their delivering `ResolutionContext`, for settlement. Do not wrap
  every term: allocate per-site state only when a contextual callable first arrives.
  Centralize access to the remaining parameter lists, their contextual flags, and their
  instantiated annotations for both definition shapes and declared callable interfaces.
  `unappliedParams` (`Shape.scala`) and `ParamList.flags.ctx` cover definition shapes, but the
  current `unappliedParams` returns no lists for `CallableTypeShape`. Annotated member access can
  produce that shape, so preserve contextual-list metadata and the declaring definition through
  `DeclaredParams` / `CallableTypeShape` construction, instantiation, and partial application.
  Completion must use those declared interfaces without recovering hidden implementation flow.
- **Calling-convention check.** Compare the contextual calling convention (§3.1) of each target
  with the reference's existing targets when the target is recorded: `recordValueTarget`,
  `resolveThrough`, and the selection paths that append to `resolvedTargets` or `resolvedMembers`.
  Do the check in one helper that all these paths call. Report through
  `resolutionProblem`/`markError`, as other target conflicts are reported (compare
  `checkPrivateMix`). The check needs only declarations, so it applies to every reference, in
  every unit, independently of sites.
- **Several callees.** The per-site state holds:
  - the contextual calling convention, fixed by the first callee;
  - one `InstanceArg` per supplied parameter, shared by all callees.

  Decide callees in arrival order. The first callee's selection fills an `InstanceArg`; each later
  callee's query must select the same candidate (§3.1). For instance functions, retain the nested
  `InstanceArg`s and check agreement recursively under each callee's query bindings. Comparing
  only the outer instance-function symbol would miss incompatible nested arguments. Each callee
  is applied to the same synthesized flow sites, under its own activation, as an ordinary
  application receives several callee shapes.
- **Settlement.** Extend `settleUnboundReferences` to process the ordered worklist (§3.6). Rename
  it if its name becomes misleading, and update the doc comments that reference it.
- **Flow model of a completion.** Model each **Supply** step as a synthesized application flow site,
  as `iterationFlow` does: an `App(Term.Missing, CtxTup(args))` with recorded lexical binders,
  driven by `applyShape(raw, args, app, checked = true)`. This makes argument zipping, arity
  checking, parameter constraints, and type-argument inference reuse the ordinary application
  paths: `zipArgsIn` for definition shapes and `applyValue`'s declared-interface handling for
  `CallableTypeShape`.
  - The completed value the consumers receive is the shapes of the last step.
  - Model **Abstract** steps with a synthesized `Lam` whose body is the next step's flow site. The
    `Lam` is a flow model only; lowering does not lower it (§4.4).
  - An application head's Supply steps feed the enclosing application's head: that application's
    `applyShape` must receive the completed callable, not the raw one.
- **Instance arguments.** One argument term per query, a new resolver-synthesized term that stands
  for the instance selected for one contextual parameter. Suggested name: `Term.InstanceArg`.
  - It is a `ShapeHost`. Once a candidate is selected, it forwards the shapes of the selected
    argument expression (`var selected: Opt[Term]`).
  - Publishing as each query is decided lets later queries of the same clause observe earlier
    selections through the ordinary application paths (§3.2). Do not constrain parameters through
    a second path.
  - Handle it in `TermImpl` (describe, `subTerms` = the selected term, `show`, `showDbg`), `Cloner`,
    `resultFlow`, `listen`, Lowering, and the legacy `Resolver`, where it is unreachable.
- **Query construction.** Interpret the parameter's annotation in the site's call activation.
  Use the activation that `applyValue` computes for the step's flow site: `instantiateDefinition`
  and the captured substitution for definition shapes, or `instantiateCallable` and the
  instantiated `CallableTypeShape` annotations for declared interfaces. Then classify it per §3.2.
  - Observe the position values with `listenInstanceViews` and `listenTypeParameterValues` on the
    instantiated position types, in the base context, which observes the values of every
    activation. There is no activation-specific matching rule (§3.4).
  - Explicit type arguments are visible through `hasExplicitTypeArgument` and the bindings
    published by `bindTypeArguments`.
- **Lexical candidates.** Build the reference for a selected lexical candidate with the same code
  that elaborates a written reference, so that it carries the same `Capture`s. Refactor that code
  into a helper if needed; never duplicate it. Test references from nested functions, lambdas,
  methods, handlers, and `:lift`ed code.
- **Namespace candidates.** Generalize the implicit-namespace machinery over a **request**, with two
  implementations:
  1. the existing name request of an `UnresolvedRef`;
  2. an instance request, one per query.

  The functions to generalize are `ImplicitNamespaces`, `typeNamespaces`, `classNamespaces`,
  `valueNamespaces`, `ownNamespaces`, `firstProvider`, `consultNamespace`, and `lateNamespace`.
  The request decides what "provides" means (§3.3), its consultation key, what a candidate is,
  and how candidates are published. Name requests and named instance queries key consultation by
  module; parameter queries key it by module and triggering class or alias. A module-only key
  would reuse a negative provider decision for another definition that names the same namespace.
  Provider tests use the cached instance index and declaration heads, including subclasses for
  named queries, without testing argument flows.
  For an instance request, publishing means adding the candidate to the namespace tier of the
  query; deduplicate the same instance declaration reached through multiple consultations. For a
  name request, publishing is `resolveThrough`. The name request's behavior must stay identical:
  all `ImplicitNamespace*.mls` and `LeadingDotSelections.mls` outputs unchanged. Add the
  type-argument extension of §3.3 only for instance requests. Do not copy and adapt the walk.
- **Matching.** Implement "may be a value of" (§3.4) as one function, used both for decisions and
  for late-value checks.
- **Nested sites (Phase 6).** An instance-function argument is a synthesized application chain,
  driven like a site completion, with nested queries decided in place.
  - Share the selected argument chain across callees only when its function and all nested
    selections agree (§3.1). Retain the first selections and report any later mismatch.
  - Keep the derivation path as an explicit, immutable stack, passed down through the nested
    decisions. Do not store it in global mutable state.
  - Each stack entry holds the selected instance function and the query's flow type, together with
    its size and covering set. All three are computed once, when the query is decided (§3.8).
  - Represent flow types as small immutable terms over class symbols, unions, and the wildcard,
    computed from the observed values. They serve only the divergence check, and they are not
    `DeclaredType`s.
  - Apply the divergence check while matching a nested query's instance-function candidates,
    before selection.

### 4.3 Representation of completions

Store the completion on the site term in a mixin, like `keyAccess` (`TermImpl.NewResolvableImpl`),
for the term classes that can be sites: `App`, `TyApp`, `New`, `MemberRef`, `NewSel`,
`UnresolvedRef`, `Super`, `Lam` (a contextual lambda in a value position, or a lambda that is an
ordinary application head), and `Capture` when it is the outermost term.

- `SimpleRef` is not a site: under the invariant of §3.1, a variable never holds a contextual
  callee.
- Compound application heads need no completion either. In `(if c then f else g)(1)` or in a
  block returning a contextual lambda, the head's result expressions are value sites themselves.
- The Phase 2 checkpoint attached the mixin to every `Term` for these two reasons. Both are gone,
  so move it back to the classes above unless another reason remains. A field on every term
  breaks the per-term state budget of §4.6.

The pending metadata reuses the single worklist entry; an empty completion allocates no helper.
Anonymous candidate selections use declaration keys in the ordinary member-lookup path, sharing
its receiver transport and visibility checks without reintroducing anonymous source names.
The prototype also stores an output host beside the steps, which the consumers of a completed site
observe. Keep it, allocated only for sites that receive a contextual callee; block completion must
seal it with the synthesized applications. The completion has this shape:

```scala
final case class ContextualCompletion(steps: Ls[ContextualStep])
enum ContextualStep:
  /** Supply one `using` list; `application.rhs` is a `CtxTup` of `InstanceArg`s. */
  case Supply(application: Term.App)
  /** Abstract over an ordinary list of the callee (eta-expansion), with fresh parameters. */
  case Abstract(params: ParamList, application: Term.App)
```

- Include the completion's argument terms in `subTerms`, as `keyAccess` is included.
- Copy completions in `Cloner`, substituting symbols, as it does for `keyAccess`.
- `:rt` and `:e` outputs should show completions readably.

### 4.4 Lowering

Centralize the lowering of sites with completions:

- **Application chains.** When `collectAppChain` collects a chain, interleave the argument lists
  that its sites' completions supply with the written lists, in application order, and pass them
  to `lowerMultiCall`. This preserves method-call receivers: `Test.this.test(j)(tmp)`.
  - A bare reference with a completion becomes a call.
  - A `new` site appends its supplied lists to the instantiation's argument lists, in order.
- **Abstract steps.** Generate lambdas, as the builtin-reference case does with `setupFunctionDef`.
  The site's operands are evaluated once at the site and bound to temporaries (X4).

### 4.5 Unchanged parts

- The legacy resolver and its tests. They keep passing; do not port fixes into it.
- Name resolution of `UnresolvedRef`s, except for the shared worklist order.

### 4.6 Performance

- Programs that do not use `using` must allocate no new per-term state. The checkpoint's proposed
  relaxation of this requirement for deferred generic flow is withdrawn along with the deferred
  completion edges (§4.2).
- Recording a site is one buffer entry, like `accessSites`.
- Per-module instance indexes are cached. Within a query, provider decisions are bounded by the
  consulted modules for named queries, or by the (module, triggering class or alias) pairs for
  parameter queries (§3.3). Name-request consultation remains unchanged.
- Before finishing Phase 2 and Phase 3, compare time and allocated bytes against the base commit:
  - use `git worktree` checkouts in a scratch directory, `sbt -batch`, and the `ThreadMXBean`
    allocation counter;
  - run on the full diff-test suite, or on a large representative subset;
  - report the numbers in the commit message;
  - a regression above 2% must be explained or fixed.


## 5. Phases

Each phase ends with a full `hkmc2AllTests/test` run that passes, followed by a commit that
includes the golden outputs. Commits use the agent's own identity (AGENTS.md).

### Phase 1: test ports and elaboration groundwork

Implementation status: groundwork and test ports are complete. The contextual suite contains
the 14 ports below, seven new behavior files, and an import fixture under its own
`mlscript-compile/` directory, so `ctest` emits that fixture's JavaScript. Pending behavior uses
`:fixme`; missing expected diagnostics use `:breakme` because the harness does not allow their
absence under `:fixme`. Unrelated generic-override representation and handler-parent resolution
gaps remain explicit regressions. Performance comparisons are due at Phases 2 and 3.

- Create `hkmc2/shared/src/test/mlscript/slop/contextual/` with a `.mls` configuration that only
  contains `:..` (inheriting `slop/.mls`). Each test file starts with `:.`.
- Port the legacy tests in §6 into it, adapted to D1–D4. Expected values are written with
  `:expect`, and parts that are not yet implemented are marked `:fixme` or `:todo`.
- Add new tests for the namespace, matching, and timing rules (§6), marked the same way.
- Implement §4.1 except for instance functions: instance members, index, lexical environment, and
  site roles and recording. Existing outputs may change only where new-resolution modules or objects
  declare instances, which now become members; review each such diff.

### Phase 2: sites, lexical instances, and direct insertion

Checkpoint status (incomplete): the user requested committing the partial implementation while
the §4.2 blocker was under review. That blocker is now resolved (§4.2): resume Phase 2 with the
steps below, before the remaining Phase 2 items.

1. Forward each received shape unchanged when it needs no completion. Then confirm that the
   two import-isolation tests and the `LexicalCaptures` `:fixme` pass.
2. Make contextual lambdas value sites, with the warning, and add the function-type error (§3.1,
   §3.7). Rewrite `ContextualLambdas.mls` (§6).
3. Add the invariant assertions (§4.2).
4. Move the completion mixin back off `Term` (§4.3).

Direct lexical insertion, matching, callable-clause metadata,
agreement checks, and Supply lowering are prototyped; `FlowCallees.mls` and
`LexicalCaptures.mls` add coverage, and the contextual ports have updated golden outputs.
The checkpoint is not a completed phase and does not satisfy the phase exit criteria:

- `ctest`: 60 passed.
- `sdtest contextual`: 23 passed, 1 failed. `MatchingEdges.mls` still has the §3.4 `:todo`
  marker on structural compatibility, but its block now succeeds. The marker needs reconciliation
  with the harness's requirement that `:todo` blocks fail; this is separate from interception.
- `hkmc2AllTests/test`: stopped in the Scala.js tests at the two generic-import failures described
  in §4.2 (50 passed, 2 failed). Later aggregate stages did not run.
- Late-value diagnostics remain incomplete (for example `generic("later")` in `MatchingEdges`);
  diagnostic messages still need query types and clearer identification of unnamed parameters.
  Existing `:fixme` and `:breakme` cases also retain the later phases' pending behavior.
- Performance comparison has not run; it remains required before completing Phase 2.
- Phases 3–6 have not started. Namespace lookup has not been generalized.

- Implement interception, settlement, Supply steps, `InstanceArg`, query construction, matching,
  lexical candidates, completion storage, and lowering of Supply steps. This covers value sites,
  application heads (X1), class constructors, `new`, callees revealed through flow-typed receivers,
  declared callable interfaces, and sites with several callees (X8), including the agreement checks
  of §3.1 for direct instances.
- Report the errors of §3.7, except for late namespaces and divergence. This includes unsupported
  query/declaration types and late-value and late-callee checks for direct insertion; Phase 4
  extends their coverage to eta-expansion and generic-body cases.
- Exit when the lexical-only direct-insertion parts of the `TypeClasses`, `ExplicitlySpec`,
  `ClassCtxParams`, `NestedUsingInstances`, `Summon`, `ForwardTypeClassUses`, `BadTypeClasses`,
  `SymbolResolution`, and `Debugging` ports pass. `newres/LexerMigration.mls` must lose its `:fixme`.
  Cases requiring Abstract steps remain marked `:fixme` or `:todo` until Phase 4.

### Phase 3: namespace instances

- Generalize the namespace machinery (§4.2) without changing name behavior. Add the instance index
  lookups, the "provides" rule, type-argument namespaces, the namespace tier, and late namespaces.
- Add tests for:
  - type-class companions and data-type companions;
  - declaring modules;
  - the first-provider cutoff;
  - a namespace whose only instance has a subclass head, including an aliased annotation; it
    provides even when argument incompatibility later rejects the candidate;
  - a parameter query that consults one declaring module through multiple classes or aliases,
    including `B extends A` with only an `A` instance; a negative decision for `B` must not hide
    the provider for `A`, and repeated discovery of that instance must not cause ambiguity;
  - type-argument namespaces (`Show[List[Point]]` finds `Point`'s companion);
  - private instance members;
  - instances in imported files (`import` of a `slop/contextual` helper module, or of an existing
    `mlscript-compile` module);
  - ambiguity across namespaces;
  - late namespaces;
  - lexical instances shadowing namespace instances.

### Phase 4: eta-expansion, cascading, and late values

- Implement Abstract steps in flow and lowering (X4), complete the `EtaExpansion`, `Cascading`,
  and `Tricky` ports, and enable the eta-expansion cases deferred from the other ports in Phase 2.
- Extend coverage of the late-value, late-callee, and unsupported-type errors implemented in
  Phase 2 to eta-expansion and generic-body cases.
- Add generic-body tests (§3.4):
  - a lexical instance shadowing namespace instances inside a generic function whose callers
    pass types that have namespace instances;
  - a generic function without a lexical instance selecting a namespace instance through its
    callers' flows;
  - the late-value error that a later caller with an incompatible type causes.

### Phase 5: migration and documentation

- Try migrating `mlscript-compile/apps/parsing/Lexer.mls` to `#lang(0.3.x)`. If unrelated
  new-resolution gaps block the migration, leave the file as it is and record the blocker in
  `doc/new-resolution-suite-migration.md`; otherwise, remove the `parsing/Lexer` row there.
- Update the "Contextual calls" bullet of the migration document.
- Rewrite `doc/reference.md` §13 (Context Parameters) for new resolution, with the rules of §3,
  and link it from the Implicit Namespaces section.
- Add an "Contextual parameters" section to `doc/new-resolution-design.md` with the
  implementation invariants of §4.
- Keep this plan file until Phase 6 is done: it still specifies Phase 6.

### Phase 6: derived instances

- Parse and elaborate `using fun`. Implement instance-function candidates, nested queries, and
  the divergence check (§3.8), including recursive agreement across callees (§3.1).
- Add tests:
  - `Show[List[Int]]`;
  - `Show[List[List[Int]]]`, which needs two levels of the same instance function;
  - a missing element instance;
  - ambiguity between a derived and a direct instance in the same tier;
  - lexical instance functions;
  - imported instance functions;
  - several callees selecting the same instance function with recursively identical nested
    arguments (success);
  - several callees selecting the same instance function but different nested arguments (selection
    mismatch), including a mismatch below two levels of derivation and a callee arriving late;
  - divergence by equality with an alternative: `loop` from §3.8, where the `Show[Int]` instance is
    selected for the nested query;
  - divergence by equality without an alternative, which is a missing-instance error with the
    divergence note;
  - divergence by growth (`bad` from §3.8), detected at the second repetition;
  - a nested query that is larger than an earlier one but selects a different instance function,
    which is not divergent;
  - the pair instance that swaps its arguments (§3.8);
  - the recursive `Rose` instance (§3.8);
  - cyclic flows at a position, for which observed types cut cycles with `?`.
- Afterwards, move the derived-instance rules to `doc/reference.md` and the design notes, then
  delete this plan file.


## 6. Tests

Port the legacy tests below into `slop/contextual/<SameName>.mls`. Keep the legacy files untouched,
as they still test the legacy resolver. In each port, write the expected new-resolution behavior;
where it differs from the legacy expectation, add a short comment citing §3 or §3.9.

| Legacy file | Notes for the port |
| --- | --- |
| `ctx/TypeClasses.mls` | Port nearly verbatim (lexical declarations still work). `M.tFoo` keeps selecting the latest `Foo` instance (separate blocks are separate tiers). |
| `ctx/CascadingTypeClasses.mls` | The `:todo`s are expected to succeed (X2). The unconstrained `foo` cases become undetermined or ambiguous errors per §3.4. |
| `ctx/TrickyResolution.mls` | Expected to succeed: `Foo[Int]` wins, binds `A`, then `Bar[Int]` (§3.5). |
| `ctx/ClassCtxParams.mls` | Class constructors and class-body lexical instances. Leave the `x.Foo#S` FIXME case as `:todo` if it is unrelated. |
| `ctx/EtaExpansion.mls` | Phase 4. The IR changes (temporaries, X4) are expected. |
| `ctx/ExplicitlySpec.mls` | Explicit `using` arguments mixed with insertion and eta-expansion. |
| `ctx/ForwardTypeClassUses.mls` | Forward references to modules defined later in the block. |
| `ctx/NestedUsingInstances.mls` | Local blocks, objects, and modules; `:lift` with handlers. |
| `ctx/Summon.mls` | `use[T]`; `use[Num]` succeeds with `using Int = 42` because `Int extends Num` (§3.4); use an unrelated type for missing-instance coverage; keep the undetermined `f` case. |
| `ctx/SymbolResolution.mls` (using parts) | Moduleful results of contextual functions. |
| `basics/BadTypeClasses.mls` | Declaration errors (X5); the `M.foo()` `:breakme` case should now work (a value site supplies the trailing `using` list, §3.1). |
| `basics/CompanionModules_Classes.mls` (using part) | `bar` with a local `using Int` calling `Foo.foo`. |
| `basics/MultiParamListClasses.mls` (using part) | Constructors with `using` lists. |
| `handlers/Debugging.mls` (using part) | Instance bound to a handler. |

New tests (in `slop/contextual/`):

- **Namespace instances.** Type-class companion; data-type companion; declaring module;
  type-argument namespaces; first-provider cutoff; private members; imports; ambiguity; late
  namespace; lexical shadowing of namespaces. Include subclass-only providers (also through
  aliases), argument incompatibility that does not undo the cutoff, and parameter queries that
  consult the same module through different classes or aliases (§3.3, Phase 3).
- **Matching.**
  - Top-level subclass candidates (`using IntFoo = …` for `Foo[Int]`) match, using the arguments
    inherited from the query head.
  - A subclass candidate and a head-class candidate in the same tier are ambiguous (X3).
  - Superclass candidates do not match.
  - Positions receiving subclass instances.
  - Unknown or dynamic values.
  - Union position types.
  - Vacuous positions.
  - Undetermined parameter queries.
  - X7.
- **Timing.**
  - A site whose callee's module is defined later in the block.
  - A capitalized name settled before or after a site, both orders.
  - Two sites where the first selection reveals the second's namespace.
  - Late values from a later worksheet block.
- **Generic bodies** (Phase 4, see above).
- **Application heads (X1)** and `new` with `using` lists.
- **Contextual lambdas** (§3.1). Rewrite `ContextualLambdas.mls` for the revised rule, with
  the warning on each contextual lambda:
  - `let get = (using n: Int) => n`, with an `Int` instance in scope: `get` is the instance's
    value. Calling it is an error.
  - The same binding without an `Int` instance in scope: a missing-instance error at the lambda.
  - A contextual lambda passed as an argument is completed at the argument.
  - The direct calls of §3.1, including `((using n: Int) => n)(using 9)`.
  - The inner contextual lambda of `(x: Int) => (using n: Int) => x + n`, completed when the outer
    lambda's body runs, with the instance visible at the inner lambda.
  - A contextual lambda as the result of an `if` or a block in application-head position.
  - A function type with a `using` list (error).
- **Invariant and generic flow** (§4.2).
  - The imported `Generic.identity(Item(1)).first` case.
  - The existing import-isolation tests, unchanged.
  - The `LexicalCaptures` `use[Box[T]].value` case.
  - A completed value passed through a generic function, a local binding, a record field, and a
    returned closure.
  - `x.m` with `x: A`, where `m` has a `using` list and only callers' activations reveal it: an
    ordinary late callee of that selection (§3.6).
- **Flow-revealed callees (X8).**
  - A method with a `using` list selected through a parameter whose class only flow determines.
  - A method with a `using` list selected through an annotated receiver, exercising the
    `CallableTypeShape` interface, including explicit type arguments and partial applications.
  - Overriding targets that agree on the selected instance.
  - Overriding targets whose `using` annotations select different instances (selection
    mismatch error).
  - Several callees selecting the same instance function with equal or different nested arguments,
    including deeper derivations and late callees (Phase 6).
  - Targets with different contextual calling conventions: a selection on a receiver that can be
    one of two unrelated classes, only one of whose `foo` has a `using` list, or whose `using`
    lists have different lengths. It is an error both where an instance would be supplied and
    where nothing is supplied (for example, `x.foo(using a)`).
  - A callee revealed after the site's turn.
  - A contextual callee mixed with a dynamic access (error).

Do not add Scala unit tests duplicating these. A Scala test is justified only for a property
that diff tests cannot observe; state that property in the test.


## 7. Validation, commits, and escalation

- Run `ctest` first when running individual diff tests. Run `hkmc2AllTests/test` before every commit.
- Commit each phase separately with its golden outputs.
- Check the whole diff for accidental changes to empty lines and indentation.
- Do not push and do not open pull requests.
- **Stop and report**, instead of working around the problem, when:
  - a rule of §3 cannot be implemented without changing other language semantics;
  - interception (§4.2) cannot be made uniform across consumption paths;
  - the namespace generalization changes any name-resolution output;
  - the performance budget (§4.6) is exceeded without a clear fix;
  - an invariant you need cannot be checked. Use `softAssert` for invariants and `softTODO` for
    known temporary gaps; never silently skip a case.


## Appendix: code pointers

- `semantics/Elaborator.scala`:
  - `Interpretation` (~L547);
  - the instance owner (~L2697);
  - parameter lists with the `inUsing` flag (~L3396);
  - `importFrom` and `topLevel` (~L3697).
- `syntax/Tree.scala`: instance naming (~L642).
- `syntax/ParseRule.scala`: `Kw(using)(termDefBody(Ins))`.
- `semantics/NewResolver.scala`:
  - implicit namespaces: `unresolvedRef`, `resolveThrough`, `requireTypeNamespaces`,
    `valueNamespaces`, `typeNamespaces`, `classNamespaces`, `ownNamespaces`, `firstProvider`,
    `consultNamespace`, `lateNamespace`, `settleUnboundReferences`;
  - application flow: `applyShape`, `applyValue`, `zipArgsIn`, `constrainParameterIn`;
  - term flow: `listen`, `listenValue`, `fromSymbol`;
  - the synthesized-application precedent: `iterationFlow`;
  - type parameters: `registerTypeParameters` (rigid values), `bindTypeArguments`,
    `listenTypeParameterValues`, `inferTypeArguments`.
- `semantics/NewResolverState.scala`: `accessSites`, `unboundReferences`, `completeBlock`, and
  `ImplicitNamespaces` / `Namespace` / `NamespaceWitness`.
- `semantics/Shape.scala`: `unappliedParamLists` / `unappliedParams`, `AppShape`, `DefnShape`,
  `DeclaredParams`, `CallableTypeShape`, and `RigidTypeShape`.
- `semantics/TermImpl.scala`: `NewResolvableImpl.keyAccess` (the precedent for resolver-built
  terms) and `subTerms`.
- `codegen/Lowering.scala`: the `App` chain case (`collectAppChain`, `lowerMultiCall`) and the
  builtin-reference lambda (`setupFunctionDef`).
- `codegen/OverrideLayout.scala`: "must preserve contextual parameter lists".
- `semantics/Resolver.scala` (legacy): `ICtx` and the expansion logic in `resolve`, for reference
  only.
- `mlscript-compile/Predef.mls`: `fun use[T](using instance: T) = instance`.
