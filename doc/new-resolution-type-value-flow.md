# Instance types and parameter constraints

`InstanceShape(T)` describes an instance of the type `T`. Types remain in the
`TypeShape`/`DeclaredType` graph. The instance wrapper replaces the earlier
nominal-only representation at annotation boundaries: parameter and result
annotations, ascriptions, generic arguments, and annotated tuple fields retain
a type reference until an operation requests its interface.

The wrapper refactor is implemented. Instantiation of declared type parameters
once per definition and call site is the agreed direction. The integration with
marks and type constraints proposed below needs review before implementation;
bidirectional constraints and variance are also still pending.
See the [resolver notes](new-resolution-design.md)
for current behavior and the [migration worklist](new-resolution-suite-migration.md)
for remaining ports.

## Type arguments are different from instance bounds

Supplying `Int` as the type argument for a contextual parameter `A` affects both
positive and negative uses of `A`:

```text
A has the supplied type Int:

L <: A    requires    L <: Int
A <: U    requires    Int <: U
```

An ordinary integer argument to a parameter `x: A` contributes only a lower
bound. It does not supply `Int` as the meaning of every occurrence of `A`.
For `pair[A](x: A, y: A)`, an integer and a string therefore contribute two lower
bounds; neither argument must satisfy the other's type.

If two distinct type values, `Int` and `Str`, reach the same activation of `A`,
each bound must apply to both. `L <: A` requires both `L <: Int` and `L <: Str`;
`A <: U` requires both `Int <: U` and `Str <: U`. Supplying the single type value
`Int | Str` is different: its complete type expression remains the constraint
target. Decomposing a union in positive position does not justify decomposing it
conjunctively in negative position.

Concrete mismatches such as `Str <: Int` may remain quiet during this migration.
The absence of a loud diagnostic does not authorize dropping constraints before
they reach the relevant type or parameter.

These rules concern inputs/outputs, or equivalently lower/upper bounds. Function
parameters reverse polarity and function results preserve it. Array operations
are one application of the rules.

## Finite call-site instantiation and marks

**Instantiate each definition's explicitly declared type parameters once per
syntactic call site.** This includes binders in inline annotations and separate
type signatures, whether the call supplies type arguments or infers them. A call
`f(x)` therefore instantiates a declared `f[A]` just as `f[Int](x)` does.

Memoize a complete group of parameter symbols using this key:

```text
(original definition, syntactic application site)
    -> {original parameter -> instantiated parameter}
```

Different sites receive different symbols. Revisiting the same definition at the
same site reuses its group, including during recursion. The key must not contain
the supplied types, incoming bounds, marks, or an already instantiated definition.
Install the group before subscribing to constraints so reentrant propagation
finds it. The only permitted allocation resembling fresh inference variables is
this bounded instantiation; do not allocate another variable per flow, constraint
match, or recursive visit.

Symbols identify these instances; marks still identify the contexts in which
their bounds flow. A single call inside a helper shares its parameter instances
across the helper's callers, while enclosing marks distinguish those callers.
Keep the original lexical resolution boundaries and existing normalization;
instantiated symbols must not introduce additional scope boundaries. Mutable
array literals retain the builtin `Array` element parameter with allocation marks;
actual element shapes contribute bounds there. They need no fresh element variable.

Keeping a reference to an unresolved parameter is essential. Copying its current
positive candidates loses its negative uses and its identity as a type argument.
Subscriptions must also account for constraints or candidates arriving later.
Graph caches and listeners belong to the consuming `NewResolverState`; extending
a consumer must not mutate a prelude or an exporter's inference graph.

This follows the finite-allocation idea in §3 of
[Tate's type-outference paper](https://rosstate.org/publications/outference/outference-tate-oopsla25.pdf):
label listeners introduce signature unknowns once per invocation site and nominal
label, reusing them as bounds arrive rather than expanding every concrete type.
Here the proposed key uses the original definition and application site. The
paper's formal calculus has monomorphic methods; its termination result does not
directly establish termination for our generic functions and marks.

## Instance wrappers and interface observations

`InstanceShape` holds a `DeclaredType`, including its lexical bindings.
`listenTypeInstances` supplies this wrapper; `listenInstanceViews` interprets it
for an operation such as selection, application, or destructuring. The cached
`listenTypeViews` observations reuse the specialized nominal, callable, record,
and tuple interfaces. `NominalInstanceView` is the nominal member-lookup view
previously called `NominalTypeShape`.

For example, an instance viewed as `Base` exposes `Base`'s declarations even if
the implementation is a `Child`. Interpreting a function type exposes its declared
domain and result. Interpreting a union for member lookup can observe each
alternative, while transporting its wrapper preserves the original union node.

This refactor alone does not implement the planned distinction between supplying
a type argument and adding an ordinary bound. In particular, the current
`inferTypeArguments` still expands wrappers when inferring from an instance, and
explicit arguments still suppress ordinary refinement. The proposed constraint
work must replace these behaviors together.

## Variance rules to implement

Follow InvalML's argument interpretation in
[`typeAndSubstType`](../hkmc2/shared/src/main/scala/hkmc2/invalml/InvalML.scala)
and argument comparison in
[`constrainArgs`](../hkmc2/shared/src/main/scala/hkmc2/invalml/ConstraintSolver.scala).
Its [`TypeArg`](../hkmc2/shared/src/main/scala/hkmc2/invalml/types.scala) exposes an
input part (`negPart`) and an output part (`posPart`):

| Argument | Input part | Output part |
| --- | --- | --- |
| `S` | `S` | `S` |
| `in T` | `T` | `Any` |
| `out U` | `Nothing` | `U` |

Thus `S` means `in S out S`. The internal pair can also represent a written
`in T out U`. For an unqualified argument, a declaration's `in` or `out` annotation
selects the corresponding form. An explicitly written use-site wildcard supplies
its own parts, as it does in InvalML; it is not combined by guessing a variance.

For actual argument `a` and expected argument `b`, require:

```text
a.output <: b.output
b.input  <: a.input
```

A plain invariant `Array[Int]` against `Array[A]` therefore retains both uses of
the element type. `Array[out A]` admits only the output connection; `Array[in A]`
admits only the input connection. Substitution into member types must select the
appropriate part at each polarity, including nested arrows. Copy InvalML's
variance semantics, not its fresh inference-variable implementation.

## Why two independent candidate-copying edges are insufficient

An experimental implementation made `appendTyped` propagate elements into an
initially empty mutable array and passed the existing declaration worksheets.
However, this recursive example exposed an activation-correlation failure.
It is retained as a `:fixme` regression in
[`newres/MutableArrays.mls`](../hkmc2/shared/src/test/mlscript/newres/MutableArrays.mls)
(the recursive `append` block, immediately after `appendTyped`):

```mlscript
class Item(val value: Int)
fun append[A](xs: Array[A], value: A, n: Int) =
  if n > 0 then append(xs, value, n - 1) else xs.push(value)
let xs = mut []
append(xs, Item(5), 2)
xs.0.value
```

The experiment reported an unknown element type originating from the generic
body's abstract activation of `A`. That candidate must remain confined to that
abstract activation. The experimental bound-copying implementation is not part
of the retained compiler changes. On the committed resolver, the regression
currently fails earlier: `xs.0.value` has no resolved target because generic
array input propagation is still missing. Its expected result is `5`; the
current golden output does not reproduce the discarded prototype's unknown-type
diagnostic.

The failure comes from independently applying an existing capture path and its
reverse to already expanded candidates. Write `enter(f, s)` and `exit(f, s)` for
marks at function `f` and site `s`, and `*` for a capture that matches any site.
A candidate starting at `enter(f, abstract)` can travel as follows:

```text
forward:
  enter(f, abstract) -- exit(f, *) --> no mark
                    -- enter(f, recursiveCall) --> enter(f, recursiveCall)

independent reverse:
  enter(f, recursiveCall) -- exit(f, recursiveCall) --> no mark
                         -- enter(f, *) --> enter(f, *)
```

The reverse traversal has forgotten `abstract`. Its wildcard can then match a
real caller's exit. This demonstrates loss in the candidate-copying approach;
it does not establish that the existing mark representation itself is inadequate.
Discarding the abstract candidate, suppressing reverse propagation for recursion,
or truncating paths would conceal the loss rather than preserve the constraint.

## Proposed integration with the resolver

For the recursive example above there are three relevant versions of `A`:

```text
A_body       original binder used to check the generic definition
A_outer      instance for append(xs, Item(5), 2)
A_recursive  instance for append(xs, value, n - 1)
```

Further recursive visits reuse `A_recursive`; they do not create
`A_recursive_recursive`. A second external application gets its own instance of
`A`, but still reaches the same recursive application site. Its enclosing marks
must keep the two external contexts distinct. The original abstract candidate of
`A_body` must not be copied into the call instances: instantiate the declared
constraints, not the generic body's accumulated unknown-value candidates.

This replaces the earlier proposal to retain wildcard matches across paired
candidate-copying edges. It does not yet demonstrate that the recursive example
works: the compiler still needs consistent substitution of the call instances
through deferred type observations and body-result flow.

### Definition and application identities

Use the stable `Term.App.resSym` as application identity, rather than taking a
site from the callee's marks. Marks can identify a function reference shared by
several applications:

```mlscript
let g = append
g(xs, First(1), 2)
g(ys, Second(2), 2)
```

These applications need distinct parameter instances. The two-array regression
following the recursive `append` block in `newres/MutableArrays.mls` checks this
case with different element interfaces.

For construction, use `Term.New.resSym` and canonicalize the constructor and
class to the same original owner. For an anonymous polymorphic annotation, the
proposed owner is its original quantified declaration node. Neither imported
views nor instantiated callable views should manufacture a new original owner.

### Binder substitution before observation

Normalize binders from inline declarations and separate signatures into a
reusable scheme with its parameter bounds, declared type fragments, and links to
inference for unannotated parts. Do not require a complete signature. Currently,
`typeResolution` strips `Forall` to its body; that loses the information needed
to instantiate separate polymorphic signatures. Preserve the quantifiers first.

An instantiated callable must retain one immutable substitution from that
scheme's own binders to the site's parameter symbols. Use it for parameter
annotations, results, nested callback types, bounds, and type arguments before
`listenInstanceViews` expands a parameter. Enclosing class or function parameters
remain captures; they are not binders of the nested definition being instantiated.

Argument matching alone is insufficient. The generic body was elaborated using
the original binders, and a returned tuple or closure can defer observing an
annotated value until after the call. Carry the same substitution through those
deferred observations. Keep generic-body checking on the original abstract
activation; do not mutate the body or unconditionally connect its inference host
to each call instance. The representation of these substituted body-result views
is the main integration question to resolve before implementation.

### Partial signatures and inference holes

Instantiation applies to explicit type binders even when the rest of a definition
is only partially annotated. The recursive `append[A]` example already has an
inferred result. A more direct example mixes annotated and unannotated inputs:

```mlscript
private fun pair[A](x: A, y) = [x, y]
```

At an application site `s`, instantiate `A` as `A_s`. The annotation of `x`
becomes `InstanceShape(A_s)`. The unannotated `y` retains its existing value-flow
symbol and obtains argument shapes under the call's marks. Infer the result from
the body: its first field retains the reference to `A_s`, and its second field
retains the marked flow from `y`. Neither `y` nor the result needs an invented
quantified parameter or a fresh type variable at the call.

The substitution must survive delayed tuple-field observations. Likewise, in
`private fun apply[A](x: A, f) = f(x)`, the unannotated callback and its result
must remain connected to the contextual `A`. Both examples, called with distinct
element interfaces, currently pass in
[`newres/PartialSignatures.mls`](../hkmc2/shared/src/test/mlscript/newres/PartialSignatures.mls).
The instantiation refactor must preserve that behavior.

Represent a partial signature position by position:

| Part of the definition | Source of its interface at a call |
| --- | --- |
| Explicit type binder `A` | The memoized call-site instance `A_s` |
| Written type fragment | Its instance wrapper, using the call's substitution |
| Unannotated value parameter | Its existing inference host and marks |
| Unannotated result | The body's flow graph, retaining substitution and marks |
| Inferable hole within a type | A stable inference node for that source hole, under marks |

**Inferable holes use ordinary marked inference, not anonymous quantified
parameters.** This is the agreed semantics; hole syntax is not selected here.
For schematic `Array[?]`, retain the declared `Array` structure and connect its
element position to the hole's inferred flow. Reuse the source hole's node across
visits and distinguish contexts with marks. No call-site symbol copy is allocated
for the hole. Constraints follow the position's input/output polarity as usual.
If no useful shape reaches a hole, it supplies no member interface; it does not
grant dynamic access.

An inference hole must be distinguishable from an intentionally abstract type,
an `in`/`out` wildcard, and an unresolved or invalid annotation. These must not
all collapse to `TypeShape.Abstract`, which the current interpreter uses for
several unsupported forms. Inferring one missing piece must not add members to
an explicitly written concrete interface elsewhere in the annotation.

Whether omitted generic arguments also denote inferable holes is still a design
question. Current `DeclaredTypes.mls` tests treat missing arguments in annotations
such as `Pair[Int]` for `Pair[A, B]` as unknown interfaces. Similarly, an unknown
member type exposed through a nominal annotation is not automatically an
inference hole. Preserve those distinctions until their intended behavior is
decided; the agreement about explicit holes alone does not resolve them.

The scheme therefore cannot be a closed type synthesized from whatever shapes
happen to be available first. It must retain live links to inferred portions of
the definition, including bounds arriving later or through recursion. Existing
exposure checks for unannotated parameters and generic-body checking still apply;
partial annotations must not silently disable either.

### Partial application and explicit specialization

For curried calls, the proposed rule is to instantiate when the first parameter
list is consumed and retain that substitution in the partially applied callable.
Later lists reuse it. A separately quantified returned callable has its own
binders to instantiate at its later application. A standalone specialization such
as `let g = f[Int]` can retain its supplied type arguments until application;
each application of `g` then binds its own site instances to `Int`. This avoids
introducing a second allocation policy at type-application nodes.

### Constraint propagation and implementation order

1. Preserve partial declaration/signature schemes and their original identities,
   including links to inferred portions. Distinguish inference holes from
   intentionally abstract types and variance wildcards. Add a
   consumer-owned cache of complete call-site instances, with origin links back
   to the declared binders. Do not add mutable caches to symbols.
2. Transport the memoized substitution through callable and result views before
   expanding instance wrappers. Keep the existing marks for value flow and
   lexical captures. Verify the abstract generic-body candidate stays isolated.
3. Relate the resulting type references in both input and output positions,
   retaining their hosts, substitutions, and marks. Ordinary arguments contribute
   bounds; supplied types receive all obligations at their applicable polarity.
   Apply the InvalML variance rules above.
4. Replace `applyTypeArguments`, nominal inference, explicit-argument suppression,
   and the positive-only conversion in `instanceBindings` together. Reuse the
   same mechanism for functions, constructors, and declared array interfaces.

There are at most as many allocated parameter instances as the sum of each
reachable definition's binder count over its syntactic call sites. This bounds
symbol allocation, not every possible implementation of the solver. Recursive
constraints must return to shared nodes and deduplicated relations; expanding
substitution environments or nested types afresh could still fail to terminate.
Demonstrate fixed points with recursive and mutually recursive calls before
landing the propagation changes. Any needed change to mark normalization or to
the context domain must be proposed separately.

## Acceptance checks

- An initially empty mutable array receives an element through `Array[A]`.
- Two calls using different arrays and incompatible element interfaces remain
  independent, including two callers of the recursive example above.
- A repeated visit to the same definition/site reuses its parameter symbols;
  two application sites through one alias obtain distinct instances. An inner
  site shared by different enclosing activations remains distinguished by marks.
- Inline and separate polymorphic signatures instantiate consistently, with or
  without explicit call-site type arguments. Partial applications retain their
  substitutions and captured outer binders retain their original contexts.
- Mixed annotated/unannotated inputs and inferred results preserve the passing
  tuple and callback cases in `newres/PartialSignatures.mls`. Nested inference
  holes retain written structure and use marked inference without extra
  call-site symbols; known annotation fragments still restrict the interface.
- Recursive input/output relations terminate with bounded call-site instances,
  no repeated-boundary paths, and no unbounded binding-environment construction.
- Declaration-site `in`/`out`, use-site `in`/`out`, their overrides, and nested
  function polarity agree with InvalML.
- Explicit function type arguments constrain callback inputs even when the
  function never calls the callback locally.
- Two supplied types at one activation each receive every relevant bound; one
  supplied union remains a single negative constraint target. Inspect delivery
  directly where concrete mismatch diagnostics are intentionally quiet.
- Candidates arriving before or after relations produce the same result.
  Separate importers leave the exporter and prelude hosts unchanged.
- Generic-body checking, interface exposure, and completed member targets remain
  intact. Run `ctest` before focused worksheets and `hkmc2AllTests/test` before
  completion; review and commit the generated golden outputs.

Precise array positions/lengths, loud concrete-mismatch diagnostics, optional
`splice` arguments, general storage reassignment, and handler inference remain
separate work.
