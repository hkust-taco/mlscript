# Instance types and parameter constraints

`InstanceShape(T)` describes an instance of the type `T`. Types remain in the
`TypeShape`/`DeclaredType` graph. The instance wrapper replaces the earlier
nominal-only representation at annotation boundaries: parameter and result
annotations, ascriptions, generic arguments, and annotated tuple fields retain
a type reference until an operation requests its interface.

The wrapper refactor is implemented. Bidirectional type-argument constraints and
variance are the next step. The constraint representation proposed below still
needs agreement before implementation. See the [resolver notes](new-resolution-design.md)
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

## Existing symbols and marks identify inference

**Do not allocate fresh type variables for calls, arrays, or constraint matches.**
Fresh variables would prevent recursive inference from returning to existing
graph nodes and reaching a fixed point. A contextual reference uses the existing
parameter symbol, its originating inference host, and marks. In particular, a
mutable array uses the builtin `Array` element parameter with its allocation and
call contexts. Actual element shapes contribute bounds to that parameter.

Keeping a reference to an unresolved parameter is essential. Copying its current
positive candidates loses its negative uses and its identity as a type argument.
Subscriptions must also account for constraints or candidates arriving later.
Graph caches and listeners belong to the consuming `NewResolverState`; extending
a consumer must not mutate a prelude or an exporter's inference graph.

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

## Proposed extension: retain both contextual type references

Represent an argument relation as a persistent constraint between two type
references, each retaining its original host, bindings, and marks. Keep the
argument's input/output parts on this relation. Do not immediately replace it
with two unrelated subscriptions that copy positive candidates.

A capture match must belong to the relation traversal. When a wildcard matches
`enter(f, abstract)`, retain that matched activation while transporting the bound
through the opposite endpoint. A reverse obligation uses the same match; it
must not recreate `enter(f, *)`. For a concrete caller, both endpoints instead
use that caller's match. Deferred propagation must retain this association too.

Conceptually, the recursive relation is a family:

```text
A at recursiveCall(caller)  relates to  A at caller
```

`caller` here names a shared capture match, not a fresh type variable or a new
runtime symbol. The current independent edges effectively erase it on the
recursive side. Retaining type references allows a constraint to postpone that
match until it has an activation to use, instead of forwarding every currently
observed lower bound through an unconditional reverse edge.

Proposed implementation steps:

1. Introduce immutable contextual type-reference endpoints and memoized argument
   relations in `NewResolverState`. Reuse existing `TypeResolution` nodes and
   parameter hosts. Keep supplied type references distinct from ordinary bounds.
2. Implement capture matching that records the normalized path matched by a
   capture and reuses it across the relation's two endpoints. Keep this data in
   constraint facts or their subscriptions, never mutable global symbol fields.
3. Deliver lower and upper obligations to each supplied type reference. A plain
   inferred value adds a lower bound; explicit instantiation and invariant
   argument matching must preserve the supplied type's uses in both positions.
4. Interpret declaration/use-site variance using the input/output parts above.
   Use the same constraint mechanism for arrays, generic classes, and functions.
5. Only then replace `applyTypeArguments`, nominal inference, explicit-argument
   suppression, and the positive-only conversion in `instanceBindings` together.

The unresolved implementation question is the finite representation of capture
matches under recursive relation composition. Merely storing an ever-growing
history of matches would repeat the fresh-variable termination problem. Before
landing this extension, demonstrate that recursive processing revisits memoized
relations over existing nodes and normalized contexts, including nested type
applications and mutually recursive calls. If that requires changing mark
normalization or the domain of contexts, report that design separately.

## Acceptance checks

- An initially empty mutable array receives an element through `Array[A]`.
- Two calls using different arrays and incompatible element interfaces remain
  independent, including two callers of the recursive example above.
- Recursive input/output relations terminate without fresh type variables,
  repeated-boundary paths, or unbounded binding-environment construction.
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
