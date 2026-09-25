# Regular structural types and canonical references

This is an internal reference for structural recursion in new resolution. The
instance-wrapper and variance semantics are specified in
[instance types and parameter constraints](new-resolution-type-value-flow.md).

## Requirement and current status

A structural type must unfold into a finite graph of distinct type components.
Check regularity after reducing aliases and normalizing unions/intersections;
textually changing an argument is not itself evidence of unbounded growth.

```mlscript
type Chain[A] = {value: A, next: Chain[A]}
type Alternating[A, B] = {value: A, next: Alternating[B, A]}
type Reset[A] = {value: A, next: Reset[Array[Int]]}
type Saturating[A] = {value: A, next: Saturating[A | Int]}
type Growing[A] = {value: A, next: Growing[Array[A]]}
```

The first four have finite unfoldings. `Growing[Int]` exposes `Int`, `Array[Int]`,
`Array[Array[Int]]`, and so on. It must eventually receive a regularity diagnostic,
without widening the type or imposing an expansion-depth limit.

Canonical references now reduce fully supplied aliases and normalize Boolean
combinations. The regularity diagnostic is **not implemented**. A check using one
dependency node per formal parameter is insufficient: it conflates the parameter's
input and output parts and loses correlations between arguments. The refinement
below requires review before implementation.
The existing stack-overflow regression remains a known failure, not an acceptance
case for non-regular recursion.

## Implemented normalization

`TypeFormula` represents a union of intersections as a set of sets of interpreted
references. It applies associativity, commutativity, idempotence, distribution,
and absorption. It does not inspect nominal subtyping, class disjointness, or the
current candidates of an inference host. For example:

```text
(A | Int) | Int             = A | Int
(A | Int) & Str             = (A & Str) | (Int & Str)
A | (A & Array[A])          = A
((A | Int) & Str | Int) & Str = (A | Int) & Str
```

`TypeShape.Combined` retains the formula as one type. In particular, supplying a
union still creates one instance wrapper, and a negative obligation against that
union stays whole. Member-interface observation can inspect its components, just
as it did for source unions and intersections. Normalization does not turn one
supplied union into several independently supplied types.

Formula atoms retain their lexical bindings, canonical binder instances, and
ordinary marks. Different written references to the same unbound parameter and
host share an atom within a formula. Ordinary annotation references retain their
own source locations for diagnostics. A live parameter remains a reference;
normalization does not freeze its current bounds. Combined nodes are interned in
the consuming resolution state, using the same inherited-cache discipline as other
type references.

Fully supplied aliases reduce before they become another type's argument. Arguments
are interpreted in their caller environment first, then declaration variance is
applied and the alias's formals are substituted. A guard on source alias symbols
stops unproductive recursive expansion. Nested arguments are reduced before adding
the outer alias to that guard, so `Identity[Identity[A]]` reduces to `A`.
Reduction stops at nominal, tuple, record, and function constructors.

A captured alias uses the same application rule as deferred interpretation:

1. Rebase supplied arguments to the template endpoint using the existing mark
   operations.
2. Substitute the formals at that endpoint.
3. Transport the resulting reference back using the existing mark operations.

This applies to `Chain[B | Identity[B]]` when `Identity` is captured by an enclosing
function. Retaining the captured application as a fresh argument layer on each
projection would prevent a fixed point. Conversely, cancelling its scope crossings
would change the meaning: a wildcard exit followed by wildcard entry can lose the
caller's ID and is **not** an identity. Eager reduction performs those operations;
it does not add any special mark simplification.

Dependency discovery also follows the source graphs retained by synthetic formulas
and contextual references, without treating their saved bindings as ambient free
variables. Unresolved forward references therefore still delay interpretation.

For a fixed finite atom set, the antichains of subsets used by `TypeFormula` are
finite. This bounds repeated union/intersection substitution, including alternating
operators. Formula normalization can be exponential in the number of atoms; this
is a representation bound, not a claim of linear complexity. No fresh inference
variables or binder instances are allocated by normalization.

This does **not** by itself bound the atoms. Constructor growth, retained argument
parts that never become observable, and the existing requirements on finite marked
contexts remain separate obligations.

## Why a binder-only growth graph is insufficient

A candidate check connected original formals through recursive applications. An
edge recorded whether the argument wrapped its source formal in a non-Boolean
constructor. A growing edge on a dependency cycle caused rejection. Alias and
Boolean normalization preceded edge construction; unused formals were removed by
existing source dependency analysis.

That handles ordinary permutations and resets, including:

```mlscript
type Left[A] = {value: A, next: Right[Array[A]]}
type Right[B] = {value: B, next: Left[Str]}
```

The wrapping edge is followed by a reset, so no growing dependency cycle remains.
It also distinguishes an absorbed `A | (A & Array[A])` from the growing
`A | Array[A]`.

However, this finite case would be incorrectly rejected:

```mlscript
type Chain[A] = {value: A, next: Chain[in Array[A]]}
private fun read[A](chain: Chain[A]) = chain.next.value
```

At the positive occurrence `value: A`, substituting `in Array[A]` selects its
missing output part, `Any`. All later `value` components have that output type.
The constructor inside the input part is not an observable growing component of
this structural unfolding. A binder-only edge from `A` to `A` loses that fact.
The worksheet contains this finite projection as an acceptance test against an
incorrect regularity diagnostic.

The representation needs the same distinction. Current free-binder projection
retains the whole bound argument whenever a formal is relevant, including parts
not selected by the structural body. Recursive observation can therefore accumulate
input-part environments even when the resulting structural type is regular.
Merely permitting this case in a rejection check would not establish termination.
The candidate rejection rule has not been enabled.

## Proposed refinement for review

Track dependencies on argument parts, rather than only on binder symbols. The
analysis must distinguish lexical occurrence polarity and argument-part selection
from the direction of an instance-value constraint. A selected argument denotes
one fixed type for both subsequent input and output constraints.

Let `I_p(T)` mean interpreting a type expression in its saved lexical polarity
`p`. A reference to alias formal `A` demands the `p` part of its bound argument.
For the parts produced by the current argument interpretation rules:

| Argument | Input part | Output part |
| --- | --- | --- |
| Invariant `S` | `I_p(S)` | `I_p(S)` |
| Written `in T` | `I_not-p(T)` | `Any` |
| Written `out U` | `Nothing` | `I_p(U)` |
| Plain `S` with declaration `in` | `I_p(S)` | `Any` |
| Plain `S` with declaration `out` | `Nothing` | `I_p(S)` |

Written wildcards override declaration variance, as in the existing interpreter.
The difference between the written `in T` row and the declaration-variance row is
intentional: a written input bound is an opposite-polarity syntax occurrence;
declaration variance selects which parts of an already interpreted argument are
available. These are the rules to preserve, not a proposal to change substitution.

For an invariant actual argument `B`, selecting either part of the callee's formal
still selects the same saved `I_p(B)`. It must not reinterpret `B` with the callee's
current polarity. Likewise, after selecting a written argument part, both subsequent
constraint directions use that fixed type. Function inputs reverse lexical polarity;
record fields, tuple fields, and function results preserve it. Scope transport does
not change which argument part is selected and continues to use ordinary marks.

The analysis can attach finite demand sets to source states consisting of a source
node, lexical polarity, and whether the operation requests the whole interpreted
type or a particular argument part. The demands name original binders and their
input/output parts. Alias application composes these demands with the argument table,
hiding the callee's formals. Forward references delay finalization. Equations range
over a finite set of source states and part demands, so monotone iteration terminates
without unfolding substituted recursive types or allocating inference variables.

For `Chain[in Array[A]]` at positive polarity, the recursive output demand reaches
`Any`, ending that dependency. At negative polarity, selecting the written input
reverses the argument's saved polarity: its nested `A` demands the previous output
part, which is `Any`. Thus constructor depth does not grow indefinitely in either
polarity. A single binder node cannot express that dependency reset.

The same demand summaries must govern the saved environments. A projected argument
view should retain references only for demanded parts, together with an explicit
mask recording which parts are available. Selecting an unretained part must assert
an invalid dependency summary; it must not silently invent `Any`, `Nothing`, or an
inference hole. Extreme types in the table come from actual variance semantics,
not from environment pruning. Keep both parts when either may be selected. Preserve
source-owned holes and live inference references without inspecting their current
candidates. Nominal member dependencies remain conservative until their required
parts are known.

### A further limit of a simple growth graph

Even part-sensitive dependency edges lose relationships between arguments. This
regular type requires absorption across successive recursive substitutions:

```mlscript
type Stable[A, B] = {value: A, next: Stable[A | (B & Array[A]), A]}
```

Writing `X = A | (B & Array[A])`, its argument states are:

```text
(A, B) -> (X, A) -> (X, X) -> (X, X)
```

The second step computes `X | (A & Array[X])`, which is `X` because `X` already
contains `A`. The next step absorbs `X & Array[X]`. A per-parameter growth graph
still contains a constructor cycle and would falsely reject the definition.
`TypeGraphTermination.mls` includes a recursive observation of this example.

Consequently, refining binder dependencies into part dependencies is necessary for
environment projection, but it is **not sufficient** to make constructor cycles
an exact regularity test after Boolean normalization. Such a graph can provide a
sufficient acceptance criterion; a positive cycle cannot by itself justify a
non-regularity diagnostic. The rejection procedure must also account for normalized
substitution relationships, and must terminate on genuinely growing cases.
This procedure is an unresolved design obligation. Repeatedly unfolding until a
cache stops growing, imposing a depth limit, or assuming a constructor cycle proves
growth would not resolve it.

Proposed implementation boundary for review:

1. Specify and test the finite, part-sensitive demand equations above, including
   both polarities and alias substitution. This analysis itself has a finite
   source-graph bound.
2. Use those summaries for checked environment projection, retaining marks and
   live references. Verify the variance example and ordinary holes without claiming
   that this supplies a complete regularity decision procedure.
3. Separately design a terminating rejection check that preserves correlations
   needed by examples such as `Stable`. Only then enable regularity diagnostics,
   including for unused written annotations.

The whole resolver still needs a bound on accepted reference keys: finite source
and binder identities alone do not bound nested environments. Boolean normalization
bounds formulas only once their atom set is bounded. Existing finite-context
requirements on the marks algebra remain in force throughout.

## Regression coverage

`newres/TypeGraphTermination.mls` covers regular recursion, permutations, mutual
resets, unused arguments, transparent and captured forwarding aliases, forward
references, union/intersection saturation, Boolean-only recursion, and the variance
counterexample. Expected future regularity diagnostics are marked `:breakme`/`:e`;
they are completion obligations, not implemented rejection behavior.

`TypeFormulaTest` checks normalization against Boolean truth tables and repeated
alternating substitution. `TypeRelationTest` checks a thousand repeated reductions,
unchanged binder allocation and source-listener counts, late bounds, whole negative
union targets, and the loss of caller identity under captured alias rebasing. These
checks support normalization's local invariants; they do not establish the whole
resolver's termination argument.
