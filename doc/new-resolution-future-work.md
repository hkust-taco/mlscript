# Deferred resolution design work

This reference records confirmed implementation gaps and deferred design work.
The convergence failures below must be corrected before claiming that accepted
type graphs are finite. Other design refinements require review before implementation. Current
contracts are in [instance types and parameter constraints](new-resolution-type-value-flow.md);
remaining suite ports are in the [migration worklist](new-resolution-suite-migration.md).

## Confirmed convergence failures

### Partially supplied forwarding aliases

```mlscript
type First[A, B] = A
type Chain[A] = {value: A, next: Chain[First[A]]}
private fun walk[A](chain: Chain[A], n: Int) =
  if n > 0 then walk(chain.next, n - 1) else ()
```

This has the same finite unfolding as `Chain[A] = {value: A, next: Chain[A]}`.
`declaredType` reduces an applied alias only when every formal is supplied, whereas
deferred interpretation fills omissions with source holes. Keeping `First[A]` as
an argument retains another binding environment on each recursive constraint;
eventually hashing `DeclaredType` overflows. Supplying the unused `B` makes the
example terminate. The same failure occurs through a forwarding alias and with
argument permutations. Unify the argument-binding rules while preserving omission
identities, variance, captures, and the alias expansion guard.
Regressions: `newres/TypeGraphPartialAliases.mls`.

### Fresh sites during structural member constraints

```mlscript
type Link = {next: Link}
class Node with
  fun next[A] = this
private fun take(x: Link) = ()
take(new Node)
```

`constrainRecord` allocates a fresh `FlowSymbol.memSym` for the expected field on
every visit. Selecting `next` invokes the by-name definition and uses this new
symbol as its instantiation site. The resulting substitution distinguishes another
receiver view, which repeats the structural constraint and allocates again.
The definition/site cache cannot bound allocation when the sites themselves grow.
An unused binder is sufficient; removing it makes the example terminate. Declared
results and separate quantified signatures also reproduce the overflow.
Synthetic projections need stable identities tied to the finite source graph,
with ordinary marks retaining activation separation.
Regressions: `newres/TypeGraphProjectionSites.mls`.

## Quantified bounds

`TypeQuantifier` and `DeclaredTypeParameter` store lower and upper bounds, but
`instantiateCallable` substitutes only the parameter/result types and supplied
arguments. It never installs the bounds as relations on the new instances.
For example, a result of `[A extends Item] -> () -> A` does not expose `Item`'s
members when the type argument is inferred. A separately signed implementation
also cannot use its parameter's declared upper-bound interface. This is distinct
from postponing concrete mismatch diagnostics: the constraint edges and checking
interfaces themselves are missing. Regressions: `newres/QuantifiedBounds.mls`.

## Inherited type-argument constraints

Matching an actual subclass against `Parent[A]` currently leaves `A` unconstrained.
The nominal branch of `inferTypeArguments` compares exact class identities and
does not follow the instantiated parent view. Thus `read[A](p: Parent[A]) = p.item`
loses its result interface for both constructed and declared `Child[Item]` inputs,
while `Parent[Item]` works. The field has a complete signature, so this is separate
from inferred member signatures. The exact-class restriction predates the current
type-relation implementation. Follow the parent's bindings and scope transfers
when installing both variance directions. Regressions: `newres/InheritedTypeArguments.mls`.

## Productive Boolean alias cycles

The alias observation guard publishes an opaque candidate when revisiting an alias.
For `Choice[A] = A | Choice[A]`, this adds an unknown alternative alongside `A`,
preventing member lookup even though the productive unfolding exposes only `A`.
This behavior predates the current Boolean normalization. A correction must also
specify unproductive cycles and recursive intersections; simply removing every
opaque candidate is not a general solution. Regression: `newres/RecursiveBooleanInterfaces.mls`.

## Receiver reconstruction

```mlscript
class Box[T](val item: T) with
  fun copy() = new Box[T](item)
```

Reconstruction needs to retain the old receiver's view of `T` separately from the
new constructor's view. Distinct receiver calls currently lose the returned field's
interface. The constructor-value form `Box[T](item)` has the same precision gap.
The unannotated control, `class Box(val item)` with `copy() = new Box(item)`, mixes
field candidates from distinct receivers. This therefore affects ordinary value
inference as well as explicit type parameters.

A correction must preserve both receiver and new-allocation contexts using the
ordinary marks algebra. Correcting only a binder substitution does not establish
receiver separation. Regressions: `newres/ConstructorInstances.mls`.

## Inferred member signatures

Missing types on selected members should use the selected declaration's contextual
inference graph, consistently with partial function signatures:

```mlscript
class Item(val value: Int)
class Box with
  fun item() = Item(1)
private fun read(x: Box) = x.item().value
```

The desired result is to infer `Box.item`'s result and permit `.value`. The current
nominal view does not expose that missing result type. The same improvement applies
to missing parameter, constructor-field, and value-member types.

Keep the actual receiver's contextual flow on these inferred connections while
using the written nominal type for lookup. A `Base` annotation must not expose
`Child`-only members. Annotated portions retain their written types, and selected
members retain their own schemes, including overloaded term alternatives.

Override compatibility is part of this work: a base implementation returning
`Item` cannot justify `.value` on every dynamic dispatch result if an override can
return a different interface. Check overriding inputs and outputs against the
inherited interface before completing targets or exposing inferred dispatch
results. Preserve imported reference completion and consumer isolation.
Regressions: `newres/DeclaredTypes.mls` and `PartialSignatures.mls`.

## Omitted-argument contexts

Missing generic arguments are ordinary inference holes. Their current substitution
can lose caller separation, even without recursion:

```mlscript
class First(val first: Int)
class Second(val second: Int)
class Pair[A, B](val value: [A, B])
private fun second(pair: Pair[Int]) = pair.value.1
[second(Pair([0, First(1)])).first, second(Pair([0, Second(2)])).second]
```

Both results receive both candidates and produce missing-member diagnostics.
Removing the parameter annotation avoids this template-substitution path and
preserves ordinary argument flow. Related cases use a shared alias-body omission
or a mutable `Array` annotation, with and without recursion.

The hole belongs to the annotation inside `second`. Following the captured `Pair`
template rebases its argument outward with a wildcard exit, then projects it back
with a wildcard entry. Applied to incoming bounds, the exit consumes the call's
identified entry; re-entry cannot restore that ID. This is the specified marks
behavior, not permission to cancel those operations on references.

A possible representation separates the template endpoint from the supplied
argument environment. Following a formal would use the argument's own endpoint;
following a free reference would use the template's context. This remains an open
design: verify deferred member projection, both constraint directions, polarity,
recursive aliases, and finite canonical reference keys. Dropping template transport
loses enclosing binders, while allocating per-call hole instances violates ordinary
inference. Regressions: `newres/InferenceHoles.mls`, `PartialSignatures.mls`, and
`AnnotationContexts.mls`.

## More precise regularity analysis

The current conservative check rejects some finite structural types. The
[regularity reference](new-resolution-regular-types.md#deferred-refinement-for-later-review)
contains two refinements for later review: input/output dependency analysis used
also for environment projection, and accounting for correlations between recursive
arguments after Boolean normalization. Neither is required for the current
conservative implementation.

## Whole-graph convergence audit

Binder allocation for fixed definition/site keys, source dependency analysis,
and relation replay have local bounds. A complete argument must also bound the
sites themselves, accepted contextual reference keys, nested environments, and
formula atoms, then establish listener convergence.
Retain marked parameter references and shared recursive edges; do not expand live
bounds into fresh type trees. Test delayed delivery, mutually recursive calls,
changing compound arguments, and independent consumers at the graph level.
