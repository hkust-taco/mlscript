# Instance types and parameter constraints

`InstanceShape(T)` describes an instance of the type `T`. Types remain in the
`TypeShape`/`DeclaredType` graph. The instance wrapper replaces the earlier
nominal-only representation at annotation boundaries: parameter and result
annotations, ascriptions, generic arguments, and annotated tuple fields retain
a type reference until an operation requests its interface.

Instance wrappers and preservation of quantified signature binders and bounds
are implemented. Explicit type application also observes annotated polymorphic
values. Calls through complete callable signatures use the bounded binder-instance
cache. `DeclaredType.instances` carries a flat substitution through their declared
components; curried tails retain it, and independently quantified returned callables
instantiate their own binders. Stored specializations of complete signatures and
inferred functions retain supplied arguments until application. Inline binders on partial and inferred
functions also instantiate at application sites. Their shared bodies retain flat
substitutions through deferred tuples, records, callbacks, and closures. Nominal
argument comparisons retain both endpoint references and apply declaration/use-site
variance. The recursive array acceptance cases pass. Supplied function arguments
receive input obligations while retaining their declared output interface.
Observing specialized inferred functions before application, replacing the remaining
explicit-argument flags and constructor path, holes, inferred nominal member interfaces, and general
recursive alias environments still need integration. The implementation order below
remains the full design, not a claim that all its parts are complete.
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

`inferTypeArguments` retains wrappers when contributing a parameter bound and
observes them for structural comparison. For an explicitly supplied argument,
an input obligation follows its retained type reference instead of becoming an
additional output candidate. Each distinct supplied type receives the obligation;
a supplied union stays whole. The implementation still identifies supplied
positions with explicit-argument flags. Integrating those positions into the
shared reference graph remains necessary for constructor views and general
recursive type environments.

## Variance rules

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

`TypeShape.Wildcard` retains the written input/output nodes. Nominal bindings apply
declaration variance only to unqualified arguments. Interface observation follows
the output part; an instance bound constrains the input part. Function constraints
already reverse domains, including callbacks nested in member inputs. Argument
comparison installs the two directed `ContextualType` relations above. Missing
parts use shared `Top`/`Bottom` nodes, independently of inference holes.
`newres/TypeArgumentVariance.mls` covers these paths; applying the same machinery
to standalone function/constructor specialization remains part of the explicit
type-argument integration work.

Synthesized declaration variance uses `TypeShape.Argument`, whose parts retain
complete contextual type references. It must not transplant an argument's syntax
node into the alias or class's new binding environment: an outer argument with
the same source binder can then resolve back to its own wrapper. Reusing the
argument reference and normalizing repeated synthesized wrappers bounds this
construction. The recursive covariant `Tree` regression exercises this invariant.

## Recursive acceptance example

This passing regression is retained in
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

The result is `5`. The relation connects the array's element parameter to the
call-site instance of `A` in both directions, retaining each endpoint's marks.
Recursive calls reuse their parameter instance and propagate the inserted element
back through that graph. The adjacent two-array case checks isolation between
external callers of the shared recursive site.

## Resolver integration

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

Use constraints over these references, rather than restoring wildcard matches
after copying expanded candidates. The argument endpoint retains its caller's
substitution and context; the parameter endpoint uses the callee site's instances.
An application must not overwrite both endpoints with the callee substitution.

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
owner is its original quantified declaration node. An overload resolving to more
than one definition instantiates each original definition at that site. Where
the language implicitly invokes a getter, its source reference/selection is the
invocation site; it is not a fresh site per resolver visit. Neither imported
views nor instantiated callable views should manufacture a new original owner.

### Binder substitution before observation

Normalize binders from inline declarations and separate signatures into a
reusable scheme with its parameter bounds, declared type fragments, and links to
inference for unannotated parts. Do not require a complete signature.
`TypeShape.Polymorphic` retains `Forall` binders and bound references;
`DeclaredTypeParameter` carries their interpreted bounds on callable views.
These original identities must be used when instantiating separate signatures.

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
is described below.

### Shared graph and contextual views

Retain one source graph per definition. Its nodes describe written type structure,
references to binders, and inferred flows from parameters, expressions, and holes.
Give references to that graph an explicit view consisting of:

```text
source node + originating inference host
substitution of this node's free explicit binders
existing normalized marks
```

The binder substitution selects original binders or memoized call-site instances.
It is a flat mapping over the source node's free binders, not a stack of past
substitutions. Keep compound supplied types as graph references connected by
constraints; do not insert their successive expansions into the substitution.
Alias and nominal argument bindings likewise retain references to argument nodes,
with recursive bindings represented by back-edges rather than nested map copies.
This requires replacing the recursive structural use of `DeclaredType.bindings`
where it would otherwise grow a new environment on every recursive visit.

Memoize each view before observing its source node. Observing an inferred flow
subscribes to its existing host in the consuming resolver and applies the view
to arriving references. Observing a compound value exposes its outer shape while
giving its deferred children the corresponding view. This applies to tuple and
record fields, callable results, nested annotations, and closure captures; merely
rewriting the outer `InstanceShape` is insufficient. Compose views by replacing
bindings for the callee's own binders and retaining lexical captures, then discard
bindings unused by the observed source node. Do not wrap a view in another view.

For `pair[A](x: A, y) = [x, y]`, the result's first field observes the annotation
node under `A -> A_s`; the second subscribes to `y` under the call's marks. A
closure returning `x` keeps the first reference after the enclosing call returns.
The body, field nodes, and `y` symbol are shared; only their views differ.

The implemented body transport keeps two substitutions separate. A value such as
`InstanceShape(A_outer)` retains the caller's type reference. Its flow into a body
also carries that body's activation, for example `A -> A_inner` at a recursive
call. `ActivatedShape` records this second map on source-flow events;
`ContextualShape` and the tuple/record views retain deferred observations of values.
Dispatch unpacks the activation before performing an operation. Source listeners
accept all activations; an observation with a chosen substitution accepts only
compatible activations of its source node. It must not rewrite an already bound
caller reference to the callee's parameter. `NewResolverState.withInstances`
memoizes flat activation views that share the consumer's hosts, and `inGraph`
preserves the incoming activation when selecting an imported listener's graph.

`newres/ContextualInference.mls` exercises separate calls through one stored
function reference, mixed annotated/inferred tuple and record fields, callbacks,
and returned closures. These cases use the existing reference marks unchanged.

Generic-body checking observes the source graph with its original abstract
binders. Call inference observes it with the site's substitution. The abstract
unknown produced to check operations on a rigid binder is a checking witness,
not a lower bound to copy into the instantiated graph. Preserve the existing
diagnostics for operations unsupported by `A`; do not suppress all unknown
values or remove ordinary exposure-checking constraints. Keep the symbolic
binder dependency until an observer has chosen its view. In particular,
`registerTypeParameters` cannot keep seeding a host whose expanded candidates are
then blindly reused as a call's inferred result.

### Constraints and marks

Memoize a directed constraint by its two contextual type references, including
their originating hosts. Keep three operations distinct:

- An ordinary instance contributes a lower-bound obligation to its expected type.
- Supplying a type reference retains that reference and delivers lower and upper
  obligations to it, including obligations that arrive later.
- Comparing compound types follows their structure and argument variance, using
  the same contextual references at every recursive step.

Register listeners before replaying existing facts. Adding either a bound or a
supplied type must process the other facts already present, so event order does
not matter. For invariant arguments, install both directed constraints between
the retained endpoints; do not obtain the second by reversing a path already
applied to expanded candidates. Preserve a supplied union as a whole in negative
position. Deduplicate relations and delivered obligations by semantic references,
not by diagnostic witnesses.

The implemented `constrainTypes` memoizes pairs of `ContextualType` endpoints
before following them. A parameter receives an instance wrapper retaining the
source reference; a structured or concrete target subscribes to that reference's
later bounds. Quiet concrete mismatch diagnostics do not discard these obligations.
`TypeRelationTest` checks cyclic propagation, early/late bounds, every distinct
upper target, preservation of a whole negative union, reverse endpoint contexts,
and independent importers. The supplied-argument tests additionally check input
obligations arriving before and after supplied references, chained parameters in
different marked contexts, isolation between activations, and cycles without
listener growth. These checks do not yet replace the remaining explicit-argument
flags or establish the whole-graph termination bound.

Existing marks still transport instance flow through lexical scopes and distinguish
enclosing activations sharing a static inner call. Apply their current entry/exit
operations to each endpoint in its own view. A callee's symbol allocation key
does not include marks, and a caller's view is not replaced by a wildcard when
forming the reverse constraint. The proposal adds no mark syntax, path truncation,
or cloned lexical boundaries. Enable the existing path invariants in focused
solver tests to catch a mistaken context composition rather than masking it.

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
An empty hole is pending inference, not an `UnknownValueShape` candidate to emit
immediately: later evidence may resolve it. At completion, a hole without usable
evidence supplies no member interface and does not grant dynamic access. An
unknown alternative actually contributed by exposure checking is different and
must remain even if some concrete candidates arrive too.

An inference hole must be distinguishable from an intentionally abstract type,
an `in`/`out` wildcard, and an unresolved or invalid annotation. These must not
all collapse to `TypeShape.Abstract`, which the current interpreter uses for
several unsupported forms. Inferring one missing piece must not add members to
an explicitly written concrete interface elsewhere in the annotation.

**Omitted generic arguments are inference holes too.** For `Pair[A, B]`, a written
`Pair[Int]` supplies `Int` for `A` and a hole for `B`; bare `Pair` has two distinct
holes. Identify each omission by its source type-use occurrence and missing formal
parameter. Two occurrences do not share a hole just because they name the same
class. Reinterpreting an occurrence, following an alias, or observing another
member reuses its contextual hole reference. Apply declaration-site variance to
the missing argument just as to an unqualified written argument. Explicit
`in`/`out` arguments retain their stated defaults; their absent parts are not holes.

For `type HalfPair[T] = Pair[Int, T]`, a bare `HalfPair` introduces a hole for
`T` at that use, and the alias body forwards that reference into `Pair`'s second
argument. An omission written inside an alias body has its own source node and
is transported with the alias use's context; expansion must not allocate more
hole symbols. Excess arguments still indicate an arity error.

The positive `Pair[Int]`, `HalfPair`, and bare `Array` cases in
`newres/PartialSignatures.mls` record this missing behavior as `:fixme`s. Existing
`DeclaredTypes.mls` examples selecting members from omitted arguments without any
supporting flow remain negative tests: a hole is inferable, not evidence of an
arbitrary member. Replace the current unconditional `abstractType` treatment of
omissions; report insufficient inferred information when a genuinely unfilled
hole is observed.

The scheme therefore cannot be a closed type synthesized from whatever shapes
happen to be available first. It must retain live links to inferred portions of
the definition, including bounds arriving later or through recursion. Existing
exposure checks for unannotated parameters and generic-body checking still apply;
partial annotations must not silently disable either.

### Inferred member signatures through nominal annotations

The agreed partial-signature semantics also apply to a selected member's missing
types through a nominal annotation. For example:

```mlscript
class Item(val value: Int)
class Box with
  fun item() = Item(1)
private fun read(x: Box) = x.item().value
read(new Box)
```

Use `Box.item`'s inferred result here, consistently with partial function
signatures. Missing parameter types, constructor-field types, and value-member
types likewise link to the selected declaration's inference graph. Keep the
receiver's context on those links; using the class's unmarked global inference
would mix distinct instances. A nominal constraint must retain the actual
receiver's contextual flow as an input to these missing member types. The current
wrapper containing only a closed declared interface cannot recover an unannotated
constructor field after that receiver flow has been discarded. Keep the receiver
reference on the inferred member connection, while using the written nominal
type for lookup; do not replace the annotation's view with the actual receiver's
whole shape. Explicitly annotated member portions still use their written types.
Class-qualified selections and overloaded names
use the selected member's own scheme, including the term alternative of an
overloaded name. The corresponding examples in `DeclaredTypes.mls` are now
`:fixme` acceptance cases instead of requirements to reject inference.

The nominal member set stays fixed: a `Base` annotation must not expose members
found only on `Child`. Overrides must satisfy the selected declaration's input/output
constraints. It is insufficient to assume that the base method's body describes
every dynamic dispatch result. In particular, a base method returning `Item` and
an override returning a type without `Item`'s members cannot justify selecting
those members from the dispatched result. `PartialSignatures.mls` retains this
negative regression. Connect override signatures to the inherited interface
before completing member targets, following function input/output variance;
do not expose an unchecked base implementation shape as a dispatch guarantee.
Preserve the existing member-target completion checks for imported code as well.

### Partial application and explicit specialization

For curried calls, instantiate when the first parameter
list is consumed and retain that substitution in the partially applied callable.
Later lists reuse it. A separately quantified returned callable has its own
binders to instantiate at its later application. A standalone specialization such
as `let g = f[Int]` retains its supplied type arguments until application;
each application of `g` then binds its own site instances to `Int`. This avoids
introducing a second allocation policy at type-application nodes. Check argument
arity against the retained scheme immediately, and allow observations of the
specialized interface to use its supplied type references before a term call.

`SpecializedShape` retains the original inferred function, supplied argument
references, and captured call-site instances. Application unwraps that recipe,
allocates or reuses the definition/site binder group, and attaches the supplied
references before replaying body constraints. It does not publish arguments into
the original definition's type parameters. `newres/StoredSpecializations.mls`
checks independent specializations through one stored alias, deferred record
results, curried calls, and arity errors even when a specialization is unused.

Pre-application observation of an inferred result is still missing. The same
worksheet retains this concrete regression:

```mlscript
class Item(val value: Int)
private fun identity[A](value: A) = value
private fun use[B](f: Item -> B): B = f(Item(9))
use(identity[Item]).value
```

The expected result is `9`. Checking the argument against `Item -> B` must observe
`identity`'s inferred result with `A` referring to the supplied `Item`. Currently,
the deferred body view can map `A` only to a call-site parameter symbol, and no
call to `identity` has been observed at this point. Its result therefore fails to
constrain `B`. Allocating an instance during callback checking or writing `Item`
into the shared original `A` would violate the design.

The proposed extension, pending review, is to let deferred views also reference
supplied type-argument nodes. Such references must remain shared graph edges:
recursively substituting `DeclaredType.bindings` maps into one another would lose
the finite-domain argument below. The representation must support deferred tuple
fields and closures as well as this scalar result. This regression remains a
`:fixme` until that representation and its termination invariant are settled.

### Constraint propagation and implementation order

1. Preserve partial declaration/signature schemes and their original identities,
   including links to inferred portions. Distinguish inference holes from
   intentionally abstract types and variance wildcards. Add a
   consumer-owned cache of complete call-site instances, with origin links back
   to the declared binders. Keep omissions source-owned; do not add mutable caches
   to symbols. Preserve `Forall` binders and their bounds instead of erasing them.
2. Transport the memoized substitution through callable and result views before
   expanding instance wrappers. Keep the existing marks for value flow and
   lexical captures. Separate generic-body checking witnesses from the symbolic
   constraints replayed in a call view. Verify delayed fields and returned closures.
3. Relate the resulting type references in both input and output positions,
   retaining their hosts, substitutions, and marks. Ordinary arguments contribute
   bounds; supplied types receive all obligations at their applicable polarity.
   Apply the InvalML variance rules above.
4. Replace `applyTypeArguments`, nominal inference, explicit-argument suppression,
   and the positive-only conversion in `instanceBindings` together. Reuse the
   same mechanism for functions, constructors, and declared array interfaces.
5. Route declared member lookup to partial member schemes, retaining receiver
   contexts for inferred fields and results. Check override compatibility before
   completing member targets. Convert the member-inference `:fixme`s together;
   keep tests rejecting subclass-only members and unsupported override results.

Keep this work inside resolution and type interpretation. Lowering still consumes
completed member targets and value shapes; runtime values acquire no type-argument
objects. The main source changes are in `TypeShape.scala` (schemes and contextual
references), `NewResolverState.scala` (consumer-owned memo tables),
`NewResolver.scala` (view observation and constraint delivery), and `Shape.scala`
(transporting views through deferred children). Elaborator signature registration
must preserve binders and missing positions before the body is observed.

### Fixed points and implementation checks

There are at most as many allocated parameter instances as the sum of each
reachable definition's binder count over its syntactic call sites. Source hole
nodes and written type/term nodes are finite independently of recursive visits.
View substitutions range over the finite original and instantiated binders in
lexical scope. With the existing no-repeated-boundary mark invariant, their
normalized contexts also range over a finite domain. These facts bound the set
of memoized views and endpoint pairs **provided** compound arguments remain shared
graph edges and no cache key includes a growing substitution or capture history.
Monotone, deduplicated propagation then reaches a fixed point.

Check this at the graph layer as well as with worksheets. Replaying an existing
definition/site must leave the instance count unchanged; replaying the same view
or relation must add neither a listener nor a node. Include mutually recursive
definitions and changing arguments such as a recursive call with `Array[A]`:
the recursive site's parameter must receive a cyclic reference to the source
`Array[A]` expression, not generate `Array[Array[...]]` nodes on every pass.
Verify obligations delivered before and after edge creation, and two callers of
one inner site with different enclosing marks. Count cache growth until saturation;
passing a shallow recursion test is not sufficient evidence of termination.

`TypeInstantiationTest` checks that repeated scheme/site allocation reuses the
whole group, distinct applications through a stored declaration allocate distinct
groups, and consumers do not copy generic checking candidates into their instances.
For the implemented signature views, the substitution map contains only original
binder keys and canonical instance-symbol values. Composition cannot add a nested
environment or a compound type to that map. Instantiated callable views are cached
before installing supplied-argument listeners. This bounds this part of the graph;
the activation views similarly use finite binder maps and a fixed base state,
never chains of activation states. Unit tests check repeated composition and
imported-view identity, shared consumer hosts, and exporter isolation. Whole-graph
listener convergence and recursive alias bindings still need the corresponding
checks before the full design is complete.

Shape substitution is memoized too: repeated observations reuse the same deferred
tuple/record identity, so synthesizing its nominal array interface cannot create
a fresh type node on each traversal. Relation keys contain endpoint references,
flat binder maps, and existing normalized marks; they contain no candidate history.
Replaying a relation adds no listener or candidate. The recursive changing-array
and mutual-recursion cases in `newres/ContextualInference.mls` terminate with mark
invariant checks enabled. For a fixed finite set of source type references, there
are finitely many endpoint/map/mark combinations, and replay adds no listeners.
That local bound does not establish the remaining whole-graph alias-environment
bound, which must also prove that source references cannot proliferate.

During implementation, assert that a call instance's origin is an original binder,
all of one scheme's binders are allocated before its constraints are activated,
views are composed rather than nested, and generic checking witnesses never become
ordinary instantiated lower bounds. Retain consumer-private host copies and the
existing prohibition on changing completed member targets. The design review does
not license changing mark normalization if these checks fail; any such change
requires a separate concrete example and proposal.

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
- Selected members infer missing types through nominal annotations, including
  constructor fields, method results, and overloaded value members. Receiver
  contexts remain distinct; subclass-only members and unsafe override results
  remain rejected. Deferred closure observations preserve the outer substitution.
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
