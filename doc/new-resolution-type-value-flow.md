# Instance types and parameter constraints

`InstanceShape(T)` describes an instance of the type `T`. Types remain in the
`TypeShape`/`DeclaredType` graph. The instance wrapper replaces the earlier
nominal-only representation at annotation boundaries: parameter and result
annotations, ascriptions, generic arguments, and annotated tuple fields retain
a type reference until an operation requests its interface.

## Review outcome

The following semantic decisions are settled:

- Wrap instance values, retaining references to their annotated types. Supplying
  a type argument affects both its input and output uses; an ordinary value
  argument contributes a lower bound.
- Instantiate explicit binders once per original definition and authoritative
  instantiation site: an explicit term-level type application, an implicit
  by-name invocation, or otherwise the first term application. Retain that group
  on the resulting value. Reuse it during recursion and use marks to distinguish
  enclosing activations of the same site.
- Infer every missing signature part through ordinary marked flow, including
  holes within annotations and omitted generic arguments. These positions do not
  introduce quantified binders or receive fresh symbols at calls.
- Apply the same rule to selected members' missing parameter, result, and field
  types through nominal annotations. Retain the receiver context and the selected
  declaration's member set; check overrides against that interface.
- Follow InvalML's declaration/use-site variance and occurrence-sensitive
  substitution, including nested function types.
- Mutable arrays collect element shapes in their element type parameter under
  marks. Tracking positions and lengths is outside this design.

The implementation plan is in [constraint propagation and implementation
order](#constraint-propagation-and-implementation-order). The
[instantiation-site implementation](#partial-application-and-explicit-specialization)
uses the existing finite maps to parameter instances for deferred value views:
an explicit type application already provides their site and parameter group. The [distinction between type-reference operations and
value-scope crossings](#type-reference-scope-audit) is approved. Recursive reference
graphs must preserve caller and receiver contexts without growing binding environments. The variance
substitution rules below are implemented for declared type views.

Require structural types to have a finite recursive representation: the proposed
[regularity restriction](#regular-structural-types) rules out structural unfolding
that keeps producing distinct types. The exact check remains to be reviewed before
implementation. This restriction and sharing regular recursive references are
separate obligations; neither follows from the bound on call-site symbols.

The finite call-site symbol bound alone is not a termination proof for the whole
resolver. Non-regular expansion still overflows; class-local aliases expose a
receiver-context failure. Dependency-based binding projection now accepts regular
argument resets, including compound constants and recursively unused arguments.
The [fixed-point conditions](#fixed-points-and-implementation-checks) remain completion gates.

## Implementation status

Instance wrappers and preservation of quantified signature binders and bounds
are implemented. Explicit type applications consume schemes before term arguments
are supplied. By-name references and selections consume their definition's binders
before observing its result; explicit arguments choose the site without also
instantiating the underlying reference. Separate definition signatures follow the
same rule, while independently quantified result annotations retain their schemes.
Functions and constructors share the bounded binder-instance cache. Stored
specializations and curried tails retain their groups. Allocation-count tests
cover unused specializations, repeated calls, by-name methods through nominal
views, and distinct invocation sites.

`DeclaredType.instances` carries a flat substitution through declared components.
Shared inferred bodies retain substitutions through deferred tuples, records,
callbacks, and closures. Nominal argument comparisons retain both endpoint
references and apply declaration/use-site variance, including substitution inside
nested function and nominal types. The explicit-binder recursive array acceptance
cases pass. Supplied function arguments receive input obligations while retaining
their declared output interface.

Replacing the remaining explicit-argument flags and positive-only member
conversion, reconstructed receiver contexts, inferred nominal member interfaces,
and general recursive alias environments still need integration. Omitted arguments
use source-owned inference holes; recursive hole contexts and omissions inside
alias bodies still need the contextual reference work described below. The
implementation order below remains the full design, not a claim that all its parts
are complete.
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
syntactic instantiation site.** This includes binders in inline annotations and
separate signatures. A site need not contain a term argument list:

| Operation on an uninstantiated scheme | Authoritative site |
| --- | --- |
| Explicit type application `f[T]` | That type application |
| By-name invocation `make` or `obj.make` | That reference or selection, unless its enclosing type application supplies arguments |
| Ordinary function application `f(x)` | The first term application |
| Constructor application | Its type application if explicit; otherwise its first term application, or saturated zero-list `new` |

This table concerns term-level instantiation. A type expression such as `Array[Int]`
inside an annotation does not invoke a computation or allocate a call-site group.
A reference to an ordinary function with parameter lists, such as `let g = f`,
does not invoke that function and may retain its uninstantiated scheme.

Memoize a complete group of parameter symbols using this key:

```text
(original definition, authoritative syntactic instantiation site)
    -> {original parameter -> instantiated parameter}
```

After instantiation, carry the group on the resulting value. Neither passing that
value through an alias nor supplying later term arguments instantiates the same
scheme again. In `f[T](x)`, the type application owns the group; in `make[T]`, do
not instantiate once at the reference and again at the type application. A
separately quantified result scheme is a different scheme, not a reappearance of
the definition's consumed binders.

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
Here the key uses the original definition and authoritative instantiation site. The
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

### Substitute at the occurrence before applying argument variance

There are two distinct steps in InvalML's `typeAndSubstType`:

1. Interpret an argument expression at the occurrence's polarity. A reference to
   a parameter bound to `in L out U` selects `U` at positive polarity and `L` at
   negative polarity. Function domains and written wildcard input parts reverse
   this polarity; function results and wildcard output parts preserve it.
2. For an unqualified nominal argument, apply the formal parameter's declared
   variance to that interpreted type. An invariant formal uses the same result
   for both parts. A written wildcard instead interprets its two explicit parts
   at their respective polarities and supplies its own variance.

In particular, the formal's `in` annotation does not itself choose the input
part of a substituted parameter. InvalML first evaluates `mono(t, pol)`, then
constructs the argument according to `tp.vce`. Nor should selecting a supplied
function type re-substitute it in the enclosing member's environment: it already
denotes a type in the supplier's context.

For example, with `Child <: Base`:

```mlscript
class Box[T](val item: T)
class Receiver[T] with
  fun accept(box: Box[T]): () = ()
// On Receiver[in Child out Base], accept expects Box[Child].
```

The `T` in the method input has negative polarity, so substitute `Child` first.
The invariant `Box` argument then has `Child` in both parts. Retaining the outer
`in Child out Base` pair inside `Box` would incorrectly introduce `Base` as an
output bound of an argument that originally contained only `Child`.

Conversely, in `use(f: Sink[T] -> Int)`, `T` has positive polarity: the method
input and callback input reverse it twice. For a receiver argument
`in (Base -> Int) out (Child -> Int)`, the invariant `Sink` argument must therefore
be the single type `Child -> Int`, in both parts.

[`newres/VarianceSubstitution.mls`](../hkmc2/shared/src/test/mlscript/newres/VarianceSubstitution.mls)
contains both passing examples and controls with the projected types written
directly. It also checks tuples, structural fields, declaration contravariance,
and the polarity reversal inside a written wildcard input.

`DeclaredType.positive` records the polarity for interpreting substitutions in
its source expression. It is independent of the direction of a later constraint.
Function domains and written wildcard input parts reverse this flag. Structural
field views retain it; nominal member lookup starts from the nominal arguments
already interpreted in the enclosing occurrence. Substituting a bound parameter
selects its part without replacing that part's original lexical environment.

When the pair is not yet available, `TypeShape.SelectedArgument` retains the
argument reference and the requested part. Both interface observations and
constraints follow that same part, including when it arrives later. The consumer
caches selections by argument reference and polarity; selecting an existing
selection returns it unchanged. Resolved parts are reused directly, except when
a missing wildcard part needs its original source for diagnostics. A forwarding
cycle which exposes no interface stops at the repeated selection, while retaining
subscriptions for later evidence.

For a fixed finite set of argument references, there are at most two cached
selection nodes per reference. Polarity likewise only doubles an otherwise finite
view domain; no parameter symbol or expanded type tree is allocated by selection.
`TypeRelationTest` checks delayed parts, cyclic selections, identity reuse, and
stable listener counts on relation replay. These are local bounds: they do not
establish the separate whole-graph bound for recursive binding environments.

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

For an ordinary implicit instantiation, use the stable `Term.App.resSym` as
application identity, rather than taking a site from the callee's marks. Marks can identify a function reference shared by
several applications:

```mlscript
let g = append
g(xs, First(1), 2)
g(ys, Second(2), 2)
```

These applications need distinct parameter instances. The two-array regression
following the recursive `append` block in `newres/MutableArrays.mls` checks this
case with different element interfaces.

An explicit term-level `Term.TyApp` needs its own stable site identity, memoized
by the original syntax node, never allocated afresh during observation. By-name
invocations use the source reference/selection's site. Resolving an explicit
application must choose that site before interpreting an underlying by-name
reference, so its implicit invocation cannot allocate a competing group.

For construction without explicit type arguments, use `Term.New.resSym` when it
consumes arguments or saturates a zero-list class; an unapplied constructor uses
its later first application. Canonicalize the constructor and class to the same
original owner. For an anonymous polymorphic annotation, the
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
`newres/PartialSignatures.mls` now pass. Existing
`DeclaredTypes.mls` examples selecting members from omitted arguments without any
supporting flow remain negative tests: a hole is inferable, not evidence of an
arbitrary member. `TypeShape.Hole` retains a source inference host, cached by the
type-use node and omitted formal parameter. Observation and constraint propagation
share the argument-completion operation, so they reach the same hole. Bounds can
arrive after an observation; an empty host emits no unknown candidate. Intentional
abstraction remains `TypeShape.Abstract`. Type validation rejects excess arguments,
including in unused annotations.

Result annotations and ascriptions constrain their implementations, allowing their
holes to receive evidence while their written fragments keep restricting the
interface. Exposure checking contributes unknown shapes only to missing output
parts of incoming values, including external callback results. It does not add
arbitrary lower bounds to written binders fixed by a partial application. These
unknowns represent real possible inputs and remain alongside local evidence.
`newres/InferenceHoles.mls` checks source/formal-position isolation, these annotation
boundaries, and exposed interfaces.

Two context cases remain explicit `:fixme`s in that worksheet. A recursive
`append(xs: Array, value, n: Int)` currently mixes the element interfaces of two
external callers, whereas the explicit-binder version has separate call-site
symbols. Holes must retain ordinary marked inference; copying the hole at each
call is not an acceptable repair. Also, with `type SomeBox = Box`, the hole in the
alias body is currently shared by both parameters of
`both(left: SomeBox, right: SomeBox)`, even though their alias-use references differ.
The contextual graph representation must preserve those uses without expanding
the alias or allocating more hole symbols. Neither case is covered by the passing
source-occurrence isolation test, which uses two directly written `Pair` annotations.

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

Explicit type application is an instantiation site, even before any term
arguments are supplied. For `let g = f[Int]`, allocate the definition's group at
`f[Int]`, attach `Int` to its parameter instance, and retain that map on `g`.
Later applications of `g` reuse the map. They still have their own value-flow
marks; sharing the type-parameter group does not make their term arguments or
results the same runtime value. Check type-argument arity at specialization,
including when the result is unused.

Without explicit type arguments, a function with parameter lists instantiates
when its first list is consumed. A curried tail retains that group for later
lists. By contrast, referencing a by-name function or selecting a by-name method
already invokes its body, so instantiate before observing its result. For example:

```mlscript
private fun make[A] =
  let cells = mut []
  (value: A) =>
    cells.push(value)
    cells.0
let shared = make
```

`shared` closes over one array allocated by the invocation at `make`. Its later
calls must all use that invocation's instance of `A`. Giving each call to
`shared` an independent `A` would treat one shared array as unrelated element
types. Separate expressions `let left = make` and `let right = make` are separate
invocation sites. `newres/InstantiationSites.mls` checks shared storage, independent
by-name method invocations, and rejection of an incompatible result selection
through both inferred and annotated closures. The annotated variant,
`make[A]: A -> A`, rejects `shared(First(3)); shared(Second(4)).second` (written on
separate lines in the test), since the second call returns the stored `First`.
A result annotation must not re-generalize the by-name definition's binder. The same rule applies to explicitly specialized
`make[T]`. Only a separately quantified result scheme retains its own binders,
subject to ordinary generic-body checking.

`SpecializedShape` retains the group consumed by a type application of an inferred
definition. Complete callable signatures remove their scheme when instantiated.
Both distinguish a consumed scheme from an open scheme carrying lexical captures;
later calls must not instantiate the consumed scheme again. The substitution is
retained through callback checking, tuple/record results, closures, and constructor
aliases. Elaboration defers observing the base reference of a type application
until its arguments are available, preventing a second by-name instantiation.

Constructors use the same site policy. `C[T]` and `new C[T]` instantiate at their
explicit type application, including when term arguments remain to be supplied.
Without explicit arguments, an unapplied `new C` waits for its first term
application; a saturated zero-list `new C` invokes construction at the `new` site.
Later lists and aliases reuse the selected group. Array spreads observe that
element parameter, including bounds inferred from inserted values.

`newres/StoredSpecializations.mls` covers independent specializations, deferred
record results, curried calls, and unused arity errors. Compiler-level allocation
checks assert that two explicit specializations allocate two groups even when
unused, whereas repeated calls through one specialization allocate only one group
for that scheme. By-name function/method cases, separate signatures, independently
quantified results, shared mutation, and specialization inside generic bodies are
also covered. Broader graph convergence remains a separate completion gate.

`newres/ConstructorInstances.mls` still contains two failing regressions.
Reconstruction with `class Box[T](val item: T) with { fun copy() = new Box[T](item) }`
must retain the receiver's view of `T` separately from the new constructor's view;
the first of two distinct receiver calls currently loses its resulting element
interface. Separately, this callback must receive the supplied input type:

```mlscript
class Item(val value: Int)
let callbacks = new mut Array[Item -> Int](0)
callbacks.push((x) => x.value)
```

The expected input of `x` is `Item`, but its member target remains unresolved.
`instanceBindings` still expands explicitly supplied class arguments into
positive interfaces. Simply replacing this conversion with `TypeShape.Parameter`
is insufficient: nested nominal comparisons can reach that parameter with no
outer constraint marks, even though the incoming value retains class and member
entries. The explicit-argument flag then fails to identify the supplied slot and
incorrectly treats the input as another output candidate. The shared reference
graph must retain the supplied endpoint and its context through those comparisons;
it must replace this conversion and the flag-based routing together. Both failures
also occur before constructor call-site instantiation; they are not accepted
behavior or reasons to change marks or allocate additional variables.

Pre-application observation of an inferred result is still missing.
`newres/StoredSpecializations.mls` retains this concrete regression:

```mlscript
class Item(val value: Int)
private fun identity[A](value: A) = value
private fun use[B](f: Item -> B): B = f(Item(9))
use(identity[Item]).value
```

This regression now returns `9`. `identity[Item]` itself supplies the authoritative
instantiation site. Checking it against `Item -> B` can therefore observe the
inferred result under `A -> A_specialization`, with `Item` already attached to
that instance. No call of the specialized value needs to have been observed.

This example does not require deferred views that map binders directly to
supplied type expressions. Use the existing finite map to parameter instances;
do not introduce that broader representation solely to repair this regression. Shared reference graphs remain necessary for compound
arguments and recursive environments, independently of this instantiation fix.

### Constraint propagation and implementation order

1. Preserve partial declaration/signature schemes and their original identities,
   including links to inferred portions. Distinguish inference holes from
   intentionally abstract types and variance wildcards. Add a
   consumer-owned cache of complete call-site instances, with origin links back
   to the declared binders. Select the authoritative site before observing the
   value: explicit specialization and by-name invocation consume the definition's
   scheme, and later applications preserve its group. The annotated by-name
   shared-storage regression and allocation-count tests now pass. Keep omissions
   source-owned; do not add mutable caches
   to symbols. Preserve `Forall` binders and their bounds instead of erasing them.
2. Transport the memoized substitution through callable and result views before
   expanding instance wrappers. Keep the existing marks for value flow and
   lexical captures. Separate generic-body checking witnesses from the symbolic
   constraints replayed in a call view. Verify delayed fields and returned closures.
3. Relate the resulting type references in both input and output positions,
   retaining their hosts, substitutions, and marks. Ordinary arguments contribute
   bounds; supplied types receive all obligations at their applicable polarity.
   Apply the InvalML variance rules above.
4. Complete supplied-argument references and replace explicit-argument suppression
   and the positive-only conversion in `instanceBindings` together. Functions
   and constructors share instantiation-site binder allocation and retain consumed
   groups; their remaining input/output obligations must use the same reference
   mechanism as nominal arguments and declared array interfaces.
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

### Type-reference scope audit

The remaining graph work has a concrete termination regression in
`newres/TypeGraphTermination.mls`:

```mlscript
type Chain[A] = {value: A, next: Chain[Array[A]]}
private fun walk[A](chain: Chain[A], n: Int) =
  if n > 0 then walk(chain.next, n - 1) else ()
```

This non-regular variant still overflows the stack without any call to `walk`.
With `checkMarkPaths` enabled it reports repeated exits first, so its failure is
not evidence only of growing argument environments. The regular variant with
`next: Chain[A]` and the finite selection `chain.next.next.value` now pass,
including with mark checks enabled. Both constraint expansion and mark paths need
validation independently of runtime recursion depth.

The approved correction distinguishes these operations:

- Expanding a type alias substitutes references to its arguments in its source
  type graph. The alias declaration introduces no value invocation. Keep each
  argument's caller context; do not add a value entry/exit for the alias's own
  lexical qualification.
- Selecting a structural record type's field follows its written type reference.
  `RcdField.make` creates a synthetic captured definition for value-field lookup;
  that synthetic value boundary must not be introduced by a type-field projection.
  Keep the field symbol as the resolved selection target.
- Function and class captures still cross actual value scopes and use the existing
  mark operations. These paths must remain on references to captured parameters,
  even when aliases or structural fields forward them.

This approval concerns which operations cross a value scope, not permission to
truncate repeated marks, widen an alias, or allocate more inference variables.
The interpreter now forwards alias qualifications without a value capture, and
structural field declarations retain their written type without a synthetic
capture/exit. Worksheets cover regular recursion, finite parameter permutations,
mutually recursive aliases, function-local aliases, and structural callbacks.
An imported recursive alias is checked through two independent consumer modules.
These cases pass with mark checks enabled. A graph-level structural cycle test
also checks late bounds and verifies that repeated relations add no listeners or
parameter instances.

The class-local alias case remains a `:fixme`: projecting the result of
`Box[A].get(): Slot`, where `Slot = {item: A}`, loses the correspondence between
the method's scope and its receiver's scope. This also fails without the scope
correction. Closed type interfaces need their deferred child references observed
in the appropriate context; adding an entry to every closed interface instead
breaks regular alias traversal. The whole-graph proof must address this context
transport, and existing repeated-mark failures in generic array-method paths,
not just the now-passing regular alias examples.

The expanding alias needs the regularity diagnostic described below. The regular
argument-reset regressions now pass after projecting `DeclaredType.bindings` onto
the source type's dependencies. A local nominal annotation whose constructor
field refers to an enclosing function parameter still exposes the receiver-context
failure; it has its own regression beside the class-local alias case.

The same graph audit must distinguish an open definition template from an already
interpreted reference. In `Box[T].copy() = new Box[T](item)`, the source `T` in the
supplied argument belongs to the receiver, while the constructed result refers to
the new site's instance of `T`. One merged map cannot choose both meanings after
the argument reference has been interpreted in the wrong view. Observe saved
source-graph operations with their caller references before attaching the callee's
instance map. Do not implement this by rerunning `resolveNew` over arbitrary syntax:
legacy constructions can have value shapes without a new-resolution producer,
and completed reference targets must remain immutable. A saved graph operation
must retain its selected definition and interpreted argument references.

### Receiver-context investigation

Two current regressions isolate missing scope transfers. Both fail before any
concrete type mismatch is relevant:

```mlscript
class Item(val value: Int)
private fun local[A](value: A) =
  class Local(val item: A)
  let box = (new Local(value) as Local)
  box.item
local[Item](Item(7)).value
```

`Local.item`'s annotation captures the enclosing `A` into the class scope. The
nominal view's member projection does not leave that scope. When `local` returns,
the interpreter tries to cancel the function exit against the still-pending class
entry, triggering the scope assertion. The regression is the final block of
`newres/TypeGraphTermination.mls`.

```mlscript
class Item(val value: Int)
class Box[A](val value: A) with
  type Slot = {item: A}
  fun get(): Slot = {item: value}
(new Box[Item](Item(4))).get().item.value
```

Here the reference to `Slot` captures the type into `get`'s scope. The interpreter
produces an unmarked `RecordTypeShape`, and its current capture rule only enters
already-marked shapes. The method entry is therefore lost before the deferred
field is inspected. The method exit then meets `A`'s class entry instead. This is
the existing class-local alias regression in the same worksheet.

Simply entering every compound interface is not a valid general correction.
For `Chain[A]` inside a function, the type template `Chain` can come from an outer
scope while the supplied argument `A` is already in the function's scope.
Transporting the fully substituted interface moves both, introducing a second
entry for the supplied argument. Captured template references and supplied
argument references must retain their separate contexts.

**Proposed representation extension, awaiting review:** use contextual references
for declared substitutions and deferred member types, generalizing the existing
`ContextualType` relation endpoints. Compose class/method transfers on these
references before expanding their inferred shapes. A nominal member projection
must explicitly leave its declaring class's scope; arguments supplied outside
that scope must retain their corresponding entry. A compound result must keep
the transfers needed by its deferred components. Apply the same reference
transport in input and output constraints, including callback arguments.

The extension must reuse original source references, canonical binder instances,
and existing mark normalization. Each transported endpoint must contain a
normalized path rather than a list of transport operations or nested wrappers.
Repeated transport of a recursive interface must return the same endpoint key.
This preserves the existing finite-source/finite-instance argument only if mark
paths obey the no-repeated-boundary invariant and regular type bindings remain
bounded; neither condition may be assumed merely because the two examples pass.
Tests must also retain independent receivers/callers, imported-graph isolation,
recursive aliases, and the input obligations of supplied callback types.

### Regular structural types

The proposed restriction is that unfolding a structural type must admit a finite
graph of distinct type components, with recursive occurrences represented by
back-edges. A finite alias definition alone does not establish this property:

```mlscript
type Chain[A] = {value: A, next: Chain[A]}
type Growing[A] = {value: A, next: Growing[Array[A]]}
```

`Chain[Int]` repeats the same interface and can be represented by a cycle.
`Growing[Int]` exposes successive `value` types `Int`, `Array[Int]`,
`Array[Array[Int]]`, and so on. It is non-regular and should be diagnosed rather
than expanded indefinitely or silently approximated. The third block of
`newres/TypeGraphTermination.mls` currently records this latter failure as a stack
overflow; it is no longer an acceptance case for unrestricted structural recursion.

Regularity is not a requirement that recursive arguments be textually unchanged.
For example, `{value: A, next: Alternating[B, A]}` as the body of
`Alternating[A, B]` has a finite two-state unfolding. Mutually recursive aliases
and finite changes of arguments must also be considered. The precise check,
including how it handles aliases and inferred holes, remains a design review
item. It must terminate on rejected inputs too; waiting for an unfolding cache to
stop growing is not a decision procedure. Do not impose a depth limit.

Growth along one recursive edge is not sufficient to reject a type:

```mlscript
type Left[A] = {value: A, next: Right[Array[A]]}
type Right[B] = {value: B, next: Left[Str]}
```

Starting from `Left[Int]` visits `Right[Array[Int]]`, then settles into the cycle
`Left[Str]` / `Right[Array[Str]]`. The argument reset breaks the expanding
dependency. `TypeGraphTermination.mls` includes this finite mutual unfolding as
an acceptance case alongside the parameter-permutation and unused-argument cases.

There is also a representation obligation for accepted types. Currently
`DeclaredType.bindings` is a recursive map of `DeclaredType` values, and the whole
reference is used as a view-cache key. `declaredType` substitutes a directly bound
parameter and projects compound references onto their free binders. A genuinely
expanding dependency, such as repeatedly binding `A` to `Array[A]`, can still build:

```text
E0 = {A -> Int}
E1 = {A -> (Array[A], E0)}
E2 = {A -> (Array[A], E1)}
...
```

The source expression and binder identities stay fixed while the environments
grow. Removing synthetic value-scope crossings does not bound these environments.
The regular argument-reset regression in `TypeGraphTermination.mls` is:

```mlscript
type Reset[A] = {value: A, next: Reset[Int]}
fun read(chain: Reset[Str]): Int = chain.next.next.value
```

The unfolding has only the `Reset[Str]` and `Reset[Int]` interfaces. Compilation
now terminates: the closed `Int` reference has no free binders, so it retains no
previous binding map. The same holds for a fixed compound argument `Array[Int]`.
Accepted regular types need finite reference keys and shared recursive edges,
not a fresh nested environment on each visit.

Dependency pruning alone does not identify transparent forwarding aliases. This
additional regular regression still overflows:

```mlscript
type Identity[X] = X
type Chain[A] = {value: A, next: Chain[Identity[A]]}
fun read(chain: Chain[Int]): Int = chain.next.next.value
```

The argument continues to denote `Int`, but successive cache keys retain
`(Identity[A], previous-environment)`. Here `A` is genuinely a free binder of the
argument expression, so discarding unused bindings cannot help. A regularity
check must not classify the transparent alias application as a growing type
constructor. Canonical references must resolve forwarding through aliases and
their substitutions, respecting argument variance and occurrence polarity.
This needs to work through multiple aliases and parameter permutations, with a
finite source-graph guard for unproductive alias cycles. Special-casing a directly
written identity alias would not establish the required representation bound.
`TypeGraphTermination.mls` records this case separately from non-regular array
nesting and from the receiver-context failures.

The implemented dependency analysis operates on source `TypeResolution` nodes.
An edge forwards the child's free binders, excluding those bound by an alias or
quantifier. An applied alias forwards an argument's dependencies only when its
body depends on the corresponding formal. All equations are monotone over the
finite set of source binders, so iteration reaches a least fixed point. This also
accepts `Loop[A] = {value: Int, next: Loop[Array[A]]}`: no observable component uses
`A`, and the cycle alone cannot introduce that dependency. Nominal arguments
remain relevant regardless of whether the class's members mention them.

Nominal declarations conservatively retain all enclosing explicit type binders.
Elaboration records this immutable set before elaborating members, including for
legacy exporters. Consumers read it from the declaring graph. This preserves
parameters used through nested aliases, member annotations, or inferred member
types without making dependency analysis wait on member inference. The class's
own parameters are supplied by its type application, rather than treated as free.

No summary is finalized while a reachable source type lacks a target. Interface
observation, constraints, and hole exposure wait on shared dependency hosts;
when the target arrives, each observer projects its own saved environment. There
is at most one waiting subscription per source/dependency pair. Completed summaries
are immutable; inference hosts and waiting callbacks use the usual consumer-private
graph copies. Valid written types have one target, while synthesized argument,
selection, and inferred-value nodes retain their own references and do not read
an ambient binding map. The forward-alias worksheet and a graph-level recursive
tuple test check delayed discovery, independent substitutions, and replay without
additional listeners or parameter instances.

This bounds dependency analysis and eliminates irrelevant environment growth.
It does not yet establish the full representation bound for every regular type,
or diagnose non-regular structural expansion; those remain completion obligations.

Keep structural alias unfolding distinct from inferred constraints at a recursive
generic function call. The latter reuses a site's parameter symbol and can add an
edge from the source `Array[A]` expression to that symbol without eagerly
substituting its accumulated bounds. A regularity restriction on written
structural interfaces does not by itself establish or replace the finite-domain
argument for that constraint propagation.

### Fixed points and implementation checks

There are at most as many allocated parameter instances as the sum of each
reachable definition's binder count over its syntactic instantiation sites.
Explicit type applications and implicit by-name invocation sites are finite source
occurrences too; observing them repeatedly does not add sites. Source hole
nodes and written type/term nodes are finite independently of recursive visits.
View substitutions range over the finite original and instantiated binders in
lexical scope. With the existing no-repeated-boundary mark invariant, their
normalized contexts also range over a finite domain. These facts bound the set
of memoized views and endpoint pairs **provided** structural interfaces satisfy
the regularity restriction, compound arguments remain shared graph edges and no
cache key includes a growing substitution or capture history.
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

Constructor views retain source type-argument nodes and flat binder maps, not
expanded argument candidates. Binder allocation must use the original class and
the authoritative instantiation site. Constructor argument subscriptions are
memoized before observing their arguments. `TypeInstantiationTest` checks the
site counts above, including reuse across curried tails and saturated zero-list
construction. `typeApplicationSite` caches one site identity per source `TyApp`
node across activation views. It allocates neither a new source occurrence nor a
type-parameter group on repeated observation; by-name references reuse their
existing reference/selection site identity. These local allocation checks do not establish
the remaining whole-graph alias bound or repair reconstructed receiver contexts.

For omitted arguments, each source type-use/formal-position pair allocates one
`TypeShape.Hole` host. No recursive traversal or call allocates a parameter symbol
for it. `TypeRelationTest` checks reuse across repeated observations, empty hosts
waiting for evidence, cyclic constraints with stable listener counts, and private
bounds in separate importers sharing the same source identity. This bounds hole
allocation and replay; it does not establish the missing context precision for
recursive holes or alias-body omissions noted above.

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
  two applications through an uninstantiated ordinary function alias obtain
  distinct instances, whereas calls through one explicit specialization reuse
  its group. By-name references/selections instantiate before exposing their
  results, without re-generalizing shared mutable state. An inner site shared by
  different enclosing activations remains distinguished by marks.
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
