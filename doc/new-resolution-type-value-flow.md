NOTE: This document was written by Codex Astra and has not been deeply reviewed;
it is not meant to be official documentation and
is in fact likely to contain parts that are unintelligible to readers who lack sufficient context.


# Instance types and parameter constraints

This internal reference describes the current type-flow representation in new
resolution. User-facing rules are in the [language reference](reference.md#resolution-interfaces).
[Deferred improvements](new-resolution-future-work.md) cover receiver reconstruction,
inferred member signatures, omitted-argument contexts, and regularity precision.

## Type arguments and instance bounds

Supplying `Int` as the type argument for a contextual parameter `A` affects both
its input and output uses:

```text
L <: A    requires    L <: Int
A <: U    requires    Int <: U
```

An ordinary integer argument to `x: A` contributes only a lower bound. For
`pair[A](x: A, y: A)`, integer and string arguments contribute two lower bounds;
neither argument must satisfy the other's type.

If two distinct supplied types `Int` and `Str` reach the same activation of `A`,
each obligation applies to both. Resolution also approximates an upper union by
constraining both components: `L <: A | B` propagates into both `A` and `B`. A lower
intersection contributes every component separately when inspecting its interface
for constraints: `L1 & L2 <: R` installs both `L1 <: R` and `L2 <: R`.
For example, `(Int -> Int) & (Str -> Str) <: A -> B` constrains both arrows,
producing `A <: Int`, `Int <: B`, `A <: Str`, and `Str <: B`.
These rules collect possible resolution targets without solving
alternative constraint sets or forming products of intersection candidates.
They deliberately approximate type inference; diagnosing concrete incompatibilities
such as `Str <: Int` belongs to type checking, not resolution.

This distinction also applies to separate function signatures and callback
layouts. Skipping an uncertain compatibility check must not skip its flows.
Every callable component contributes its domain to the implementation parameters,
and later curried lists remain connected even when an earlier layout differs.
Each implementation parameter has a shared annotation endpoint that accumulates
these components; replacing it with the last component would disconnect earlier
constraints. Matching positions stay precise. Uncertain middle positions receive
the union of their possible inputs, including typed rest elements. Rest slicing
may widen lengths, but retains the deferred types of every possible element.

## Instance wrappers and interface observations

`InstanceShape(DeclaredType)` describes an instance of a type. Parameter/result
annotations, ascriptions, and annotated fields retain this wrapper until lookup,
application, or destructuring requests an interface through `listenInstanceViews`.
The type itself stays in the `TypeResolution`/`TypeShape` graph. A written interface
restricts observation even when more specific implementation values reach it.

Member lookup merges the fields of record intersections. Constraint inspection
instead observes each component independently, including through aliases, type
parameters, and inference holes. The type-view cache distinguishes these two
observations so inferred arguments cannot change the interface of an annotation.

A `DeclaredType` contains:

- A source `TypeResolution` node.
- Bindings from original formals to contextual argument references.
- A flat substitution from original binders to canonical call-site instances.
- The lexical polarity at which to interpret substitutions.

An interface view does not replace these references with their current candidates.
Late constraints must remain connected to the same endpoints. Nominal views retain
symbolic parameter endpoints for constructed receivers, including supplied arguments.
Suppliedness is recorded on the canonical parameter instance; marks choose which
activation's supplied bounds receive an obligation. An input obligation does not
add its implementation shape to a supplied parameter's output interface.

## Finite call-site instantiation and marks

Each explicitly declared binder is instantiated once per original definition and
**authoritative syntactic instantiation site**. Inline binders and separate
signatures follow the same policy:

| Operation on an uninstantiated scheme | Authoritative site |
| --- | --- |
| Explicit term-level type application `f[T]` | That type application |
| By-name invocation `make` or `obj.make` | The reference or selection, unless an enclosing type application supplies arguments |
| Ordinary application `f(x)` | The first term application |
| Constructor application | Its explicit type application; otherwise its first term application, or saturated zero-list `new` |

An annotation such as `Array[Int]` is a type expression, not an invocation.
An ordinary reference to a function with parameter lists can retain its scheme.
A by-name reference has already invoked the computation: retaining its consumed
scheme and independently instantiating it at later uses would misrepresent shared
state returned by that invocation.

The cache maps `(original definition or source scheme, syntactic site)` to the
complete group of parameter instances. It contains no supplied types, incoming
bounds, marks, or instantiated-definition identities. Install a group before
subscribing to constraints so reentrant observation finds it. Recursion reuses
the group; marks distinguish enclosing activations of a shared inner site.
No other observation, projection, or recursive traversal allocates fresh binders.
`App.resSym`, `New.resSym`, and reference/selection sites provide stable identities;
`typeApplicationSite` memoizes one identity per original `TyApp`. Structural
field constraints likewise reuse one projection site per source field across
recursive and activated views (`TypeGraphProjectionSites.mls`). Class and
constructor views use the same original owner. An anonymous polymorphic annotation
uses its source scheme, and each alternative of an overload has its own owner.

`TypeShape.Polymorphic` and `DeclaredTypeParameter` retain the original binders and
their bounds. Inputs, results, and nested callbacks receive the site's substitution
before interface expansion. The same substitution is applied to bounds, including
captured enclosing binders. Instantiation connects `lower <: instance <: upper`
after recording explicit supplied arguments, so a lower bound cannot widen a
supplied interface. By-name invocations install these relations when their scheme
is consumed. Recursive and dependent bounds share the existing relation graph.
Using an upper guarantee as an interface for an unconstrained result or a generic
checking body remains a [design issue](new-resolution-future-work.md#upper-bound-interfaces).
Enclosing binders remain lexical captures, not binders of the nested definition
being instantiated.

### Partial application and explicit specialization

`f[T]` consumes its scheme even before a term application occurs. `SpecializedShape`
retains the group for an inferred function; an instantiated complete callable view
removes that scheme. Stored aliases and remaining curried lists reuse the group.
A separately quantified result retains its independent scheme.

For ordinary explicit applications, lexical captures are applied to the callable
before binding caller-supplied arguments. By-name invocation needs the arguments
before observing its result: the resolver records the reference's captures and
rebases those arguments through the ordinary mark operations into the invocation.
It records that invocation so its result is not specialized a second time.
Arity checks also apply to unused specializations.

## Variance and substitution

Follow InvalML's [`typeAndSubstType`](../hkmc2/shared/src/main/scala/hkmc2/invalml/InvalML.scala)
and [`constrainArgs`](../hkmc2/shared/src/main/scala/hkmc2/invalml/ConstraintSolver.scala).
Its [`TypeArg`](../hkmc2/shared/src/main/scala/hkmc2/invalml/types.scala) supplies
input and output parts:

| Argument | Input part | Output part |
| --- | --- | --- |
| `S` | `S` | `S` |
| `in T` | `T` | `Any` |
| `out U` | `Nothing` | `U` |
| `in T out U` | `T` | `U` |

Nominal declaration variance applies to an unqualified argument. A written wildcard
supplies its own parts and overrides declaration variance. Comparing actual `a`
with expected `b` installs `a.output <: b.output` and `b.input <: a.input`.
Missing wildcard parts are actual top/bottom types, not inference holes.

A subclass contributes the arguments of the requested nominal ancestor. Each
parent step preserves the child's binder substitution and the parent's scope
marks before installing both variance directions. This applies to constructed
receivers and declared nominal views, including multiple inheritance steps and
captured enclosing binders (`InheritedTypeArguments.mls`).

A nominal annotation's parent is interpreted inside the subclass instance scope,
whereas the annotated value and its supplied type arguments are outside it.
Capture the arguments used by the parent before substitution, and leave the
subclass scope before applying the value's caller path. `nominalParent` shares
that exit between ancestor constraints and inherited member lookup. Constructed
receivers already carry the exit in their constructor context.

### Compose substitution polarity through type arguments

A formal bound to `in L out U` selects `U` positively and `L` negatively.
Function domains and type-argument input parts reverse polarity; results,
structural fields, and type-argument output parts preserve it. Write `I_p(S)` for
interpreting `S` at polarity `p`. For an unqualified argument `S`, an invariant
formal therefore retains both
`I_not-p(S)` as its input and `I_p(S)` as its output. These interpretations can
differ when `S` contains substituted parameters. Declaration-site `in` retains
the input interpretation and supplies `Any` as the output; declaration-site `out`
retains the output interpretation and supplies `Nothing` as the input. Written
wildcards use the same polarity composition and override declaration variance.

For example, with `Child <: Base`:

```mlscript
class Box[T](val item: T)
class Receiver[T] with
  fun accept(box: Box[T]): () = ()
```

On `Receiver[in Child out Base]`, `accept` expects `Box[in Base out Child]`.
The domain reverses polarity, and `Box`'s input part reverses it again, selecting
`Base`; its output part selects `Child`. Selecting `Child` once and using it for
both parts would be unsound: a `Receiver[Base]` can be viewed through this receiver
type, but an invariant `Box[Child]` is not a `Box[Base]`. A receiver that writes its
stored `Base` into an `Array[T]` exposes the runtime failure of that rule.

Resolution propagates these obligations into inferred arguments and preserves
explicitly supplied interfaces. Checking concrete subtype compatibility belongs
to the later type checking phases: an `Array[Child]` annotation remains the read
interface during resolution, while the incompatible call must be rejected by the
type checker. The annotated-array case in `VarianceSoundness.mls` resolves
normally and, with type checking disabled, records the unsafe runtime write.
InvalML regressions check rejection of the corresponding concrete mismatch.

Alias formals start a new substitution scope. References to already-bound
enclosing parameters inside an argument still select their bounds according to
their position in the enclosing signature. A fresh, unbound parameter remains
itself. Apply declaration variance (or the written wildcard) to that interpreted
argument, then select its endpoint according to its occurrence inside the alias body.
For `type Source[out T] = {item: T}`, both `Source[A]` and
`Source[in Nothing out A]` expose `A` in `item`, including when the application
occurs in a function domain. The enclosing domain affects the interpretation
of `A`, not whether the occurrence of `T` in `{item: T}` selects its output.

The implementation keeps the alias body's enclosing polarity so captured outer
binders retain their interpretation. It therefore reverses only the new formal
bindings' stored endpoint pairs when that polarity is negative. A globally
negative occurrence of `T` then selects the original output endpoint, while a
further domain reversal inside the alias selects the original input endpoint.
This also keeps `Identity[A]` equivalent to `A` in both polarities.
Nominal applications retain their composed argument pairs directly: member
signatures subsequently interpret them from the member's positive interface.
`TransparentAliasPolarity.mls` covers shorthand and explicit projections;
`VarianceAliases.mls` covers captured binders and nested identity aliases.

`DeclaredType.positive` records this lexical polarity, independently of a later
constraint's direction. `TypeShape.Wildcard` retains written parts;
`TypeShape.Argument` retains both contextual argument parts.
Neither transplants supplied syntax into the callee's binding environment.

`TypeShape.SelectedArgument` saves one requested part for a scalar occurrence when
the argument is deferred. Both subsequent constraint directions use that same
selected type; an invariant argument makes separate selections for its two parts.
Selections are cached by argument reference and polarity; selecting an existing
selection is idempotent. Forwarding cycles retain subscriptions but stop repeated observation.
For a fixed argument-reference set, selection adds at most two nodes per reference.

### Iteration and synthesized applications

Resolution is a best-effort check, not a type checker. Implicit spread observations
must propagate known flows without rejecting an opaque or inconvenient protocol.
They preserve every union and intersection component. Member lookup combines
an intersection's interfaces, while constraints inspect each component independently. An unknown alternative joins the known elements; it never
replaces them. Definitively completed iterator results supply no element, while
a missing or unknown `done` still permits observing `value`.

Each non-tuple spread operand owns one `IterationFlow`: stable sites for selecting
`Symbol.iterator`, calling it, selecting and calling `next`, and reading `done`
and `value`, plus one deferred element host. These observations use ordinary
member scope transport and call instantiation. The implicit zero-argument calls
omit compatibility diagnostics but retain argument and result flow. Tuple
construction sees one unknown-length segment per operand, regardless of the
number of incoming iterator or element alternatives. This prevents products of
alternatives from multiplying through recursive spreads. Imported producers keep
their canonical sites while publisher storage remains local to each consumer.

Arrays use this same protocol through the prelude's symbol-keyed method. Direct
Array element-bound observation remains useful for array patterns and rest
constraints, where the operation describes Array storage rather than iteration.
The `appliedTypes` table interns synthesized applications by constructor symbol
and contextual arguments, sharing the mechanism for `Array[T]` and `Awaited[T]`.
It reifies symbolic argument references before observation; caching their current
values instead would lose later bounds and caller-specific substitutions.

## Shared bodies and contextual constraints

The inferred body is a shared graph. Instantiated views carry flat original-binder
to instance-symbol substitutions through deferred tuples, records, callbacks, and
closures. They do not copy expanded argument candidates into a new body graph.
Shape substitution is memoized so repeated observations reuse aggregate identities.

`NewResolver.shapeSupport` determines which ambient type binders a value can
observe. The elaborator records lexical binders before installing listeners;
constructed instances and partial applications also need their declaration's
own binders. Synthesized aggregates include the support of their contents.

Instance bounds and inferred hosts contain templates written at their source
sites. Support is closed over those sites, including instances retained by
nested values. `projectType` removes irrelevant retained bindings; `project`
selects additional ambient bindings, preserving existing captures. An unknown
scope retains every binding. The analysis follows the finite source graph,
never live inference bounds. Applied type-argument counts are recorded when the
application is interpreted so dependency summaries do not depend on observation
order.

Activation environments are not projected: they select which body's events a
listener accepts, independently of what the delivered value can observe.

### Value views, consumed schemes, and activation events

The similarly named forms in
[`Shape.scala`](../hkmc2/shared/src/main/scala/hkmc2/semantics/Shape.scala)
answer different questions. A **scheme** is a callable's explicitly quantified
binders and their bounds. Consuming it chooses the canonical parameter instances
for an authoritative instantiation site; it does not imply that a term argument
list has been applied.

| Form | Meaning | How it is consumed |
| --- | --- | --- |
| `ContextualShape(source, instances)` | Observe a shared value using these bindings for references inside it. This does not consume the value's own generic scheme. | Member/body observation uses the substitution; `shapeParts` extracts it before application. |
| `SpecializedShape(declaration, arguments, instances)` | This declaration's scheme has already been consumed by explicit type application. Retain its supplied type references and chosen instance group. | `shapeParts` retains the supplied arguments, so `appShape` reuses the consumed group. |
| `ActivatedShapeEvent(value, instances)` | Deliver an inference event to operations running in this body activation. The enclosed value retains its own, independent substitution. | `listen` checks compatibility, unwraps the envelope, and invokes the receiver in that activation. |

All three `instances` fields map original binders to `TypeParameterInstance`
symbols, but the first two describe the value, whereas the third describes the
receiving operation. `ContextualSymShape` retains a value's substitution while
an overload remains a `SymShape`, before selection produces a term shape.
`ActivatedShapeEvent` accepts either a term shape or a symbolic shape as its payload.

For a schematic nested definition:

```text
outer[A](a: A) defines inner[B](b: B) = (a, b), and returns inner.
```

The returned `inner` captures an instance of `A`; its own `B` remains quantified.
A contextual view retains the captured `A` without selecting an instance for `B`.
Two later calls can instantiate `B` at their respective sites. Treating every
contextual view as specialized would prevent that instantiation.

Conversely, in `let g = f[Int]`, the type application has already consumed `f`'s
scheme, even if `g` has not received term arguments. `SpecializedShape` preserves
that fact for an inferred declaration. Subsequent calls through `g` or its aliases
reuse the chosen group. Treating this as only a contextual view would let
`appShape` instantiate the declaration again. A complete annotated
`CallableTypeShape` records the same transition differently: `instantiateCallable`
substitutes its parameter/result references and clears `scheme`. Remaining curried
lists retain those references; a separately quantified result has its own scheme.

The activation envelope is independent of both cases. Suppose a recursive
`f[A]` passes a value mentioning its caller's `A` into another call of `f`.
Write `A@p` and `A@q` for the instances chosen at two static sites (these are
explanatory names, not additional runtime identities). The incoming value must
still refer to `A@p`, while operations on the callee's shared body run with
`A -> A@q`. Schematically, delivery can therefore carry:

```text
ActivatedShapeEvent(
  ContextualShape(value, {A -> A@p}),
  {A -> A@q})
```

Replacing either map with the other would confuse the incoming value's type
references with the callee's parameters. Marks still distinguish lexical
activations when recursion revisits the same static site; these substitutions do
not replace, cancel, or otherwise change mark operations.

`publishViewed` first applies the value substitution with `instantiateShape`,
then `publishActivated` records the current `NewResolverState.instances` on the
event. `listen` accepts an event when its map and the requested activation agree
on every shared key; absent keys do not conflict. A source listener with an empty
requested map therefore accepts all activations. On delivery, the receiver runs
with the combined compatible activation maps, while the enclosed value keeps its
own references. `NewResolverState.withInstances` shares consumer hosts, and
`inGraph` preserves the incoming activation when invoking an imported listener.
Publishers store `ShapeEvent`, a shared base with two alternatives: an ordinary
`Shape` or an `ActivatedShapeEvent`. The envelope is not a `Shape` or `TermShape`,
so it cannot enter member lookup, application, or mark transport. Its payload is
a `Shape`, preventing nested event envelopes. Semantic listeners receive shapes
only after dispatch. Ordinary shapes remain unwrapped when no activation is
attached; dispatch contextualizes those values using the observing state.

Event equality includes both the payload and activation. Repeated publication of
one event is deduplicated, while the same shape in distinct activations remains
separate. Publisher replay and imported-host copying retain the complete events;
they do not replace saved activations with the state active during replay.

### Related interfaces and representation invariants

The view normal form is enforced by the Scala types. `CoreShape` excludes
`ContextualShape` and `SpecializedShape`, and `MarkedShape[T]` retains its core's
type parameter. `AppShape.receiver` has type
`CoreTermShape = CoreShape | MarkedShape[CoreShape]`: an application cannot contain
a contextual or specialized receiver, even beneath marks or earlier applications.
`ContextualShape.source` accepts only the shapes that defer substitution through
a view (`AppShape`, `NewShape`, `DefnShape`, `BaseShape`, and `IntroShape`). It
cannot contain another view, a marked shape, or a shape that stores substitutions
directly. `SpecializedShape.declaration` is a `DefnShape`.

The symbolic counterpart follows the same rule: `ContextualSymShape.source` is
a `CoreSymShape` (plain or declared), so it cannot wrap another contextual symbol.
`CallableTypeShape.paramLists` is a `NELs[DeclaredParams]`: every callable view
has a next argument list, even when that list itself accepts zero arguments.
Consuming the last list exposes the result instead of constructing an empty
callable view. Mapping parameter types preserves nonemptiness with `ne_map`.

Value captures and body activations use `TypeSubstitution`, which wraps an
immutable map with a cached hash. Its constructor derives
each key from the instance's original binder. `withOverrides` combines two valid
substitutions with the right operand taking precedence, `without` removes
shadowed binders, and `restrictTo` retains only the binders in a view's support.
These operations preserve the substitution type; arbitrary map updates do not.
This rules out mismatched binder/instance pairs without runtime validation
at every `DeclaredType` construction.

Consequently, `shapeParts` can decode one outer marking and one view with an
exhaustive match. It returns a `CoreTermShape`, its captured instances, and any
consumed type arguments. It preserves the application chain: peeling applications
would forget consumed term lists and could mistake a constructed object for a
constructor. Application, callback checking, constructor lookup, and constructor
patterns share this decoder. `ShapeViews.mls` exercises nested captures,
specialized curried values, callback constraints, and constructor-pattern controls.

These roles must also be distinguished from interpreting an annotated instance:

| Form | Role |
| --- | --- |
| `InstanceShape` | Preserve a `DeclaredType` reference in a value constraint, including its input and output uses. `listenInstanceViews` interprets it when an operation requests an interface. |
| `NominalInstanceView` | Expose a nominal type's declared members and inherited interface with their argument bindings. |
| `RecordTypeShape` | Expose a structural annotation's declared fields and their argument bindings. |
| `CallableTypeShape` | Expose a declared calling interface. `scheme` records whether quantified binders remain available for instantiation. |

`ContextualShape` is the general deferred value view, not a mandatory wrapper
around every substituted shape. Tuples and records store their substitutions
directly; `InstanceShape` stores one inside its `DeclaredType`; declared interfaces
substitute their references. `instantiateShape` centralizes these cases and
memoizes their results. Applying another substitution composes flat maps rather
than nesting contextual wrappers. Entries already captured by a value take
precedence over a later observation's map. For an open `CallableTypeShape`, its
own quantified binders are excluded from capture substitution.

The semantic requirements are independent value and activation substitutions,
and an explicit distinction between open and consumed schemes. The first two
value forms express scheme status separately; the event envelope belongs to the
publisher protocol and shares no value operations with them.

Keeping both maps does not itself introduce a chain of environments. Their keys
are original binders and their values are canonical instance symbols, not further
substitutions. `withInstances` reuses a fixed base state; `listen` removes the event
envelope before handing its value to the operation. For a fixed finite set of
binders and instantiation sites, there are finitely many such maps and map pairs.
This is a local bound, not a proof of termination of the entire type graph; see
[canonical references and termination obligations](#canonical-references-and-termination-obligations).

### Checking witnesses and constraint edges

Generic bodies also receive a checking activation containing `RigidTypeShape`
witnesses. Those witnesses enforce generic opacity even in private/non-strict
code. Interface observation sees an unknown interface; call-site inference must
not copy a checking witness into its bounds.

`constrainTypes` memoizes directed pairs of `ContextualType` endpoints before
installing subscriptions. Invariant arguments install both directions. A parameter
receives a symbolic instance wrapper; structured and concrete endpoints retain
listeners for future bounds. Delivery before and after edge creation must agree.
Relation replay adds no candidates, listeners, or parameter instances.

## Scope transport

See [Lexical paths in resolution](new-resolution-scopes.md) for the scope-tree
model, reduction proof, and producer obligations. Syntactic captures and qualified
type selections share `TypeShape.Reference`; both retain the declaration's
endpoint before the enclosing substitution is applied.

`ContextualType` pairs a reference with an ordinary normalized mark path.
`transportType` uses the same mark operations as value flow and
flattens existing contextual nodes before interning the endpoint; references contain
one normalized path, not nested transport histories. `inverseMarks` reverses
directions for constraint transport; it is not a mathematical inverse
on candidates. A wildcard exit can consume an entry carrying a call-site ID.
Re-entering without an ID does not restore it. Exit followed by entry must not be
cancelled as an identity, including on deferred references.

The relevant scope crossings are:

- Function/method entry and exit, and lexical captures of enclosing definitions.
- Nominal member projection: capture argument references into the class and exit
  the class when publishing its selected member view. Inherited members also exit
  the class through which they are selected, since the parent reference is
  captured into that class.
- Constructor invocation: use the same instance boundary for its class and
  constructor, including later parameter lists.

`Marks` stores the most recent crossing first. `shape.exit(path)` applies the
tail before the head; a list of path fragments is applied from left to right.
`shape.enter(fragments)` reverses both directions and fragment order. Thus
`shape.enter(p :: q :: Nil)` agrees with `shape.enter(q).enter(p)`.
For one boundary, entering at site `i` and then exiting at site `j` cancels when
either site is absent or the sites agree, and rejects the candidate otherwise.
Exiting and then entering retains both crossings. Associativity of composition
does not make these two operations mutual inverses.

Alias qualification and structural type-field projection introduce no value scope.
Modules introduce no invocation boundary. Transport must follow the source
reference's scope, including references nested inside structured types; inspecting
only whether an outer shape is marked cannot decide this. `transportShape`
composes paths on deferred instance references before delivering them at projection
and result boundaries. Leaving a wildcard entry outside a wrapper could consume a
call exit before the wrapper's own path was considered.

A declared member is located at its class's definition, where its signature's
`Capture` nodes start. A receiver path starts where the value was created or
annotated instead. Its innermost exits from scopes that do not enclose the class's
definition are the receiver's provenance: they transport the class's argument
bindings, but not the member's own scope. Otherwise a member's scope would move
with each receiver's origin. Receivers created at different depths then disagree
about the scopes that enclose shared nodes such as a method's type-parameter
instance at one call site, and a candidate published through one receiver crosses
a scope twice when read through another. `NewResolver.nominalMember` performs this
split using the enclosing scopes that elaboration records for each type definition.
`newres/Arrays.mls` and `GenericMethods.mls` cover recursive and nested receivers.

New-resolution syntax records lexical `Capture` nodes, including in the prelude.
Imported type interpretations retain these source references in the consuming
graph; they do not reconstruct capture paths from selected member parameters.

For mutable array literals, the nominal interface lives at the literal's use site.
The allocation context belongs to its element-parameter reference. Attaching that
exit to the whole interface would duplicate the class exit during member lookup.

## Partial signatures and inference holes

Unannotated function parameters and results use ordinary marked inference.
Omitted generic arguments use one `TypeShape.Hole` host per source type-use and
formal position. They receive constraints from arguments, results, and ascriptions;
no invocation allocates another hole or a quantified binder for it. For example,
`Pair[Int]` omits the second formal of `Pair[A, B]`, while bare `Pair` omits both.
Distinct source occurrences have distinct holes; revisiting one occurrence or
expanding its alias reuses it. Declaration variance applies to omitted arguments,
and excess arguments are rejected, including in unused annotations. An empty hole
waits for evidence instead of immediately publishing an unknown candidate.

Written fragments continue to restrict the interface. Abstract types remain
`TypeShape.Abstract`; variance extremes are not holes. Interface exposure adds
unknown values to genuinely missing external inputs, including callback results.
Those unknown candidates remain alongside any local evidence.

Current limitations are [omitted-argument context precision](new-resolution-future-work.md#omitted-argument-contexts)
and [missing selected member types](new-resolution-future-work.md#inferred-member-signatures).

## Canonical references and termination obligations

Source dependency analysis computes free original binders over the finite
`TypeResolution` graph. Alias/quantifier edges hide their bound formals; an alias
application forwards argument dependencies only for formals used by its body.
Monotone finite-set equations reach a least fixed point. Nominal arguments remain
relevant, and nominal declarations conservatively retain all enclosing explicit
binders recorded by elaboration, including dependencies through local aliases.

No summary is finalized while a reachable source target is unresolved. Observations,
constraints, and hole exposure wait on shared dependency hosts, then project their
own saved environments. Synthetic formula/argument/selection nodes follow their
saved references instead of reading an ambient binding map. This removes irrelevant
bindings without freezing inference candidates or treating forward references as closed.

Instances are projected by a second analysis over the same graph
(`NewResolver.instanceDependencies`): synthesized reference nodes do instantiate
their retained references with the ambient instances, so those references' free
binders and retained instance sites count, as do the sites of directly referenced
instances and the template scopes of inferred and omitted-argument hosts and of
generic type uses that omit arguments. A pending target leaves this set
unbounded, which retains every binding.

[Regular structural types](new-resolution-regular-types.md) specifies guarded alias
recursion, alias reduction, Boolean normalization, and the conservative
constructor-cycle rejection check.
Accepted recursive references must share graph edges rather than grow substituted
environments. Structural recursion and recursive generic function constraints are
different: a call can add an edge to a reusable parameter instance without eagerly
unfolding its accumulated bounds.

For a fixed set of instantiation sites, the binder cache allocates finitely many
instances, so flat substitutions over the original binders also have a finite range.
Source holes have stable identities. Normalized paths contain distinct lexical
boundaries in each direction; their bounded length gives finitely many paths only
when their site labels also range over a finite set.
Formula normalization is finite for a fixed atom set. These bounds do not alone
establish finiteness of nested binding environments or the atom set.

Structural field constraints now reuse source projection sites, and partial
forwarding aliases share deferred interpretation's source-hole binding rules.
Wildcard normalization similarly retains canonical argument parts rather than
nested substitution histories. Their regressions establish these local bounds;
a [whole-graph termination argument](new-resolution-future-work.md#whole-graph-convergence-audit)
must still cover all accepted contextual references, formula atoms, and listener
convergence. Depth limits and dropped marks do not establish a fixed point.

These representations are internal to resolution. Lowering consumes completed
targets and value shapes; runtime values acquire no type-argument objects.

## Async fulfillment interfaces

`Promise[A]` retains its settlement value type. The intrinsic `Awaited[A]`
projects the eventual fulfillment interface, recursively adopting nested promises.
Both `await` and `.then` observe this projection; constructors may receive a promise
through their resolve callback. Factories and async results expose
`Promise[Awaited[A]]`, while `Promise.all` applies the projection to its element type.

The Promise declarations follow TypeScript's library where the current language
can express the signatures. Executor, resolve, reject, and finalizer callbacks use
`undefined` for TypeScript's `void`; only rejection reasons are unrestricted `Any`.
`then` keeps separate fulfillment and rejection result parameters, `catch` includes
the original fulfillment type, and `finally` preserves it. `Nothing` is the empty
fulfillment type of a rejected promise, including through type aliases.

Optional first callbacks, zero-argument factories, and default type arguments still
require language support. The rejection callback of `then` uses the existing rest
parameter convention; it, `catch`, and `finally` accept explicit `undefined` or
`null`. Promise inputs currently support native promises; structural
`PromiseLike` values, general JS
iterables, and tuple-mapped `all` results remain outside these signatures.

An async definition's result annotation describes its body before the async wrapper.
Inferred bodies feed a shared deferred type edge, preserving their lexical marks.
The `Awaited` application stays symbolic until the caller supplies its substitution:
expanding it at the definition would lose inferred generic result parameters.
Fulfillment observers are interned before following nested promises, retaining
late bounds and sharing recursive edges. Exposing a promise also exposes callbacks
inside its payload, so their parameter obligations cannot escape checking.

Structural thenables currently produce an unknown fulfillment interface. Treating
the original object's fields as the fulfilled value would be incorrect because
JavaScript can replace that object with the value passed to its `then` callback.
`Promises.mls` retains an explicit regression for the unsupported callback inference.

## Validation

Graph tests cover bounded instance allocation and replay (`TypeInstantiationTest`), directed
relations, delayed targets and consumer isolation (`TypeRelationTest`), and Boolean
normalization, including substitutions that identify atoms (`TypeFormulaTest`).
`MarksTest` checks activation matching, normalized composition, regrouping, reverse
transport, and wildcard identity loss across nested and sibling scopes.
These algebraic checks cover combinations that worksheet examples cannot exhaust.
`PublisherTest` checks exporter immutability.
`SubstitutionGrowthTest` bounds the views and activation contexts allocated for
generated chains of generic identities, and checks the substitution laws on
shapes: transitive site dependencies, nested and captured instances, bounds
published after a view exists, and observation-order independence.

Worksheet coverage under `newres` includes `MutableArrays`, `ContextualInference`,
`InstantiationSites`, `StoredSpecializations`, `SpecializationCaptures`,
`TypeArgumentVariance`, `VarianceSubstitution`, `VarianceSoundness`, `VarianceAliases`,
`AnnotationContexts`, `TypeGraphTermination`, `IrrelevantBinders`, `BinderSupport`, and `ArraySpreadViews`.
`Promises` covers async fulfillment, nested adoption, constructor inference,
generic call isolation, and escaping payloads. Deferred cases retain explicit
regression expectations;
see the [future-work reference](new-resolution-future-work.md).


### Fresh property keys

`@annotations.jsSymbol(path)` identifies a property by a stable path through modules and
immutable vals. The terminal val's `@annotations.fresh` marker is a contract,
not a type check or a proof about its initializer. Resolver key identity includes
the receiver path, and direct immutable receiver aliases are normalized. Modules
use their module symbol, independently of a companion function or class overload.
Key recognition does not evaluate a val initializer or force alias expansion.

Annotations on declared module members can be interpreted from the module's
syntax before its value definitions complete. This matters for prelude bootstrap:
`@fresh` must not require a runtime value from the declared
`annotations` module. Builtin `Symbol` lookup is lazy so interpreting an unrelated
annotation does not require `Symbol` to be present in an earlier prelude block.
Completed overload sets are published as soon as their definitions are available,
allowing a subsequent annotation to select through an earlier immutable val.

Lowering records computed names as explicit class operands and selected keys as
explicit path operands. Transformations therefore retain their imports and
captures and substitute their symbols. Computed names are evaluated in the
class's enclosing scope. Lifting cannot move such a class out of the invocation
that evaluates its keys; doing so could reuse a key or read it before initialization.

At block completion, resolution recovers an access path from the use site's
lexical scope to the key's binding, following enclosing modules when necessary.
Context updates preserve scope identity; entering a nested block creates a new
scope. Term definitions retain their binding scope, as module definitions do.
File bindings can also be reached through the compilation unit's existing default
export or private export ABI. Foreign provenance alone does not make a local
binding importable.

The legacy resolver uses the same `AccessPath.findAccessPath` helper for implicit
companion references. It retains the module overload at each step, so a companion
of a constructor function is reached through its class value, including across
files and after lifting.

The recovered expression is part of the resolved reference and is cloned and
lowered like other operands. Lowering does not maintain a separate inventory of
available bindings. A member's resolved declaration cannot supply a factory-local
key to an escaped instance's caller. Such accesses fail at the use site; nested
closures can still capture the key. These checks do not change candidate flows.
Overrides with a common key retain all their targets and share only the recovered
key operand.

Private members of classes and modules cannot supply keys across files: their
generated accessor symbols are local to one emitted JavaScript module. Resolution
reports the inaccessible private member at the selection, and code generation
asserts this boundary as a compiler invariant. This restriction does not apply to
private file-level vals, which use the compilation unit's private export ABI.
