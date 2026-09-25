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
each obligation applies to both. Supplying the single type `Int | Str` instead
retains that complete type as the negative constraint target. Positive union
elimination does not justify splitting a negative union into conjunctive obligations.
Concrete mismatches such as `Str <: Int` can remain quiet during migration; this
does not permit dropping the corresponding constraints.

## Instance wrappers and interface observations

`InstanceShape(DeclaredType)` describes an instance of a type. Parameter/result
annotations, ascriptions, and annotated fields retain this wrapper until lookup,
application, or destructuring requests an interface through `listenInstanceViews`.
The type itself stays in the `TypeResolution`/`TypeShape` graph. A written interface
restricts observation even when more specific implementation values reach it.

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

Declaration variance applies to an unqualified argument. A written wildcard
supplies its own parts and overrides declaration variance. Comparing actual `a`
with expected `b` installs `a.output <: b.output` and `b.input <: a.input`.
Missing wildcard parts are actual top/bottom types, not inference holes.

A subclass contributes the arguments of the requested nominal ancestor. Each
parent step preserves the child's binder substitution and the parent's scope
marks before installing both variance directions. This applies to constructed
receivers and declared nominal views, including multiple inheritance steps and
captured enclosing binders (`InheritedTypeArguments.mls`).

### Substitute at the occurrence before applying argument variance

First interpret an argument expression at its lexical occurrence polarity. A
formal bound to `in L out U` selects `U` positively and `L` negatively. Function
domains and written wildcard input parts reverse polarity; results and structural
fields preserve it. Then apply the enclosing formal's declaration variance to the
interpreted argument. An invariant formal uses that one type for both parts.

For example, with `Child <: Base`:

```mlscript
class Box[T](val item: T)
class Receiver[T] with
  fun accept(box: Box[T]): () = ()
```

On `Receiver[in Child out Base]`, `accept` expects `Box[Child]`: the occurrence of
`T` is negative, and the invariant `Box` argument uses the selected `Child` for
both parts. A declaration's `in` annotation does not itself change the lexical
polarity at which a substituted argument is evaluated.

`DeclaredType.positive` records this lexical polarity, independently of a later
constraint's direction. `TypeShape.Wildcard` retains written parts;
`TypeShape.Argument` retains contextual references for synthesized variance.
Neither transplants supplied syntax into the callee's binding environment.

`TypeShape.SelectedArgument` saves a requested part when the argument is deferred.
Both subsequent constraint directions use that same selected type. Selections are
cached by argument reference and polarity; selecting an existing selection is
idempotent. Forwarding cycles retain subscriptions but stop repeated observation.
For a fixed argument-reference set, selection adds at most two nodes per reference.

## Shared bodies and contextual constraints

The inferred body is a shared graph. Instantiated views carry flat original-binder
to instance-symbol substitutions through deferred tuples, records, callbacks, and
closures. They do not copy expanded argument candidates into a new body graph.
Shape substitution is memoized so repeated observations reuse aggregate identities.

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

Value captures and body activations use the opaque `TypeSubstitution`, whose
underlying immutable map remains available for reads. Its constructor derives
each key from the instance's original binder. `withOverrides` combines two valid
substitutions with the right operand taking precedence, and `without` removes
shadowed binders. Both preserve the substitution type; arbitrary map updates do
not. This rules out mismatched binder/instance pairs without runtime validation
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

## Validation

Graph tests cover bounded instance allocation and replay (`TypeInstantiationTest`), directed
relations, delayed targets and consumer isolation (`TypeRelationTest`), and Boolean
normalization, including substitutions that identify atoms (`TypeFormulaTest`).
`MarksTest` checks activation matching, normalized composition, regrouping, reverse
transport, and wildcard identity loss across nested and sibling scopes.
These algebraic checks cover combinations that worksheet examples cannot exhaust.
`PublisherTest` checks exporter immutability.

Worksheet coverage under `newres` includes `MutableArrays`, `ContextualInference`,
`InstantiationSites`, `StoredSpecializations`, `SpecializationCaptures`,
`TypeArgumentVariance`, `VarianceSubstitution`, `AnnotationContexts`, and
`TypeGraphTermination`. Deferred cases retain explicit regression expectations;
see the [future-work reference](new-resolution-future-work.md).
