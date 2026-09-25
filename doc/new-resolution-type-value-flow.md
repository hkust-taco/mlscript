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
checking body remains a [design issue](new-resolution-future-work.md#quantified-bounds).
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

`ActivatedShape` records the body activation that produced an event.
`ContextualShape` carries the value's caller-side view. These substitutions must
remain separate: recursion can bind the same original parameter differently in
the callee body and in a captured caller value. Composition keeps a fixed base
state and flat maps, not a chain of activation environments. Source listeners
accept all activations; contextual observations accept compatible ones.
`NewResolverState.withInstances` shares consumer hosts, and `inGraph` preserves
the incoming activation when invoking an imported listener.

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
  the class when publishing its selected member view.
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

[Regular structural types](new-resolution-regular-types.md) specifies alias reduction,
Boolean normalization, and the conservative constructor-cycle rejection check.
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
