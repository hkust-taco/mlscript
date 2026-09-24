# New-resolution implementation invariants

This note describes the resolver's implementation contracts. User-facing rules
are in the [language reference](reference.md#resolution-interfaces); outstanding
ports and implementation gaps belong in the [migration worklist](new-resolution-suite-migration.md).

## Inference ownership and completed references

[`NewResolverState`](../hkmc2/shared/src/main/scala/hkmc2/semantics/NewResolverState.scala)
owns the inference graph and caches. Listeners have type
`TermShape => NewResolverState ?=> Unit`, so imported callbacks access hosts
through the consuming state. Importing copies accessed hosts' candidates and
listeners lazily; caches consult individual source entries on demand. It must
not copy or enumerate an exporter's entire resolver maps.

Type-parameter references retain their originating host. This lets exporter-private
inference on third-party parameters survive re-exporting. Legacy annotation
interpretations also remain local, rather than attaching consumer callbacks to
shared prelude syntax.

Completion seals each file or diff-test block's recorded decisions and original
host data read by erasure/lowering. Symbol flow and elimination listeners remain
active against private host data, but cannot change completed reference targets.
This applies even between worksheet blocks sharing an elaborator state. An unknown
reaching a sealed elimination can still report an error without changing its target.

[`CompilerCacheTest`](../hkmc2/jvm/src/test/scala/hkmc2/CompilerCacheTest.scala)
checks independent consumers and unchanged source candidates, listeners, and
legacy annotations. [`PublisherTest`](../hkmc2/jvm/src/test/scala/hkmc2/PublisherTest.scala)
covers cycles, reentrant replay, transitive private inference, and bounded copying
in the presence of unrelated exporter hosts. `newres/GenericMethods.mls` covers
exported mapped arrays and imported generic functions and methods.

## Captures and generic flow

`InstanceShape` retains a type reference at annotation boundaries; member lookup,
application, and destructuring obtain specialized interfaces through
`listenInstanceViews`. The distinction between supplying a type argument and
adding an ordinary bound, the agreed variance rules, and the proposal to instantiate
declared type parameters once per definition and syntactic call site are documented
in [Instance types and parameter constraints](new-resolution-type-value-flow.md).
The description below records current generic inference. Omitted generic arguments
use source-owned inference holes and retain live inference through partial
signatures. Recursive hole contexts, alias-body omissions, and missing nominal
member types still need the contextual reference work described in that document.

Class bodies introduce lexical captures, and a class and its constructor share
one resolution boundary. A method's reference to an outer constructor must include
the enclosing instance boundary as well as the method boundary. Consuming a
reconstructed instance cancels the old instance exit against its capture, retaining
the fresh constructor exit. Explicit `new` uses the same constructor context for
arguments and subsequent parameter lists.

Context fragments compose from the definition to its consumer; argument flow
traverses that composition in reverse. Capture paths have no truncation or depth
limit. The optional `checkMarkPaths` assertions in
[`Shape.scala`](../hkmc2/shared/src/main/scala/hkmc2/semantics/Shape.scala)
detect repeated boundaries in either direction. They are disabled by default
because scanning every new mark's tail makes chain construction quadratic in depth.
`newres/RecursiveEnvironment.mls` and `ConstructorFieldRecovery.mls` exercise
recursive calls, nested captures, partial construction, and independent field results.

Explicit and inferred function/constructor type arguments flow through the
corresponding type-parameter symbols with entry/exit marks. Explicit arguments
receive input constraints without adding value-argument shapes to their output
interface at ordinary call boundaries. Bodyless members of constructed instances
still use a positive-only conversion for supplied class arguments; the callback
input regression in `newres/ConstructorInstances.mls` records this limitation.
Inference also connects nested
nominal parameters, such as `Foo[A]` containing a `Box[A]`. Generic methods use
the same flow as free functions, including callback-result inference and curried
signatures. Declared callable shapes retain their type parameters. Functions and
constructors allocate explicit binders once per original definition and syntactic
term application. Stored specializations and unapplied `new` retain supplied type
references until that application; subsequent curried lists retain its instance map.

Nominal argument comparisons retain directed `ContextualType` endpoint pairs.
Invariant arguments install both directions, rather than copying expanded
candidates. `in`/`out` arguments use InvalML's input/output comparison rules;
written wildcards override declaration variance. A parameter receives a symbolic
instance wrapper, and structured/concrete targets retain listeners for later
bounds. `newres/MutableArrays.mls` includes passing direct and recursive append
cases, including distinct callers through one stored function reference.
`TypeRelationTest` checks graph replay and consumer isolation directly.

Generic definitions receive a distinct checking activation when their type
parameters are declared. Its `RigidTypeShape` witnesses enforce generic opacity
independently of visibility, exposure, or strict mode. Interface observation turns
a witness into an unknown interface, but call-site inference does not copy that
witness as a bound. Symbolic references remain available for substitution instead.

Inline explicit binders in partially annotated functions use the same finite
definition/application-site allocation as complete callable signatures. The
shared body carries a flat substitution through deferred tuples, records,
callbacks, and closures. A source-flow event's body activation and its value's
caller-side type references remain distinct, including when recursion rebinds the
same original parameter. Contextual observations select compatible activations;
marks continue to distinguish enclosing callers of a shared inner site. See
`newres/ContextualInference.mls` for stored-function and deferred-field cases.

Omitted generic arguments use `TypeShape.Hole`, a stable inference host for each
source type-use/formal-position pair. They infer through arguments, result
annotations, and ascriptions; an empty hole waits for evidence. Written fragments
continue to restrict the interface. Exposure checking contributes unknown values
to missing parts of external inputs, including callback results, without widening
written binders. `newres/InferenceHoles.mls` also retains unresolved cases for
recursive holes and omissions shared through an alias body. No hole creates a
call-site parameter instance.

Standalone specializations of inferred functions retain their supplied types in
`SpecializedShape` until application. Each application binds its own memoized
parameter instances; the original generic binder remains unchanged. Argument
arity is checked even for unused specializations. `newres/StoredSpecializations.mls`
covers stored aliases, inferred record results, and curried calls. It also records
the remaining gap in observing an inferred specialized result during callback
checking before application; see the
[type-flow reference](new-resolution-type-value-flow.md#partial-application-and-explicit-specialization).

## Declared interfaces and exposure checking

Type interpretations retain arrows, type arguments, and lexical captures.
Generic aliases and inherited declared interfaces substitute their arguments;
declared member selections carry those contexts without reading implementation
value flow. An unannotated member read through a declared interface produces an
unknown shape, rather than consulting its initializer or method body.
This is current behavior pending the reviewed partial-signature design: missing
member types will use the selected declaration's contextual inference graph,
while nominal annotations continue to restrict the visible member set. Override
compatibility must be checked before exposing inferred dispatch results.
Callback parameter types constrain implementation parameters, and callback results
constrain inferred type arguments. `newres/DeclaredTypes.mls` covers these paths,
separate signatures, tuple constraints, and distinct generic instantiations.

[`InterfaceExposure`](../hkmc2/shared/src/main/scala/hkmc2/semantics/InterfaceExposure.scala)
checks values reachable through a file's exposed interface before completion.
Worksheet blocks run this pass only under strict resolution. It seeds unannotated
parameters with `UnknownValueShape` and follows returned functions, record/tuple
contents, public instance members, and both interpretations of exposed overloads.
Callable result annotations constrain returned implementations through their
declared domains. Private helpers retain local inference unless their values escape.

Discovery uses a queue and temporary observers of shape publishers. Each reached
shape is processed once, with listeners discovering subsequent candidates;
there is no repeated whole-graph scan. Observers detach before completion and
are never copied into consumer states. Imported new-resolution definitions have
already had their interfaces checked and are not recursively checked by importers.

Unknown values and unresolved spreads carry shared, lazy provenance. Messages,
locations, and diagnostic chains are materialized only on error; provenance does
not affect shape equality. Diagnostics can identify the parameter and the storage
and return steps that expose it. `newres/InterfaceExposure.mls` covers discovery,
typed closures, overloads, and later exposure of a private definition from an
earlier block; its expected failures also document remaining precision gaps.

## Structural and dynamic shapes

Record fields have their own `BlockMemberSymbol`s. Lookup follows overwrites and
spreads in source order, preserving selected values' shapes and captures. Named
fields in term tuples are expressions, not type annotations. Tuple shapes group
them into one trailing record, matching lowering while retaining source evaluation
order, last-write-wins lookup, computed-key uncertainty, and property identities
across imports. See `newres/NamedFields.mls`, `ImportedNamedFields.mls`, and
`RecordInterfaces.mls`.

Tuples preserve zero-based projections and expose the builtin Array class as
their parent. For example, `[First(1), Second(2)]` has a `First` value at index 0
and a `Second` value at index 1. An Array operation such as `map` can read either
element, so its callback receives both candidate shapes.

For a mutable literal, statically resolved element reads listen to the builtin
`Array[T]` type parameter's symbol. The initializer and later indexed assignments, `fill`, `push`,
and `unshift` send element shapes to that symbol. For example, starting with
`mut [First(1)]` and then pushing `Second(2)` makes both `First` and `Second`
candidates for each statically resolved element read. Overwriting or removing an element does not
remove its shape from these candidates. Resolution does not track which shape
belongs at which index or how long the array is. Each candidate is checked when
resolving an operation on an element; the presence of a `First` candidate cannot
justify accessing a `First`-only member when `Second` is also a candidate.

The symbol is shared, but its shapes carry context marks that distinguish array
allocations and enclosing function calls. This keeps writes to separate arrays
from affecting each other's element reads. The cache in `NewResolverState` stores
the array's shape before subscribing to its initializer, allowing empty arrays to
receive writes and recursive arrays to refer to themselves. Numeric projections,
spreads, patterns, and callbacks all receive the element shapes through `T`.

An explicit element type restricts which members resolution may use. If an array
is viewed as `Array[Base]`, inserting a `Child` that extends `Base` does not make
`Child`-only members accessible through that view. Resolution uses `Base`'s
declared members, regardless of the inserted value's more specific shape. In
`Array[A]`, where `A` is a type parameter, element reads instead receive the shapes
inferred for `A`.

When an array is returned or otherwise exposed to callers, `InterfaceExposure`
also follows its element shapes. A function stored in that array must be checked
for calls from outside the compilation unit, just like a directly returned
function. `newres/MutableArrays.mls` and `CompilerTest` cover element flow,
separation between calls and importing compilation units, and exposed functions.
See the [migration worklist](new-resolution-suite-migration.md) for the remaining
`splice` and generic-parameter write propagation gaps.

When an array's element shape is unknown, indexed access produces an unknown
shape; that does not authorize arbitrary member access on the result.
Tuple-pattern transfer handles leading, trailing, and rest elements, including
declared Array element types. See `newres/Arrays.mls` and `TuplePatternBindings.mls`.

`DynShape` is distinct from `UnknownValueShape`: recursive widening, mutable reads,
and other losses of precision do not license dynamic lookup or calls. Known invalid
alternatives still report errors alongside dynamic candidates. Constructor patterns
narrow unknown inputs to declared class interfaces, retaining unknown type arguments
and provenance for unannotated fields instead of specializing them from local calls.

Dynamic selections have no fabricated nominal definition. Lowering retains the
runtime receiver and property name. Dynamic values propagate through record/tuple
spreads and unique wildcard opens; competing wildcard receivers still need
disambiguation. Class projections, constructor patterns, and type references require
known, unambiguous identities. See `newres/Dynamic.mls`, `Records.mls`,
`SpreadCalls.mls`, and `loose/Targets.mls`.

## Normal results of control flow

Resolution must agree with lowering about which expressions produce values.
Assignments, `drop`, imperative conditionals, and loops return unit; their
operands or branch results must not supply the result's member interface.
A normally completed `try` returns its body's value, preserving its capture
marks, while the `finally` clause runs for effects. `throw` and `continue` supply
no normal result. `newres/ControlFlowResults.mls` checks these contracts, including
backtracking assignment and independent calls through cleanup blocks.

## Overloads, foreign declarations, and lowering

Ordinary values select function/constructor overloads; selection receivers select
companion modules. Preserve this distinction through nested captures and opens.
`newres/OverloadedCalls.mls` covers direct, generic, stored-function, module-member,
and captured uses.

Foreign declarations expose call and constructor capabilities explicitly.
The JS backend uses native class values for `new` and patterns without generated
MLscript `.class` storage. Bodyless foreign methods use foreign-call normalization
even when `declare` is on the enclosing class, so JavaScript `undefined` results
follow the existing unit normalization. Prelude declarations are parsed as one
compilation unit, permitting references across blank lines.

Generated runtime-helper selections, such as `runtime.assertFail`, are synthetic;
they do not provide a fallback for unresolved source selections. Free-variable
collection and assignment lowering must handle resolved direct references and
retain the existing binding/assignment checks. Constructor-pattern resolution
discards every nested capture when recovering class identity; leaving one behind
can make generated patterns test a constructor function instead of its class.
