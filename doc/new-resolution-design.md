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

[`PublisherTest`](../hkmc2/jvm/src/test/scala/hkmc2/PublisherTest.scala)
checks independent consumers and unchanged source candidates and listeners,
cycles, reentrant replay, transitive private inference, and bounded copying
in the presence of unrelated exporter hosts. `newres/GenericMethods.mls` covers
exported mapped arrays and imported generic functions and methods.

## Captures and generic flow

[Instance types and parameter constraints](new-resolution-type-value-flow.md)
specifies instance wrappers, input/output constraints, variance, canonical binder
instances, shared body views, and partial-signature inference. Its
[shape roles](new-resolution-type-value-flow.md#value-views-consumed-schemes-and-activation-events)
section distinguishes captured value substitutions, consumed callable schemes,
and inference-event activations, with examples and their representation invariants.
[Regular structural types](new-resolution-regular-types.md) specifies normalization
and the conservative recursion restriction. Do not duplicate those algorithms in
member lookup or value-flow handling.

Context fragments compose from a definition to its consumer; argument flow
traverses that composition in reverse. A class and its constructor share one
resolution boundary. Methods capture their enclosing instance scope as well as
the enclosing function scopes. Alias qualification and structural type-field
projection introduce no value boundary; modules introduce no invocation boundary.

A normalized mark path contains entries followed by exits, with no repeated
lexical boundary in either direction. `Shape.scala` enables assertions for this
invariant. Checking each new tail costs linear time in its depth; it must not be
replaced by truncating or widening paths. In particular, wildcard exit followed
by wildcard entry is not an identity: it can discard a caller's activation ID.
Reference transport uses the same operations as ordinary value flow.

The prelude uses its own `#lang(0.3.x)` directive. Its loader applies file
configuration before elaboration and erasure, and supplies the block's original
symbols for builtin lookup during bootstrap. Its signatures therefore carry the
same `Capture` syntax as other new-resolution declarations.

Legacy consumers can read completed new-resolution signature symbols through
`legacyResolvedSym`. The lookup asserts that the referenced block is complete and
shares erasure's symbol-selection rules, including ambiguity and error checks.
It does not resolve imported syntax again or observe incomplete candidate sets.

`newres/SpecializationCaptures.mls`, `RecursiveEnvironment.mls`, and
`ConstructorFieldRecovery.mls` exercise captured specialization, recursion, and
partial construction. `PrimitiveMembers.mls`, `Arrays.mls`, `GenericMethods.mls`,
and `MutableArrays.mls` exercise prelude signature captures and array member paths.
Receiver reconstruction and omitted-argument context precision are
[deferred improvements](new-resolution-future-work.md).

## Declared interfaces and exposure checking

Type interpretations retain arrows, type arguments, and lexical captures.
Generic aliases and inherited declared interfaces substitute their arguments;
declared member selections carry those contexts without reading implementation
value flow. An unannotated member read through a declared interface produces an
unknown shape, rather than consulting its initializer or method body.
Inferring these missing member types is a [deferred improvement](new-resolution-future-work.md#inferred-member-signatures)
that also requires override compatibility checks.
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

Tuples preserve zero-based projections and expose the builtin Array interface.
An Array callback receives candidate shapes from every element. The
[language reference](reference.md#10-arrays) specifies mutable-array behavior and
the restriction imposed by explicit element annotations.

For a mutable literal, all element reads and writes use the builtin `Array[T]`
parameter's symbol. Marks distinguish allocations and enclosing calls. Cache the
nominal view before subscribing to the initializer so empty arrays can receive
writes and recursive arrays can refer to themselves. Numeric projections, spreads,
patterns, and callbacks all use the same element endpoint.

The nominal interface is located at the literal's use site. Its element reference
carries the allocation exit; the interface itself does not. Member lookup already
exits the nominal class scope. Adding the allocation exit to the entire view would
therefore cross that boundary twice. Initializer shapes enter the allocation
context before reaching the parameter host.

When an array is returned or otherwise exposed to callers, `InterfaceExposure`
also follows its element shapes. A function stored in that array must be checked
for calls from outside the compilation unit, just like a directly returned
function. `newres/MutableArrays.mls` and `CompilerTest` cover element flow,
separation between calls and importing compilation units, and exposed functions.
See the [migration worklist](new-resolution-suite-migration.md) for the remaining
`splice` contract and storage-reassignment gaps.

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
