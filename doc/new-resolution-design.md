NOTE: This document was written by Codex Astra and has not been deeply reviewed;
it is not meant to be official documentation and
is in fact likely to contain parts that are unintelligible to readers who lack sufficient context.


# New-resolution implementation invariants

This note describes the resolver's implementation contracts. User-facing rules
are in the [language reference](reference.md#resolution-interfaces); outstanding
ports and implementation gaps belong in the [migration worklist](new-resolution-suite-migration.md).

## Inference ownership and completed references

[`NewResolverState`](../hkmc2/shared/src/main/scala/hkmc2/semantics/NewResolverState.scala)
owns the inference graph and caches, once per compilation unit. Listeners have
type `TermShape => ResolutionContext ?=> Unit`. An immutable `ResolutionContext`
selects the consuming state, import path, and active substitution; changing the
substitution never creates another resolver state. Imported callbacks access hosts
through that context. Importing copies accessed hosts' candidates and
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

[Lexical paths in resolution](new-resolution-scopes.md) derives the normal form,
boundary agreement, and depth bound from walks in the lexical scope tree. It also
states the endpoint obligations on producers and the separate requirement for
stable identities in recursive inference graphs.

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

An unknown-length tuple segment retains a deferred element field, just as a
fixed tuple position does. Tuple views instantiate both through the same field
representation, and indexing, array interfaces, argument transfer, and patterns
observe that field through `listenTupleField`. Unknown length does not erase the
element's type arguments or captured environment. A positional selection after
a spread includes every field that can occupy that position, including a fixed
suffix when the spread is empty; positions before a spread remain precise.
`newres/ArraySpreadViews.mls` covers these cases and distinct generic callers.

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

## Candidate identity

Graph producers compare by identity. Tuples, records, and declared-type instances
must be built through their canonical factories because their identities anchor
inference hosts. Immutable views use `ShapeIdentity.key` to compare their source
and effective substitution without including diagnostic witnesses. Member lookup
uses the observation itself so that errors retain its diagnostic evidence.

`ValueKey` caches hashes of immutable fields; keys must never include live
publisher contents or inferred bounds. `DeclaredType` interns semantic references
in the consuming unit while retaining each observation's witnesses. Importing
normalizes references without changing the exporter, and cross-unit equality
visits each shared reference pair once to avoid exponential traversal of type DAGs.

`instantiateShape` projects substitutions onto the value's binder support before
constructing a view. Captured bindings take precedence over incoming bindings;
activation environments remain separate. See
[binder support](new-resolution-type-value-flow.md#shared-bodies-and-contextual-constraints).

`Candidates` deduplicates with the payload type's key and preserves publication
order. Ordinary iteration and subscription replay use a snapshot; `foreachGrowing`
also visits candidates appended during callbacks.

## Recursive getter results

Parameterless definition bodies have a shared result host, cached by definition
and generic activation before following the body. Recursive references subscribe
to that host instead of traversing the body again. An unproductive cycle has no
normal result candidates; a productive branch publishes candidates through the
cycle, with the publisher suppressing duplicates. No unknown or dynamic fallback
is introduced to stop recursion.

The host stores results at the body's lexical endpoint, including their activation
events. Each reference still applies its own exit and capture marks. Resolver-state
caches and consumer-local publisher copies preserve this graph across imports
without sharing mutable inference between consumers. `newres/RecursiveGetters`
checks cycles, later candidates, captures, generic specializations, imports, and
runtime getter effects.

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

Bare classes can share their name with a function definition that has a parameter
list. The generated function owns the class reference, so JS uses the existing
`.class` property for references, selections, and imports. Arbitrary values,
parameterless functions, and term declarations cannot supply that companion:
their results may be primitive, aliased, or frozen, and must never be augmented.
Instance methods cannot supply per-instance companions either, because their
function objects are shared. Inlining may replace calls to a companion function,
but must preserve its binding while the class is used. WASM identifies constructor
functions by their class symbols, separately from explicit function companions.
Session imports follow the selected definition and cast target, rather than MIR
`freeVars`, which tracks lexical bindings introduced by `Scoped`. Importing a
class must not also import its function companion: the two have independent
signatures and can be shadowed independently in later worksheet blocks.

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

## Implicit namespaces

User-facing rules are in the [language reference](reference.md#implicit-namespaces).
An unbound capitalized value is an `UnresolvedRef` with `NameLookup.NamespacesThenOpens`;
a leading-dot selection is one with `NameLookup.LeadingDot` and no wildcard prefixes. It
initially publishes a `NamespaceProbe`; as flow reveals namespaces, it immediately
looks up and publishes their candidates. Block settlement decides wildcard fallback
and diagnoses the resulting candidates. The probe travels along ordinary value edges and
through the operations of the chains rooted at the reference, which derive their result
from an operand: selections (including projections and checked or dynamic accesses),
applications, type applications, and instantiations (with `new` or `new!`).
Elaboration's interpretation roles decide where implicit namespacing applies: chained
selection receivers (`Receiver(chained = true)`) and the classes instantiated by `new`
(`Clss(instantiated = true)`) use it, whereas types, `extends` clauses, and annotations
only consult explicit bindings and wildcard opens.

The probe is not a value, wherever it arrives: as a value, or as the view of a type
variable that it reached. `ShapeObserver` dispatches observed shapes to distinct value
and probe callback types, preserving the original shape and marks without a wrapper.
`listenInstanceViews`, `listenTermViews`, `listenReceiver`, and `listenClass` use it to
hide probes from value consumers and deliver them to the chains that pass them on.
`listenInstanceFlow` and type-view hosts retain both kinds of flow, as their consumers
can need either. `inferTypeArguments` records an observation before following either endpoint,
then observes probes reaching a declared type, directly or as the view of a type variable.
A probe stands for a value of the whole required type, whose namespaces `typeNamespaces`
discovers. The same observation key governs structural constraints and namespace discovery;
there is no separate relation table that could discard a later argument's namespace.
A constructor pattern's head instead observes the values that reach its scrutinee
(`scrutineeNamespaces`, in `matchShapePat`), before the views of declared types erase
the declarations that these types name. `valueNamespaces` follows the types of declared
values, including the values that reach their type parameters, and the classes of
instances. Record patterns read the fields of their input with the member lookups of
selections, at a site that the elaborator records.

Interned type references include local alias annotations and the identities of their
arguments. Ordinary types carry no namespace annotation and serve directly as view and
constraint keys. There is no parallel observation graph. Thus `Box[FirstAlias[X]]` and
`Box[SecondAlias[X]]` retain different argument references without attaching the argument's
namespaces to `Box` itself. Projecting a field exposes that argument's annotated type.
Diagnostic locations do not participate in interning. Per-use interpretations of synthesized
nodes preserve diagnostic witnesses and operand order, and must have the same child types
as the interned source.

Expanding an alias with a companion or declaring namespace prepends its identity to a local
`TypeNamespaces` priority list. The first occurrence of an alias is enough: for a fixed
name and lexical scope, trying it again cannot discover a different provider. Repeated
`Identity[Identity[A]]` forwarding therefore reaches the same annotated reference. Aliases
with no namespaces add no metadata. Eager argument reduction remains necessary for the
current recursive cache scheme, so suspended alias applications cannot accumulate in its
substitution environments. The interner stores child references without diagnostic payloads
and imports each shared reference once into the consuming unit.

`typeNamespaces` follows the type graph using the ordinary `reduceType` application rules.
It first tries the type's local alias priorities, then its head constructor, body, or inferred
values. Each class or alias contributes the first of its own namespaces (its companion,
then its declaring module) that provides an accessible member (`firstProvider`). Required
types constrain probes; provided type parameters additionally observe incoming values.

Boolean components that survive normalization contribute independently. An annotation on
a Boolean formula distributes its priorities over the surviving atoms when the formula is
combined again. Distinct annotated atoms remain distinct; recursive normalization needs no
separate merge of namespace observations. Discarded components contribute no namespaces:
`Any | A` has the namespace behavior of `Any`, and `A | (A & B)` has that of `A`.
`ImplicitNamespaces.consulted` decides each namespace once per reference: it is pending
until defined, then missing the name, inaccessible, selected through a path from
`AccessPath.valuePath` (whose paths carry the same `Capture`s as written references),
or found late.

`settleUnboundReferences` runs before interface exposure and block completion, and takes
the references and contextual sites of the current block from `resolutionSites`. It lets
capitalized references without namespaces fall back to their wildcard opens in source order, then diagnoses
missing and ambiguous names. Namespaces revealed afterwards are reported against the
settled candidates and never change them; `AccessPath.reachable` checks their paths
without building them. `LeadingDotSelections.mls` and the `ImplicitNamespace*.mls` files
in `slop/` cover these rules.

## Contextual parameters

The [language reference](reference.md#13-context-parameters-type-classes) specifies
completion, matching, scope, and timing. The implementation shares the ordinary
flow graph, application inference, and implicit-namespace walk.

`Ctx` carries a persistent list of lexical instance tiers, shared by sites. Each
contextual parameter clause contributes one tier; each completed `using`
declaration contributes another. Module and object declarations own their instance
members and cache an instance-member index. Anonymous instances have declaration
keys inaccessible to source; named instances use ordinary member names. Both
lookup paths share visibility and receiver transport. Legacy binding tables remain
unchanged. Runtime anonymous bindings occupy a separate symbol-keyed table to
avoid collisions with named properties and inherited instances.

Elaboration records contextual sites and unresolved references in one
`resolutionSites` worklist in post-order. The site's pending entry stores its role,
source scope, lexical instances, and type binders. Settlement processes each entry
synchronously before exposure and completion. An application head supplies only
leading contextual lists; a value site also abstracts ordinary lists that precede
later contextual lists. Calling-convention checks apply when reference targets
arrive, independently of whether a site supplies arguments.

`listenContextual` materializes definition references at their producing site.
It uses instance views only to classify the received value, and forwards ordinary
values unchanged. Forwarding an expanded view would lose deferred substitutions,
marks, and annotations, breaking generic identity calls across imports. Declared
`InstanceShape` values pass through without expanding their type references;
written function types cannot contain contextual lists. Selected declared callable
interfaces retain their contextual-list metadata and declaration identity.

Every stored value and completed output has no leading contextual list. Check this
with `softAssert` at variable, field, parameter, and completion publishers.
Contextual lambdas are completed at their literal sites; generic values cannot
carry a deferred completion obligation. Generic member lookup remains opaque.
No deferred completion graph edges or per-term wrapper state are needed.

Only potential site classes mix in `ContextualSiteImpl`: applications, type
applications, instantiations, definition references and selections, `super`,
lambdas, and outer captures. `SimpleRef` and compound heads are not sites. Pending
sites reuse the worklist entry; completion work, output hosts, and observers are
allocated only on demand. Completed syntax is sealed with its synthesized terms.

A Supply step uses `App(Missing, CtxTup(InstanceArg...))` and ordinary `applyShape`.
Its argument constraints and call activation exist before queries are decided.
Each `InstanceArg` records its selected expression and publishes it immediately,
so the next query can observe its inference consequences. All callees reuse these
steps, but select under their own bindings and must agree on the runtime arguments.
Selections never change after their decision. Later incompatible values report
errors through the same matching relation used for selection.

Only a subscription in the empty activation drives a site's completion. It receives
each raw value in the activation that published it, as the term traversal does for
an ordinary application, and every site has one. A consumer in a body activation
views the base completion through that activation's instances and subscribes to the
output in its own context. Driving the completion there would constrain the callee's
call-site instances, which every activation shares, with instantiated types of the
site's binders: a receiver `Boxed(1)` of a method in `Boxed[A]` would make `Int` reach
a query that selected a `Show[A]`. The site's decisions, checks, reports, and stage
subscriptions belong to the consuming unit's base context, which each activation
inherits, so sibling activations neither decide nor report again.

A flow can conflict with what a site has already seen: a late value or namespace
reaches a decided argument, or a callee's calling convention, parameter list before
an eta-expanded contextual list, or selected instances differ from an earlier
callee's. Such a report starts at the source expression whose flow did it
(`NewResolverState.trigger`): the elaborator sets it while subscribing a term it has
just created, and a site's pending inputs carry it to settlement. A late-value report
then names the value that the matching relation finds incompatible with the selected
instance's type at its position, followed by the site that selected the instance.

An Abstract step has a synthesized ordinary lambda for flow and an application
for its continuation. That application owns further completion steps, and the
lambda observes its completed result. The lambda mirrors the abstracted parameter
list of the first callee, with fresh unannotated parameters that keep its optional
markers and variadic structure, so it accepts the arguments that a direct reference to
the callee accepts. A variadic wrapper would instead forward every argument that its
caller passes, such as the index and array that `map` passes to its callback, to a
callee that does not accept them. An omitted optional parameter is null in the lambda,
and forwarding null is equivalent to omitting the argument. A later callee whose list
has a different shape is a site error, since the site has one expansion. Ordinary
application inference still checks each callee's arity and constraints.
Lowering flattens the continuation steps, interleaves contextual and written
arguments, and emits lambdas around the ordinary call or constructor operation.
A contextual argument list has the runtime layout of an ordinary one, so lowering
passes its elements directly rather than spreading an array. An expansion captures
its operands once in source order, each argument in its own temporary, and
reconstructs method selections on the captured receiver, preserving receiver binding.

Query positions are observed in the base activation, through `observeTypeViews`
with `opaque` set. An explicit type parameter that the position does not instantiate
then contributes only its abstract value: the `RigidTypeShape` that
`registerTypeParameters` publishes, viewed as an `AbstractParameterValue`. Ordinary
views turn that witness into a plain `UnknownValueShape`, and they also include the
values that constraints add to the parameter's host, for instance through an
unannotated lambda parameter that code outside the definition calls; neither would
keep the signature opaque. Matching then ignores the abstract values of type
parameters that are not in scope at the site, since they are other generic bodies'
checking witnesses. No caller activation is observed, so a generic body's decisions
never depend on its callers or importers. Importers must not mutate the exporter's
decisions or each other's observations.

`NameNamespaces` and `InstanceNamespaces` implement requests over one shared
`typeNamespaces`/`valueNamespaces` walk. Name requests retain their existing
consultation keys and behavior. Named instance requests cache provider decisions
by module; parameter requests use module and triggering class or alias. The module
instance index is shared by all requests. Provider checks inspect declaration
heads, including subclasses, without consulting argument compatibility. Instance
requests traverse type arguments as well, independently of alias-provider cutoff.
Late namespace discovery uses consumer-local caches and reports against the fixed
selection only when the namespace tier participated.

The `slop/contextual/` suite covers completion, imports, nested captures, receiver
binding, effects, namespace cutoffs, and late values and callees. Existing
`ImplicitNamespace*.mls` and `LeadingDotSelections.mls` outputs remain unchanged.
Partial parent application in anonymous refinements and generic tuple-alias scope
transport remain independent `:fixme` regressions; they do not authorize skipping
invariants or changing contextual rules. Generic override representation, nested
companion initialization, and handler-parent/interface gaps also retain explicit
regression markers in the contextual ports.

### Derived instances

`BlockImpl` normalizes the parser's nested `TermDef(Ins, TermDef(Fun, ...))`
only in its new-resolution statement view and binding table. This keeps legacy
syntax and symbols unchanged. The ordinary `TermDefinition` retains a dedicated
instance-function flag; its kind remains `Fun`, so ordinary inference and call
lowering apply. The flag occupies a separate constructor parameter list to
preserve the existing two-field `TermDefFlags` extractors in legacy resolution.
Blocks without these declarations reuse their original statement lists and
binding tables.

Class-body instances remain lexical source bindings and are excluded from the
class's selectable member table. Their runtime definitions use private class
storage, because a method cannot read a JavaScript constructor's local variable.
Lexical references lower through the owning receiver, retaining per-object
captures. Bind instance-function names lexically before elaborating their bodies
so explicit recursion retains the same meaning. Modules and objects continue to
provide ordinary instance members. These storage and normalization adjustments
implement the approved scope rules without changing source visibility.

A selected instance function builds an application chain using fresh `InstanceArg`
terms. Seed the function's type arguments from its result view of the query head,
including inherited result positions, before applying its contextual arguments.
Use the ordinary call-site instantiation cache and type constraints, which invoke
`inferTypeArguments`; parameter queries infer from the whole result. Query positions
retain alias and explicit-argument scope transfers. `constrainTypes` carries the
query endpoint back through its callee to the site, then into the derived function.
Feeding expanded observations directly would mix the two functions' lexical entry
marks and lose deferred flows. Each synthesized application drives ordinary
`applyShape` directly, so its nested queries complete synchronously before the
next enclosing query.

Each callee needs an independent inference chain: sharing the first callee's
bindings would conceal different nested selections. Retain those chains on the
outer `InstanceArg`, link corresponding nested arguments to the first chain's
canonical decisions, and compare declaration identities recursively. Only the
first expression is lowered. All chains participate in semantic traversal and
sealing, so imported activations preserve inference and late-value checks without
mutating the exporting graph. Post-resolution cloning needs only the selected
runtime expression, as for direct instance arguments.

A nested argument holds an immutable derivation path. Each path entry snapshots
the selected function, flow type, size, and covering set at decision time.
`ContextualFlowType` contains nominal classes, unordered unions, and `?`; it is
separate from `DeclaredType` and used only for divergence. Cycle detection during
observation is local to the current value path. Candidate filtering and late
namespace checks use the same divergence rule and frozen observations.

Termination needs no depth bound. There are finitely many functions and class
covering sets. Along a derivation path, queries sharing one function and covering
set have non-increasing sizes and distinct flow types. For a fixed size and
covering set, only finitely many flow types exist. Thus every derivation path is
finite. A rejected candidate leaves alternatives available; a failed nested query
does not backtrack to a different enclosing selection.

`DerivedInstances`, `DerivedDeclarations`, `DerivedCaptures`, `DerivedAgreement`,
and `DerivedDivergence` cover selection, validation, captures, inherited and
aliased result inference, recursive agreement, and every divergence case.
`DerivedImport` and `DerivedImportIsolation`, with `DerivedLibrary`, cover
imported derivation, frozen nested selections, and independent importer state.
`DerivedGenericScopes` covers enclosing generic binders, captured result aliases,
inherited result positions, parameterless generic instances, and opaque nested
queries. `GenericOpacity` covers opaque type parameters in functions and classes.

### Contextual resolution performance

Completion metadata lives on potential site classes, not on every `Term`.
An empty completion allocates no helper object. Potential sites reuse one
worklist entry; completion records, derived chains, and query observers are
created on demand. Each module caches one instance-member index, and each request
bounds provider decisions by its module keys (or module/trigger pairs for parameter
queries). Investigate regressions above 2% and fix identified causes. The approved
measurement policy also requires recording unexplained regressions and suspected
causes while continuing implementation.

Measurements use separate scratch worktrees against `fdddc5842`, JDK 25, and an
identical temporary `ContextualBenchmark` runner invoked with
`sbt -batch 'hkmc2DiffTests/Test/runMain hkmc2.ContextualBenchmark'`. It warms shared
imports, then sequentially runs the same 125 non-WASM `newres` diff files without
a source `using` clause through `MainDiffMaker`. Allocation uses
`com.sun.management.ThreadMXBean.getCurrentThreadAllocatedBytes`; CPU uses
`getCurrentThreadCpuTime`. Wall time includes the harness and JavaScript execution.
Timed runs have no concurrent builds or tests, and every round has zero failures.
Each version has one JVM run; the later phases reuse an earlier baseline run.
These measurements check overhead on this subset, rather than establish a speedup
for HKMC2. They have no paired repetitions or confidence intervals. CPU time and
allocation count only the runner thread, excluding other threads such as the JIT
and garbage collector.

Phase 2 used twelve rounds, reporting medians of the last five:

| Metric (125 files) | Base | Phase 2 | Change |
| --- | ---: | ---: | ---: |
| Elapsed time | 7.407372000 s | 7.144443542 s | −3.55% |
| Current-thread CPU time | 1.409568 s | 1.320953 s | −6.29% |
| Current-thread allocated bytes | 2,671,442,464 | 2,699,115,096 | +1.04% |

For Phases 3–6, warmup was extended to 24 rounds after CPU time continued declining
in the initial Phase 3 run. The table reports medians of rounds 20–24 against the
same 24-round base measurement; parenthesized percentages compare with that base.

| Version | Elapsed seconds | CPU seconds | Allocated bytes |
| --- | ---: | ---: | ---: |
| Base | 7.064231750 | 1.241451 | 2,681,793,576 |
| Phase 3 | 7.237733584 (+2.46%) | 1.345219 (+8.36%) | 2,708,646,216 (+1.00%) |
| Phase 4 | 7.125541042 (+0.87%) | 1.267291 (+2.08%) | 2,701,078,608 (+0.72%) |
| Phase 5 | 7.137632667 (+1.04%) | 1.292066 (+4.08%) | 2,693,274,336 (+0.43%) |
| Phase 6 | 7.016793083 (-0.67%) | 1.228095 (-1.08%) | 2,698,203,216 (+0.61%) |

Phase 3 removed a duplicate local-parameter contextual-observer lookup. Phase 4
bypasses eta-expansion callbacks when no Abstract step exists. The remaining
regressions have no isolated cause. Suspicions include contextual classification
and worklist processing, imported generic observer lookups, and dispatch in the
shared namespace walk. JVM optimization and warmup also vary: the Phase 5 compiler
and measured subset were unchanged from Phase 4, yet their measurements differed.
These are hypotheses, not profiling conclusions, and remain optimization follow-up.

Phase 6 stays below 2% on all three measurements. Derivation state is allocated
only for contextual queries, with no derivation state on ordinary terms. The earlier
regressions and run variation remain recorded above; no semantic rule or invariant
was relaxed to meet the performance target.
Its elapsed-time difference from the base is about 47 ms across 125 files; the
available measurements do not distinguish a real speedup from JVM and run variation.
