# Extraction plan for PR #575

Status: proposed; no extraction branches or pull requests have been created.

## Scope and baseline

This plan decomposes [PR #575](https://github.com/hkust-taco/mlscript/pull/575),
“Compute erased types from new-resolution shape analysis”, as inspected on
2026-10-30. The source snapshot is `2a3d9933236da5b470a6f66b05d8a5bc6b4b7741`;
the target `hkmc2` snapshot is `aa2df379b12e6fcbefca76b7a5af8a2c881e8004`.
The local source and GitHub PR heads agree.

The remaining diff is **174 files, 6,650 additions and 1,624 deletions**:

| Category | Files | Added / removed lines |
| --- | ---: | ---: |
| Compiler Scala | 33 | 1,967 / 448 |
| Scala tests | 2 | 38 / 5 |
| MLscript sources and embedded golden output | 136 | 4,528 / 1,148 |
| Generated JavaScript | 2 | 16 / 20 |
| Language reference | 1 | 101 / 3 |

Of the 136 MLscript files, 62 change only their embedded golden output.
Consequently, file count is a poor measure of the number of independent changes.
The plan below follows behavior and invariants, splitting individual files where
necessary.

[PR #592](https://github.com/hkust-taco/mlscript/pull/592) is already in the
target. Do **not** extract its erased-value/signature split, builtin arity split,
lifter symbol tightening, unified term-erasure initialization, or original
cloned-class signature regression again. Their original commits remain in #575's
ancestry because #592 was squash-merged, but those changes are absent from the
current diff.

The proposed decomposition is **35 extraction PRs**, one conditional cleanup,
and the remaining shape-erasure PR. This is a deliberately fine-grained plan.
An extraction must still have a meaningful behavior or invariant of its own;
do not create inert infrastructure PRs merely to increase the count.

## What independently mergeable means

Every extraction targets `hkmc2`, includes its own tests and current golden
outputs, and must work without unmerged parts of #575. A prerequisite in the
tables means **wait for that PR to merge, then branch from updated hkmc2**.
It does not mean targeting another unmerged extraction branch.

A dash means no semantic prerequisite was identified by source inspection.
It is a standalone candidate, not a claim that an isolated patch has already
passed tests. None of these individual extractions has been built yet. The
complete source snapshot passed 1,165 tests, but that does not establish the
correctness of intermediate subsets.

Prefer explicit annotations in extracted regressions so that representation
fixes can be demonstrated before inference is enabled. Keep the original
unannotated variants for the final integration tests. Preserve a regression's
purpose when doing this: an annotation must not hide the very bug being tested.
If a proposed split cannot pass independently without a workaround, join it to
its actual prerequisite or retain it in #575.

Paths below use these repository-relative roots:

- **S**: `hkmc2/shared/src/main/scala/hkmc2/`
- **T**: `hkmc2/shared/src/test/mlscript/`
- **C**: `hkmc2/shared/src/test/mlscript-compile/`
- **J**: `hkmc2/jvm/src/test/scala/hkmc2/`

## 1. Small source and diagnostic corrections

These are good first extractions. They require no new representation inference.

| ID | Proposed PR | Prerequisites | Exact scope and independent acceptance check |
| --- | --- | --- | --- |
| E01 | Fix binary-operator application nodes in the parser example | — | In C/apps/parsing/{Parser,Rules,Tree}.mls, wrap binary operands in `Tree.Tuple` when constructing and matching `Tree.App`. Keep the parser and printer agreement in one PR. Exercise multiplication and mixed-precedence expressions; regenerate T/apps/parsing/{ParserTest,LoopExpressions,ParserErrorTest}.mls outputs as applicable. Exclude the EOF error fix. |
| E02 | Construct a valid error tree for trailing parser input | — | Only the final unexpected-token branch in C/apps/parsing/Parser.mls: produce `Tree.Error(Tree.Sequence(tree), message) :: Nil`. Exercise the trailing-input/error path in T/apps/parsing/ParserErrorTest.mls and verify the preserved partial tree. Reconcile the shared file with E01 if it has already landed. |
| E03 | Use a list accumulator in the fish benchmark | — | Replace `showl(xs, "")` by `showl(xs, Nil)` in C/nofib/fish.mls. Compile the port and run its existing nofib regression. No compiler changes. |
| E04 | Correct the Haskell string aliases in two nofib ports | — | Add `type String = List[Char]` in C/nofib/{lambda,lastpiece}.mls. These are two instances of the same porting error; keep them together. Compile and run both ports without changing the compiler or expected benchmark results merely to accommodate the aliases. |
| E05 | Pass class objects to reflection fixtures | — | Use `A.class` / `Pair.class` for `ConcreteClassSymbol` in T/block-staging/PrintCode.mls and T/newres/ShapeFixture.mls. Distinguish the constructor function from the class object. Check the existing generated-code and shape expectations. |
| E06 | Declare the public open-method contracts in library fixtures | — | The signature additions in C/Iter.mls, C/ObjectBuffer.mls, and `NonLocalReturn.ret` in C/Runtime.mls. Keep actual parameter/result choices visible for review; this is a library-contract change, not an inferred-type implementation. Compile these libraries and run their consumers, including handlers and object-buffer tests. |
| E07 | Declare the types of exported mutable storage in fixtures | — | The mutable-slot annotations in C/{Runtime,TreeTracer,ModuleReceiverCapture}.mls and C/apps/Accounting.mls. Retain intentional `Any` and nullable slots. Include matching declaration-only adjustments in existing tests when they document the same contract, but leave new exposure diagnostics in #575. Compile and run the affected library/application consumers. |
| E08 | Locate representation-conversion diagnostics at their source | — | S/codegen/Lowering.scala: the constructor-field name fallback and `castTo` value-location fallback. S/codegen/wasm/text/WatBuilder.scala: the `loc` argument and propagation in `castConserve`. Extract only diagnostic-location changes, not the surrounding undefined or physical-signature changes. Use explicitly annotated failing field, argument, and return conversions to verify useful spans on JS and Wasm. |

Suggested focused runs: `catest pars` then `adtest parsing/` for E01/E02;
`cntest fish` then `ndtest fish` for E03; the corresponding `lambda` and
`lastpiece` selectors for E04. The general prerequisites and full-suite gate
below apply to all entries.

## 2. Resolution and representation fixes that do not need inference

| ID | Proposed PR | Prerequisites | Exact scope and independent acceptance check |
| --- | --- | --- | --- |
| E09 | Give builtin applications consistent result information | — | S/semantics/BuiltinOperatorResults.scala, `NewResolver.builtinApplication` and its primitive-interface helpers, the Elaborator application hook, `ErasedType.builtinOperatorResult`, and the corresponding `Result.erasedType` case in Block.scala. Keep the resolver and IR rules together. Test arithmetic, comparisons, string concatenation, unknown operands, and operand-forwarding operators; retain the Wasm unknown-result rule. Use T/newres/CurriedFunctions.mls, the affected PartialApps tests, codegen/CheckedCasts.mls, and wasm/BuiltinOperators.mls. Review the documented Int-overflow approximation explicitly; this is the existing workaround, not a new overloading design. |
| E10 | Separate async body payloads from callable Promise results | — | Extract the async part of `Erasure.bodyResultType`, completed body-result storage in Elaborator.State, `copyBodyResultType` in Cloner, and the Lowering consumers. Callable signatures describe Promise; explicit and implicit returns are coerced to the annotated payload. Use existing async tests and the AsyncResult pattern in T/slop/ClonedBindings.mls, with annotated payloads where needed. Keep body-result state with the defining unit so imported/cloned bodies remain valid. Do not enable inferred results. |
| E11 | Model generator calls as iterators | E10 | Extend the preceding wrapper handling to generators: `TermDefinition.generatorAnnotation/resultWrapperAnnotation`, `WrappedResult`, Iterator lookup, and NewResolver's callable-result wrapping through all curried lists. Include the generator erasure branch in the same PR so resolution and IR agree. Remove the relevant fixme in T/newres/GeneratorResults.mls; extract the GeneratorResult cloned-pattern test and the generator override case from T/slop/Erasure.mls. Preserve the current treatment of combined async/generator annotations. |
| E12 | Preserve constructor-companion signatures through cloning | — | Initialize source ClassCtorSymbols from their class's physical parameter lists and nominal result in Erasure, using declared parameter types on this base. Include the deferred ClassCtorSymbol initialization, generated-constructor initialization in Lifter, and constructor erasure copying in Cloner/SymbolRefresher. All callers must obey write-once initialization, including legacy resolution. Test annotated private and auxiliary constructors, forward classes, and cloned constructors. Do not re-extract #592's already-merged ordinary-function cloning fix. |
| E13 | Give generated function definitions function signatures | — | `FunDefn.withFreshSymbol` in S/codegen/Block.scala: retain the parameter-list structure and parameter representations for generated callables, while getters remain value slots. Test lambdas assigned to annotated function slots without a redundant Function cast, including the relevant codegen/ErasedTypes and generated-function naming cases. Exclude unrelated changes to Block.scala. |
| E14 | Enforce override representations and their physical Wasm signatures | — | The signature-comparison checks, inherited unannotated parameter/result handling, and variadic-layout correspondence in Erasure; the matching physical parameter/result handling in wasm/text/{Ctx,WatBuilder}.scala. Use existing declarations rather than inferred base types. Test annotated mismatches, inherited unannotated override slots, direct and virtual calls, narrower reference results, abstract stubs, and trailing parameters. Take the appropriate blocks from T/wasm/VirtualMethods.mls and T/slop/VariadicParams.mls. Keep exposed-open-member annotation policy in #575, since that policy uses completed inference observations. |
| E15 | Let undefined inhabit every runtime representation | E14 | `Result.isUndefined`, coercion and cast invariants, Block.returnType and Normalization joins, Wasm default-value emission at argument/field/local/result boundaries, and nullable nominal storage. Include the undefined documentation and relevant UnsafeUndefined test adjustment. Exercise all four unboxed types and nominal references with explicit annotations, plus DPE-generated placeholders. Assert only defined results/effects: the materialized undefined value is backend-dependent. This PR must not quietly make `null` or incompatible joins behave like undefined. |
| E16 | Stop treating abortive splits and exhaustive loops as normal results | — | NewResolver.resultFlow's ordered split traversal, irrefutable patterns and loop continuation handling; Elaborator's guarded Unit publication; and Normalization's unreachable-continuation handling. Test an explicitly typed early return followed by an unrelated unreachable value, an exhaustive repeating/returning loop, and nested returns. Adapt the relevant T/newres/wasm/Erasure.mls blocks and T/codegen/ScopedBlocks.mls. Keep resolver and lowering changes together. |
| E17 | Coerce tuple-extracted arguments into their declared slots | — | S/codegen/OptionalParams.scala: `bindFromTuple` coercions and the representation of the once-evaluated `optionalArg` temporary; Lowering's rest/trailing extraction assignments. Test required and omitted optional slots, constructor spreads evaluated once, and tail-call rebinding. Use annotated slots, so the boundary error is observable without inference. Keep omission-as-null semantics unchanged. |
| E18 | Align typed arguments with optional and trailing parameter positions | E17 | `Lowering.expectedParamTypes(ps, args)` and its call sites. Fixed argument lists align from both ends; unknown spreads use only the known required prefix and rely on extraction coercions for other slots. Extract integerTail, typedLayout and forwardedTail from T/slop/VariadicParams.mls. Leave override-specific cases with E14. |

E10 and E11 are intentionally ordered by feature. Landing generator result shapes
while retaining a payload-shaped callable signature would leave the compiler's
two views inconsistent. Similarly, E14 supplies the physical result context
needed by E15's backend emission.

Useful existing suites: `dtest codegen/ErasedTypes`,
`dtest newres/GeneratorResults`, `sdtest ClonedBindings`,
`sdtest VariadicParams`, `wdtest VirtualMethods`, and the relevant
`newres/wasm/Erasure` blocks moved into dedicated slop regressions as necessary.
Do not move inference-dependent expectations into an earlier PR unchanged.

## 3. Optimizer improvements and correctness fixes

Several optimizer changes were exposed by more precise source types but also
apply to existing explicitly annotated programs. Extract the safety restrictions
before broadening the set of casts/constructors through which fusion operates.

| ID | Proposed PR | Prerequisites | Exact scope and independent acceptance check |
| --- | --- | --- | --- |
| E19 | Eliminate casts made redundant by propagation and inlining | — | Only the Cast handling in BlockSimplifier.applyPath/applyResult. Recheck the rewritten operand, remove a proven redundant checked cast, preserve narrowing checks and evaluation order, and materialize a path temporary when needed. Use cast regressions in T/codegen/ErasedTypes.mls and T/opt/ConstantFolding.mls, adding a focused slop regression only where current coverage is insufficient. |
| E20 | Preserve checked argument evaluation when propagating partial calls | — | The unsaturated direct-member-call case in BlockSimplifier. Evaluate checked/effectful arguments at the original site and snapshot preceding arguments before later effects. Extract checkedPrefix/capturePrefix from T/opt/PureCallPropagation.mls and discardPartial from T/wasm/Casts.mls. Verify discarded partial applications still execute failing checks and later source-variable mutation does not change captured arguments. |
| E21 | Preserve constructor and superclass effects during elision | — | `ConstructorElision.isHarmless/harmlessClass`, its DCE use, and fusion's constructor/qualifier/argument-replay eligibility checks. Missing definitions, inheritance cycles, checks, calls and other unproved effects stay conservative. Extract CastEffect and EffectfulParent/Child tests from T/slop/Erasure.mls and exercise both DCE and fusion. Keep field-position proofs for E22. |
| E22 | Validate the parameter-to-field mapping before field fusion | E21 | `ConstructorElision.preservesParameterFields` and its use in fusion eligibility. A constructor can be harmless yet replace or reassign a field, so effect freedom alone is insufficient. Check the current IR layout, pre-constructor, parameter writes and actual field stores. Extract ChangedField and Captured/readCaptured from T/slop/Erasure.mls. |
| E23 | Preserve ordered match selection and producer-specific default layouts in fusion | E21, E22 | `DeforestFusionSolver.matches/selectedBranch`, its eligibility use, and the corresponding Rewrite branch selection and BranchId changes. Unknown earlier predicates must block choosing a later arm; inheritance and tuple/Object tests must agree with runtime matching. A shared default body must still have different field parameters for different constructor layouts. Extract the Parent/Child, arrayKind/objectKind, and A/B/Target default tests from T/slop/Erasure.mls. |
| E24 | Keep stored constructors unfused when their container cannot hold the replacement | — | `FlowWebComputation.impliedProducers`, DPE's empty callback, the unconsumed-constructor roots, and the field-storage constraints in Deforest.scala. Preserve an unfused nominal field's declared representation; do not store a replacement closure into it. Extract the two H/Box cases in T/deforest/erasedTypes.mls: nominal field stays unfused, Any field permits fusion. Verify propagation through nested containers. |
| E25 | Type generated deforestation callables and nullary closure temporaries | — | The erased signatures for branch/rest functions and the `deforest$lam` temporary's type in Rewrite.scala. Preserve the two physical parameter lists of branch functions and the captured-value list. On this base use the original slots' representations; E29 later substitutes retyped slots. Exercise an explicitly annotated nullary singleton match and inspect its generated signature/temporary. |
| E26 | Preserve the result slot when fusion replaces a return with a call | E25 | The scoped enclosing-return context and `returnCall` at fused matches and extracted rest calls in Rewrite.scala. Coerce the replacement call to the original annotated result. Test boxed reference/Int returns and nested extracted bodies. Carry T/slop/wasm/loose/DeforestPrimitiveReturn.mls as a known failing regression, not as a claimed fix: an unknown closure result still cannot represent an unboxed Int32 without further calling-signature work. |
| E27 | Keep flow-analysis effects separate from runtime values | — | The separate `unknownEffect` fallback and the distinction between effect and value strategy variables in FlowAnalysis.scala. Introduce each bookkeeping part with its consumer: E29 adds the runtime-slot collection, while this PR fixes the fallback that currently mixes effects into primitive value flow. Exercise effect-analysis suites and the counted getter in T/slop/EffectValueFlows.mls, retaining effects and conservative eta behavior. No representation inference is needed. |
| E28 | Keep erased function signatures in sync with eta expansion and DPE | — | The function-signature part of PolyInstantiationRewrite's replacement-symbol machinery, `etaTargetLists/etaParamType`, and FlowAnalysisBasedRewrite's complete rewritten signatures. Use fresh symbols for changed write-once signatures, including in-place roots and copied functions; preserve optional/rest list structure. Add SymbolRefresher helpers only as used here. Extract the typed eta example from T/opt/EtaExpansion.mls, annotating g and f's results as necessary; retain DPE and mixed-target coverage. Leave value-slot retyping to E29. |
| E29 | Retype every slot and function instance affected by deforestation | E15, E21–E28 | The remaining `StratVar.instantiationId/symbolFlows` bookkeeping, value-symbol replacement in PolyInstantiationRewrite/SymbolRefresher, and Rewrite's producer-based parameter/result/local/capture typing, instance-copy selection and boundary coercions. Exercise mono/poly recursion, identity forwarding, nested instances, field projection, mixed fused/unfused sources, and effectful non-returning paths from T/deforest/erasedTypes.mls. This is one representation-changing transformation: do not land parameter retyping while leaving its locals, return slots, captures or callers stale. |
| E30 | Prove casts against all incoming producers before allowing fusion | E29 | `CastConsumer`, propagation/copying/solver invalidation, the required context plumbing, and removal of casts whose operand representation actually changes through fusion. Keep narrowing casts needed for physical Wasm slots when fusion does not change the operand. Extract makeOpaqueBox/mixedBox and mixed-source cases in T/deforest/erasedTypes.mls plus T/slop/wasm/loose/FlowCastProofs.mls. A single unknown or incompatible producer must invalidate the proof, including across copied/recursive schemes. |

E29 is likely the largest extracted compiler PR. Splitting its implementation
into “parameters first, locals later” would knowingly violate the one-
representation-per-slot invariant. Its review should instead follow:

1. how solved flows retain the full instantiation path;
2. how replacement symbols and signatures are allocated before use;
3. how each changed boundary is coerced, including captured values;
4. why a value replaced by undefined cannot actually be produced.

The last point deserves explicit scrutiny. The existing
`coerceIntoFlowTypedSlot/coerceToOr` path retains an expression's effects and
substitutes undefined for an unrelated, unproducible result. Absence of observed
producers is only sufficient if the analysis is complete for that path. Do not
generalize this into a fallback that hides type errors, or use passing tests as
the sole proof. If that invariant cannot be established, retain a fixme or
reconsider the extraction boundary.

Introduce `coerceToOr` with its real E29 consumer, not as an earlier unused API.
Similarly, do not add empty `retypedVariables` hooks or unconsumed flow tables
in a separate “preparation” PR. E28 may implement only the function replacement
interface it actually needs; E29 can extend it.

Useful suites: `dtest opt/`, `dtest dead-param-elim/`,
`dtest deforest/`, `sdtest Erasure`, `sdtest EffectValueFlows`,
`sdtest wasm/loose/FlowCastProofs`, and `wdtest DeadConstructorElim`.
The two new `slop/**/loose/.mls` configuration files should travel with their
first actual consumer, preserving inherited test directives.

## 4. Mutable-field and record improvements

Do not turn precise mutable reads on while omitting assignment or interface
exposure inputs. That would make the intermediate compiler trust an initializer
after another value can have replaced it.

| ID | Proposed PR | Prerequisites | Exact scope and independent acceptance check |
| --- | --- | --- | --- |
| E31 | Follow only surviving record fields during interface exposure | — | The reverse, shadow-aware traversal and contextual memoization in InterfaceExposure's record case, initially for initializer exposure. Preserve unknown-key conservatism and nested spread contexts. Re-express overwrittenSource, direct/spread replacement, and computed-key cases from T/slop/strictres/MutableFields.mls using escaping callbacks, so they test resolution/exposure without the later missing-field-annotation diagnostic. Do not take assignment-flow code yet. |
| E32 | Account for every write when resolving and exposing mutable fields | E31 | NewResolver's `assignField/writeField/listenAssignedValues/assignableTargets`, projected lookup, class/record read paths, Elaborator's assignment hook, owned caches, and InterfaceExposure's unknown writes and assigned-value traversal. Include the structural input/output representation and constraints: RecordTypeShape/MemberLookup.Typed carry TypeArgument pairs through identity, substitution, support, transport, intersections and reads; `declaredField`, `constrainRecord` and `listenFieldInput` propagate writes negatively and reads positively. Exercise classes and existing `mut {f: T}` syntax, including existing interval type arguments, before introducing per-field syntax. Test projections, all receiver forms, multiple classes, escaping callbacks, late assignments, nested spreads, immutable-copy controls and both structural constraint directions. Adapt TypeRelationTest while preserving its bounded-growth property. Exclude erasure observations and the requirement to annotate exposed fields. |
| E33 | Support explicit input/output bounds on mutable record fields | E32 | The typeArgument elaboration helper, direct field-bound syntax, missing-output provenance, and immutable-field rejection. Test `mut {f: in S out T}`, parenthesized bounds, input-only/output-only fields, nested negative positions, aliases and recursive interfaces. Use the relevant MutableFieldVariance blocks with whole-record mutability until E34 lands. Do not claim complete structural subtype checking or add it in this extraction. |
| E34 | Allow individual record fields to be declared mutable | E32, E33 | The `RcdField.mut` metadata, value/type elaboration, pretty-printing, cloning, RecordShape lookup, exposure and structural-interface flag threading, and Lowering's `allocatesMutable`. Support `{mut f: value, label: other}` end to end, including its type form and spread copies. Extract the mixed-field and copied-record tests from MutableFields, the MutableRecord pattern from ClonedBindings, and the BadMut expectation change. Move the corresponding reference documentation here. Keep source erasure deferral for record slots in #575. |

E32 keeps direct assignments and writes admitted by declared interfaces together.
Separating them would let a newly precise read ignore a write through a
structural interface. The input/output representation is therefore used by its
actual readers and writers in the same PR. This is the other deliberately larger
extraction, alongside E29.

E32's tests should demonstrate incorrect member resolution or lost exposure,
not merely report an internal inferred representation. Many current
MutableFields tests instead assert the later erasure diagnostic; those blocks
stay with #575. In particular:

- assigned callbacks receiving unknown external arguments can test E32 directly;
- missing annotations on an exported mutable class field test the final erasure
  policy and cannot be moved to E32 unchanged;
- ordinary mutable-record variance tests can be moved to E32 using whole-record
  syntax, without prematurely introducing E34;
- per-field values and their full type semantics must be present together when
  E34 lands.

E33/E34 are language-feature reviews. They preserve the syntax and behavior
already proposed by #575; extraction does not authorize inventing further
syntax, changing dispatch, or extending the public library API.

Use `dtest newres/Records`, the appropriate split blocks from
`sdtest strictres/MutableFields` and `sdtest strictres/MutableFieldVariance`,
and the existing TypeRelationTest for bounded recursive intersections. New
files belong under T/slop/. Keep any genuine remaining resolution limitations
as fixmes rather than weakening their expectations.

## 5. Test consolidation and one optional cleanup

| ID | Proposed PR | Prerequisites | Exact scope and independent acceptance check |
| --- | --- | --- | --- |
| E35 | Consolidate optional-binding regressions without losing coverage | E15, E17, E18 | Reconcile T/slop/OptionalBinding.mls and T/slop/strictres/OptionalNull.mls into T/slop/strictres/OptionalBinding.mls, along with the duplicated tail-recursive case removed from strictres/OptionalParams.mls. Audit cases one by one: omission, supplied null/undefined, lambdas, currying, spreads, tail recursion, closures, constructor elimination and dynamic construction. Keep typed-extraction cases with E17/E18 initially; consolidate after they land. Do not copy current golden output into an older compiler or treat unsafe.undefined observations as new semantics. |
| E36 (conditional) | Remove the unused Runtime Int31 addition prototype | — | The deletion of `Runtime.plus_impl` at the end of C/Runtime.mls and its generated output. First check callers on the extraction base and confirm removal of the exported helper is intended. The `wasm.plus_impl` intrinsic is a different symbol and must remain. If the public-contract removal is not intended, omit this extraction and resolve the three-line deletion explicitly in the residual PR. |

E36 is not a prerequisite for the compiler improvements. E35 is optional as a
separate review if the test moves prove inseparable from their behavior changes;
in that case distribute the cases to their owning PRs and account for every
removed scenario. Neither cleanup is justification for dropping regression
coverage.

## 6. What remains in #575

Keep the actual shape-erasure feature as one coherent final change:

- compilation-unit-owned ErasureInputs, ErasureDeclarations and completed
  snapshots, with observation registered before interface exposure;
- source-slot initialization deferred until erasure, including pattern binders,
  named-tuple/record declarations, generated source fields, handler/lambda
  parameters, and the elaborated temporary saved by `set ... in`;
- contextual candidate interpretation while resolution is open, followed by
  pass-local mapping and joins of all completed evidence in Erasure;
- preservation of explicit signatures and moduleful declarations, physical
  parameter-list structure, stored function values and class-object distinctions;
- inferred unannotated values, parameters, fields and results, including mutable
  assignments, explicit returns and all four unboxed numeric types;
- the observation-dependent open-member and exposed-mutable-field checks, plus
  inference-specific integration with the already-extracted override rules;
- J/ErasureInputsTest.scala, which uniquely checks that worksheet/import
  consumers do not mutate the defining unit's completed observations;
- inference-specific regressions, documentation and genuinely resulting golden
  updates.

Do not split this feature into “bindings”, then “parameters”, then “results” by
temporarily assigning unknown representations to the other slots. That would
create incompatible intermediate calling boundaries and require temporary
behavior not present in the intended design.

The main compiler files left should be Erasure.scala, ErasureInputs.scala,
NewResolver.scala, NewResolverState.scala, Elaborator.scala, Pattern.scala,
Symbol.scala and the source-record initialization part of Term.scala. This is
an expected boundary, not a promised line count before the extractions are
built and merged.

Retain the inference portions of T/newres/{Erasure,wasm/Erasure}.mls,
codegen/ErasedTypes.mls, wasm/ReplImports.mls, the strict mutable-field cases,
and the loose worksheet tests. The final tests must still cover:

- empty evidence versus an explicit Unknown candidate;
- Unknown joined with references versus an incompatible unboxed primitive;
- undefined contributing no representation constraint;
- forward references, aliases, recursion, multiple callers and early returns;
- explicit annotations, separate signatures, generic substitution and modules;
- exposed definitions, mutable writes, imports and later worksheet blocks;
- getters, currying, constructor fields, handlers, lambdas and stored functions.

The source snapshot's WasmScratch.mls contains only directives/blank lines, not
the original reproducer. Use durable erasure regressions for the acceptance
case; do not cite that empty scratch file as evidence that inference works.

Known failing regressions must stay visible with the appropriate owner:

- the inferred result naming a class inside a cloned function body stays with
  the core inference/cloning integration;
- Wasm session classes whose fields reference other session classes remain
  worksheet/import fixmes;
- an unboxed result returned through a deforestation-generated closure remains
  with E26/E29's regression coverage;
- changed override parameter layouts remain an explicit unresolved test beside
  E14, rather than becoming an invented language rule.

Adding erased signatures to IR Call nodes is a separate planned follow-up,
outside this extraction plan. It must not become an unannounced prerequisite
for merging these existing changes.

## 7. Shared-file ownership map

Use this map when taking hunks; do not copy an entire shared compiler file.

| Files under S unless otherwise specified | Owners |
| --- | --- |
| codegen/Block.scala | E09, E13, E15; E29's coerceToOr API |
| codegen/BlockSimplifier.scala | E19, E20 |
| codegen/DeadConstructorElim.scala | E21, E22; context plumbing with E30 |
| codegen/DeadParamElim.scala | E24's flow-web callback; context plumbing with E30 |
| codegen/ErasedType.scala | E09 |
| codegen/Erasure.scala | E10–E12, E14; remaining inference and exposure policy in #575 |
| codegen/EtaExpansion.scala | context plumbing with E30 |
| codegen/FlowAnalysisBasedRewrite.scala | E28; context plumbing with E30 |
| codegen/Lifter.scala | E12 |
| codegen/Lowering.scala | E08, E10/E11, E17/E18, E34 |
| codegen/OptionalParams.scala | E17 |
| codegen/PolyInstantiationRewrite.scala | E28's function replacement; E29's complete value/instance retyping |
| codegen/SymbolRefresher.scala | E12; E28/E29 helpers as used |
| codegen/deforest/Deforest.scala | E21–E24 |
| codegen/deforest/Rewrite.scala | E23, E25/E26, E29/E30 |
| codegen/flowAnalysis/FlowAnalysis.scala | E27, E29, E30 |
| codegen/flowAnalysis/FlowWebComputation.scala | E24 |
| codegen/wasm/text/{Ctx,WatBuilder}.scala | E08, E14/E15 |
| semantics/BuiltinOperatorResults.scala | E09 |
| semantics/Cloner.scala | E10–E12, E34 |
| semantics/Elaborator.scala | E09–E11, E16, E32, E33/E34; source initialization/observation in #575 |
| semantics/ErasureInputs.scala | #575 |
| semantics/InterfaceExposure.scala | E31/E32; E34 flag threading |
| semantics/NewResolver.scala | E09, E11, E16, E32–E33; E34 flag threading; observations in #575 |
| semantics/NewResolverState.scala | E32's caches; erasureInputs in #575 |
| semantics/Pattern.scala | #575 |
| semantics/Shape.scala | E11, E32–E34 |
| semantics/Symbol.scala | E12; saved-source-temporary documentation in #575 |
| semantics/Term.scala | E10/E11, E34; source record initialization in #575 |
| semantics/TermImpl.scala | E34 |
| semantics/TypeShape.scala | E32 |
| semantics/ucs/Normalization.scala | E15, E16 |
| J/TypeRelationTest.scala | E32/E34 API adaptations; retain the original bounded-growth property |
| J/ErasureInputsTest.scala | #575 |
| doc/reference.md | E09, E14/E15, E32–E34 and the final inference sections, with each behavior |
| C/Predef.mjs and C/Runtime.mjs | Regenerate for each owning extraction; never transfer their final snapshots wholesale |

Other changed tests fall into three categories: focused regressions assigned
above, source adaptations to the final inferred/exposed representations, and
golden-only changes. In particular, explicit Any annotations that keep a
narrowing test meaningful belong with the change that would otherwise erase
that test's boundary. Constructor-facet fixture corrections belong to E05;
changed diagnostics from newly observed builtin results belong to E09; missing
public-field/open-member annotations belong to their contract or exposure PR.
Do not collect all these cases into a generic “update tests” PR.

## 8. Extraction and merge procedure

1. Keep the source snapshot above as the reference for the intended final
   behavior. For each selected ID, create a branch such as
   `codex/pr575-parser-operator-tuples` from current `hkmc2`, after its
   prerequisites have merged.
2. Extract the smallest complete implementation, documentation and regression
   set. Use the shared-file map. The historical commits are research aids, not
   cherry-pick units: `b87501d07`, `081891b34`, `65660c479` and the merge
   resolutions each mix multiple subjects.
3. Demonstrate the issue independently, preferably with an existing .mls test.
   For new tests, use T/slop/ and choose the right strict/loose and JS/Wasm
   configuration. Use annotations to isolate representation-preservation bugs
   from the still-unmerged inference feature.
4. Validate the extraction against its own base, review all generated output,
   and commit it using a command-scoped Codex identity. Each PR description
   states the trigger, changed behavior, invariant, tests and any retained
   fixme. Do not add new public contracts under the guise of conflict resolution.
5. After that PR merges, fetch the actual new `hkmc2` commit and merge it into
   this branch. Resolve adaptations by preserving both the extracted fix and
   the remaining inference logic. Do not delete the implementation from this
   branch to shrink the diff.
6. Recompute `git diff hkmc2...HEAD`, record the merged PR link/status in this
   plan, and inspect what remains. Validate any conflict resolution that changes
   code. The extraction is complete only when its independent behavior is
   upstream and its corresponding diff has disappeared here.

GitHub may squash the extracted PRs. Merge the real upstream commits back;
their original extraction commit IDs are not a substitute for that ancestry.
The earlier #592 reconciliation used an unchanged-tree merge only after exact
tree equality was established. Do not apply that strategy blindly to future
extractions, whose patches may have been adapted to a smaller base.

A practical order is:

1. E01–E08, then E13, E19 and E20 for quick independent reviews.
2. E09–E12, E14–E18 for resolution/backend correctness prerequisites.
3. E21–E30 in prerequisite order for optimizer work.
4. E31–E34 in prerequisite order for mutable records.
5. E35, decide E36, then review the reduced #575.

The optimizer and mutable-record sequences need not block one another.
Whenever two ready entries only share golden output, merge one and regenerate
the other's outputs rather than creating an artificial dependency.

## 9. Validation and review gates

For every code/test extraction:

- Use Metals for quick Scala inspection and compilation feedback.
- Keep a persistent SBT shell. Before individual diff tests, run `ctest`;
  before Wasm diff tests also run `cwtest`. Run the relevant `catest` or
  `cntest` before application/nofib consumers.
- Use `dtest` for the main suite, `sdtest` for slop, `wdtest` for the Wasm
  suite, and `adtest` / `ndtest` for the corresponding application/nofib tests.
  Main-suite newres/wasm tests still use `dtest`.
- Finish with `hkmc2AllTests/test`. A focused pass or Metals compile is not a
  substitute. Commit the latest generated .mls/.mjs output with the owning PR.
- Read the complete PR diff, including test directives, removed test blocks,
  expected errors, evaluation counts and generated casts. A regenerated golden
  file is evidence to review, not automatic proof of correctness.
- Inspect whitespace changes against contributor history. Preserve intentional
  indented blank lines and existing end markers; do not run a sweeping formatter.
  Do not create a standalone PR for compiler-internal line-number churn or the
  existing human-authored EOF spacing in wasm/DeadParamElim.mls.

Use Scala unit tests only for properties .mls tests cannot reliably observe.
The completed-observation isolation test belongs to the final core; the
existing recursive type-relation test remains useful when changing record
interfaces. Do not add unit tests that merely assert an internal erased-type
field equals the value assigned by the implementation.

This planning change itself is documentation-only. It does not rerun the
compiler suite or claim that the proposed intermediate branches are validated.
