# Extraction plan for PR #575

Status updated 2026-11-07: E01–E03, B01–B05, E08, E14, E17–E18, structural
Iterator, E27, E31, E35 and E36 are merged upstream; upstream's cast refactor
covers E19. The branch incorporates `hkmc2` through `4967bcd7d`. The approved
split retains E12 and E32 with shape-based erasure and moves E29–E30 and E33–E34
to separate follow-ups after #575. E20–E24 remain independent fixes. The
historical batch dependencies below describe the original extraction order,
subject to this revised scope.

## Scope and baseline

This plan decomposes [PR #575](https://github.com/hkust-taco/mlscript/pull/575),
“Compute erased types from new-resolution shape analysis”. The original analysis
on 2026-10-30 used source snapshot `2a3d9933236da5b470a6f66b05d8a5bc6b4b7741`
and target `hkmc2` snapshot `aa2df379b12e6fcbefca76b7a5af8a2c881e8004`.
These remain the references for the detailed work-item inventory below.

At that original snapshot, the diff was **174 files, 6,650 additions and 1,624
deletions**; these are historical totals, not a count of the remaining work:

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

The revised unit of review is a **coherent theme with a few hundred changed
implementation lines**, counting additions and removals rather than net growth.
Count Scala changes and substantive MLscript fixture changes separately from
regression inputs, embedded golden output and generated JavaScript. Extensive
diff-test updates are acceptable when they follow from that bounded source
change. Do not split a theme into tiny PRs solely to reduce its snapshot diff.

## Completed extractions

| Work item | Merged PR | Outcome |
| --- | --- | --- |
| E01 | [#594](https://github.com/hkust-taco/mlscript/pull/594) | Parser/operator construction and printing agree on tuple arguments; three golden files updated. |
| E02 | [#595](https://github.com/hkust-taco/mlscript/pull/595) | Corrected the defensive EOF error payload and stack result. Current parsing consumes all tokens, so existing tests do not exercise that fallback and goldens are unchanged. |
| E03 | [#596](https://github.com/hkust-taco/mlscript/pull/596) | Fixed the fish formatter's list tail and added empty/singleton/multiple-item regressions. Both nonempty cases failed before the fix. |
| B01 (E04–E07) | [#597](https://github.com/hkust-taco/mlscript/pull/597) | Corrected library and fixture declarations; override-fixture annotations stay with B05 and E36 remains deferred. |
| B02 (E09, E16) | [#598](https://github.com/hkust-taco/mlscript/pull/598) | Resolved builtin results and abortive expression flow, with independent JS/Wasm regressions. |
| B03 (E10–E11) | [#599](https://github.com/hkust-taco/mlscript/pull/599) | Separated async/generator body payloads from Promise/Iterator call results, including cloning and currying. |
| B04 (E13, E25–E26, E28) | [#600](https://github.com/hkust-taco/mlscript/pull/600) | Shared immutable callable signatures across definitions and their symbols; preserved them through copying and calling-convention changes. E12 stays with B07. |
| E08 | [#601](https://github.com/hkust-taco/mlscript/pull/601) | Located representation-conversion diagnostics at their source. |
| E14 | [#602](https://github.com/hkust-taco/mlscript/pull/602) | Combined representation inheritance with source argument-layout checks, Wasm signature checks and exposed open-member annotation requirements. |
| E15 / B05 | [#606](https://github.com/hkust-taco/mlscript/pull/606) | Undefined has the representationless `Nothing` type; Wasm materializes placeholders, including non-null nominal references. Upstream also adapted ordinary bottom-typed expressions and return handling. |
| E17–E18 | [#610](https://github.com/hkust-taco/mlscript/pull/610) | Typed tuple extraction and positional alignment use a shared `ArgumentLayout`, including under-applied calls and optional slots before trailing parameters. E35's test consolidation remains on this branch. |
| E19 | [#614](https://github.com/hkust-taco/mlscript/pull/614) | Upstream's `CastPath`/`CastResult` split and `RefinesCasts` supersede the original redundant-cast patch. No separate E19 extraction remains. |

E01–E03 and B01 each passed `hkmc2AllTests/test` with 1,155 tests; B02 passed
with 1,157. The upstream snapshot `1ad11c54c` contains
those five merges. Those upstream commits have been integrated back into this
branch, including E03's added formatter regressions. Integration commit
`23aa31d66` passed `hkmc2AllTests/test` with 1,165 tests. The B01 merge preserves the
implementation and test tree exactly; only this plan changes. The B02
integration (`5058fd321`) adds its upstream regressions and passed all 1,167 tests.
The B04 integration used upstream snapshot `5091705f5`, containing B03 (`ca9b82d08`) and
B04 (`5091705f5`). This integration adopts the shared `FunDefn.Signature` and
`ErasedResult` representation while retaining inferred signatures and the
representation-changing deforestation work below. The old body-result map is
removed because callable signatures now carry and clone their payload types.
Metals compilation and `hkmc2AllTests/test` passed on the integrated branch;
the full suite ran 1,172 tests. The incoming JS cast-comment fixtures use broad
input annotations and an unchecked nominal receiver so inference and redundant
cast elimination preserve the coercions those rendering tests exercise.

## Reduced #575 and independent follow-ups

### Current split for review

The core branch retains inference, constructor-companion signatures and the
complete mutable-field read/write model. Its record tests use the existing
whole-record `mut {...}` syntax and interval type arguments through aliases.
The new field declaration syntax and the optimizer transformation belong to
separate follow-ups:

| Work | Branch | Merge order |
| --- | --- | --- |
| E29–E30: deforestation retyping and cast proofs | `codex/pr575-deforestation-retyping` | After #575 |
| E33–E34: mutable-record declarations | `codex/pr575-mutable-record-syntax` | After #575 |
| E20: partial-call arguments | `codex/pr575-partial-call-arguments` | Independent, targeting `hkmc2` |
| E21–E23: constructor and match safety | `codex/pr575-constructor-safety` | Independent, targeting `hkmc2` |
| E24: fusion across container storage | `codex/pr575-fusion-storage` | Independent, targeting `hkmc2` |

The two new follow-ups share the reduced #575 as their review base. Their PRs
must be retargeted to `hkmc2` after #575 merges. They do not depend on each other.
Keep all E29–E30 slot and caller adaptations together when integrating the
deforestation follow-up.

Against `4967bcd7d`, the core contains **832 changed compiler Scala lines across
14 files** (668 additions, 164 deletions), plus **42 changed Scala test lines
across two files**. E31 removes the three overwritten-record exposure fixmes.
Without E30's cast proofs, five constructor regressions pass conservatively
again. The remaining constructor/match failures retain their assertions and
targeted E21–E23 fixmes, including the optional-field fusion case newly exposed
by the upstream optional-binding consolidation and its dependent worksheet
check. Reconcile those markers when the constructor-safety PR lands. A fourth
targeted fixme in `T/deforest/simple.mls` records the recursive result-slot
failure that E29 resolves. E24's nominal-storage regression moves with the
deforestation follow-up.

The reduced core passed Metals compilation and `hkmc2AllTests/test`; all
regenerated golden output accompanies the split.

### Previous Iterator and E27 integration

The latest merge incorporates structural Iterator (`015668cf4`) and E27
(`e62a8c172`). It adopts upstream's typed alias lookup for Iterator and Awaited.
Metals compilation and `hkmc2AllTests/test` passed; the full suite ran **1,294
tests**. The regenerated golden changes only update resolver line numbers in
the existing override diagnostics. The ten agreed fixmes below remain.

Against `e62a8c172`, the remaining Scala diff is:

| Category | Files | Additions | Deletions | Changed lines |
| --- | ---: | ---: | ---: | ---: |
| Compiler Scala | 24 | 1,082 | 250 | 1,332 |
| Scala tests | 2 | 42 | 8 | 50 |
| Total Scala | 26 | 1,124 | 258 | 1,382 |

This integration exposes no additional prerequisite for merging the reduced
feature. Further extraction would reduce review scope:

- E29–E30 still form a separate optimizer transformation: representation
  retyping and flow-proved cast removal. Their current hunks account for about
  **420 changed Scala lines across nine files**. Keep parameters, locals,
  captures, results and caller coercions together; any standalone extraction
  still needs adaptation and independent validation on `hkmc2`.
- E33–E34 add mutable-record declaration syntax, roughly **100–150 changed
  Scala lines** interleaved with E32. They could follow the core feature once
  its E32 read/write model is available. This is an estimate of the syntax
  feature's hunks, not a validated standalone patch.

E32 remains necessary for the retained precise mutable-field inference.
Removing only its assignment tracking or interface-write exposure would make
that inference unsound. The branch is independently validated with the agreed
known failures, but it still combines these themes with shape-based erasure.

### Previous reduction and independently validated follow-ups

The reduction removes the E20 partial-call optimization, E21–E23 constructor
and match fixes, E24 storage constraints, and E31 shadow-aware exposure. E32
still observes assigned values and external writes through contextual record
copies; its traversal conservatively exposes overwritten fields until E31 lands.
The original optional-binding test files and `Runtime.plus_impl` are restored,
deferring E35's consolidation and E36's cleanup.

Regressions for deferred compiler bugs retain their assertions. Targeted `:fixme`s identify the
deferred failures and name their E-number so the corresponding follow-up can
remove them. Passing cases retain their normal expectations. Iterator, E27,
mutable-write tracking, and the complete E29/E30 transformation stay together
with shape-based erasure.

The reduced branch passed `hkmc2AllTests/test` with **1,293 tests**. Its ten new
fixmes cover six constructor/match regressions in `T/slop/Erasure.mls` (E21–E23),
one nominal-storage regression in `T/deforest/erasedTypes.mls` (E24), and three
overwritten-field regressions in `T/slop/strictres/MutableFields.mls` (E31).
All affected failure cases retain their original `:expect` assertions. E20's regressions still pass with the
older, less aggressive optimization, and E35/E36 require no new fixmes.

Against `bae948bd5`, the Scala diff shrinks from 29 files with 1,347 additions
and 324 deletions to 26 files with 1,139 additions and 271 deletions: **261 fewer
changed Scala lines**, counting additions and removals. These counts include
the two retained Scala test files. The commit includes regenerated goldens and
the restored runtime helper's generated JavaScript.

The following branch names, counts and test results describe their independently
validated versions on the old base. After #575 merges, adapt the deferred fixes
to the retained inference code and regenerate goldens, including removing their
temporary `:fixme`s. E27 and Iterator have since landed upstream.

Every branch below starts directly at `hkmc2` / `hkust-taco/hkmc2` commit
`bae948bd5896748e7fde850785d9fdefd585c925`; none targets or depends on another
extraction branch. The Scala counts include comments and whitespace and count
additions and removals separately. MLscript regressions and regenerated golden
outputs are additional. All commits use the command-scoped Codex identity.

| Work | Local branch | Commit | Scala files | Scala + / − | Full-suite tests |
| --- | --- | --- | ---: | ---: | ---: |
| E20: partial-call argument evaluation | `codex/pr575-partial-call-arguments` | `4de7425e1` | 1 | 24 / 0 | 1,285 |
| E21–E23: constructor and match safety | `codex/pr575-constructor-safety` | `d0fae1ded` | 3 | 132 / 38 | 1,285 |
| E24: fusion across container storage | `codex/pr575-fusion-storage` | `c286e0c13` | 4 | 35 / 5 | 1,286 |
| E27: separate getter effects from values | `codex/pr575-effect-value-flows` | `8aabacb73` | 1 | 4 / 1 | 1,285 |
| E31: shadow-aware record exposure | `codex/pr575-record-exposure` | `fb52c50ff` | 1 | 20 / 6 | 1,285 |
| E35: optional-binding regression consolidation | `codex/pr575-optional-binding-tests` | `b848576fa` | 0 | 0 / 0 | 1,284 |
| E36: unused runtime helper removal | `codex/pr575-runtime-helper-cleanup` | `3ec7507bb` | 0 | 0 / 0 | 1,284 |
| Approved structural Iterator follow-up | `codex/pr575-structural-iterator` | `a374b7027` | 2 | 10 / 12 | 1,285 |

Each branch passed `hkmc2AllTests/test`; the Scala extractions also received
Metals compilation feedback. A temporary branch combining all eight extractions
passed **1,291 tests**. The Scala patches merged without conflicts. The only merge conflicts between
E21–E23 and E24 were in two existing golden files: `deforest/relaxedPrograms.mls`
and `deforest/todos.mls`. Regenerate those outputs when combining the branches,
since their diagnostic line numbers depend on both patches.

The constructor regressions fail on the base in four distinct ways: dropping
superclass effects, substituting the original argument after a constructor
changes its field, crashing on optional-field fusion, and selecting the wrong
match arm. The extraction passes all four. Its other cases retain tuple-match,
producer-specific default-branch layout, and pure-superclass elimination coverage.

The storage extraction keeps nominal fields compatible with their declared
representation while still allowing match closures in `Any` fields. Its Wasm
singleton regression fails on the base after unsafe fusion introduces a closure.
The stored-producer check classifies match consumers directly; constructor
eligibility remains in the fusion solver. This keeps E24 independent of the
constructor-safety helper and its changed `mergeDests` signature. Unmergeable
producers already root the exclusion graph, so their classification cannot
enable fusion.

E31 now has a standalone boundary: reverse traversal, contextual substitutions
and memoization, without enabling precise mutable reads. Three regression blocks
fail on the base because overwritten callbacks receive unknown external inputs.
Controls preserve exposure through unknown keys and surviving fields, and keep
distinct generic callback interfaces. Assigned values and externally permitted
writes remain together with E32.

E35 preserves the original raw-value and unsafe-call probes in addition to the
consolidated assertions for omitted and supplied values, lambdas, curried lists,
spreads, tail recursion, captured parameters, methods, and constructors. Its
duplicate optional-reset case is covered by the consolidated tail-call cases.
E36's public-helper removal was explicitly approved on 2026-11-07. Repository
search found no callers of `Runtime.plus_impl`; the distinct Wasm intrinsic
remains. The structural Iterator contract was explicitly approved earlier and
has landed upstream with its generator adaptation and protocol regressions.

The E27 counted-getter fixture already passes on the old base without E27; there
it checks compatibility, not an independently demonstrated bug. On the reduced
inference branch, removing E27 makes the same fixture fail with an effect
producer reaching E29's runtime-slot retyping. Restoring E27 makes it pass.
E27 prepares the flow-analysis invariant consumed by E29.

### Coupled work retained before the final split

| Retained work | Relationship to deferred fixes | Reason to keep it together |
| --- | --- | --- |
| E12: constructor-companion signatures | E21–E22 failures have targeted fixmes | Typed constructor results remove casts that previously hid unsafe constructor fusion. |
| E29: representation-changing deforestation | E27 is upstream; defer E21–E24 bugs with targeted fixmes | Parameters, locals, captures, results, instance copies and caller coercions must change together. |
| E30: flow-proved casts | Keep E29 | Removing representation-observing casts requires complete retyping of the fused value's uses. |
| E32: mutable-field resolution and exposure | E31's precision improvement can follow | All assignment paths, assigned-value exposure and structural input/output bounds must accompany precise reads. |
| E33–E34: mutable-record declarations | Keep E32 | Explicit bounds and per-field mutability need the complete read/write constraint model. |
| Shape-erasure feature | Retained in this PR | Observe all source-slot inputs before erasure and preserve physical representation boundaries. |

The six deferred branches can follow #575. When integrating them, preserve the
retained implementation in shared files and remove only the fixmes their fixes
resolve. The original independent validation does not replace validation on the
new base.

## Consolidated batches

**The table below groups the original themes; the revised scope above controls what lands in #575.** E01–E03 and B01–B05 are merged,
including E04's nofib aliases in the library/fixture batch. There is no
additional tiny nofib PR. The E-numbers remain stable references to individual
work items; B01–B10 group the broader themes. The ready branches above define
the review boundaries for this wave.

B01 is merged as #597 (extracted locally as `771a80b9f` on
`codex/pr575-fixture-corrections`). B02 is merged as #598 (extracted locally
as `aef07eead` on `codex/pr575-expression-results`). B03 is merged as #599
(extracted locally as `9afbadaf7` on `codex/pr575-async-generator-results`).
B04 is merged as #600. E08 and E14 were extracted separately from B05 as #601
and #602. E15 completed B05 as #606; E17–E18 completed B06's implementation as
#610. E19 is covered by #614. E27 is upstream; E20–E24 and E31 have independent
extraction commits listed above.
The prerequisite column records the original order for extracting all themes
before inference; it does not require postponing #575 for the deferred fixes.

| Batch | Review theme | Work items | Prerequisites | Scope |
| --- | --- | --- | --- | --- |
| B01 | Library and fixture corrections | E04–E07 | — | Remaining nofib character-list aliases, class-object references, open-method signatures and exported mutable-storage annotations. E36 now has a separate approved extraction. |
| B02 | Expression-result resolution | E09, E16 | — | Builtin result information and correct treatment of returns, abortive branches and loops. |
| B03 | Async and generator results | E10–E11 | — | Body payloads versus Promise/Iterator results, including cloning and currying. |
| B04 | Callable signatures through transformations | E13, E25–E26, E28 | — | Generated functions, cloned symbols, eta expansion, DPE and deforestation-generated callables. |
| B05 | Undefined values across runtime representations | E15 | E14 (merged) | Merged as #606 with representationless `Nothing` and Wasm placeholders. E08 and E14 are complete. |
| B06 | Optional and variadic arguments | E17–E18, E35 | B05 | Implementation merged as #610; E35's regression consolidation remains. |
| B07 | Optimizer safety | E12, E20–E24 | — | E19 is covered by #614. Type constructor companions; preserve checks and evaluation order; validate constructor effects, field mappings, branch selection and storage compatibility before elimination/fusion. |
| B08 | Representation-changing deforestation | E27, E29–E30 | B04, B05, B07 | Separate effects from values, retype every affected slot and function instance, and prove casts against all incoming producers. |
| B09 | Mutable-field resolution and exposure | E31–E32 | — | Shadowing, assignments, interface-permitted writes and structural read/write constraints. |
| B10 | Mutable-record declarations | E33–E34 | B09 | Explicit input/output bounds and per-field mutability, with documentation and regressions. |

B08 and B09 are likely the largest batches. Keep their coupled invariants
intact, but keep neighboring themes in their own batches. Check the actual
implementation diff before finalizing each extraction; these boundaries are
based on source inspection, not measurements of completed standalone patches.
An internal work-item dependency does not require another PR when both items
belong to the same batch. Do not introduce unused APIs or temporary incomplete
behavior merely to reproduce the original fine-grained sequence.

B01 was extracted from `66add69d3` and passed `hkmc2AllTests/test` with 1,155
tests. Its reviewed diff contains 16 files, 42 additions and 36 deletions,
including regenerated golden output. It changes MLscript fixtures and their
declarations without changing the Scala compiler.

Extraction exposed an E14 dependency in the open-method annotations in
T/newres/wasm/Super.mls and T/slop/wasm/OptionalParams.mls: annotating the base
method alone makes Wasm reject the unannotated override's result. Keep these
annotations and the paired T/newres/Overrides.mls changes with B05. Preserve
the unannotated overrides so the tests continue to exercise signature
inheritance; do not add annotations that hide the calling-convention bug.

B02 was extracted from `2ece680d5`. Its six Scala files contain 236 additions
and 18 deletions; the complete reviewed diff, including documentation and
regressions with regenerated goldens, is 23 files, 534 additions and 90 deletions.
Metals compilation, the focused suites, and `hkmc2AllTests/test` passed; the full
suite ran 1,157 tests. Builtin-call checks, exhaustive-loop results and explicitly
typed Wasm early returns were demonstrated to fail on the extraction base.
The existing narrowing-cast tests retain their purpose through `Num` operands
and a fractional SCC result. Shape-based symbol-slot erasure remains in #575.

B02 places the builtin-approximation paragraph under Standard Operators in
doc/reference.md. Its integration removes the duplicate from the residual
Runtime Representations section while retaining the other text.

B03 was extracted from `1ad11c54c`. Its seven Scala files contain 98 additions
and 27 deletions; the complete reviewed diff is 12 files, 282 additions and
39 deletions. Async/generator callable results expose Promise/Iterator while
body returns retain their declared payload. Completed payload metadata stays
with the defining unit and is renamed for cloned bodies. Generator wrappers
survive curried and generic callable interfaces; symbol-type inference remains
in #575.

Metals compilation, `ctest`, `cwtest`, the focused async/generator/cloning suites,
and `hkmc2AllTests/test` passed; the full suite ran 1,158 tests. The base rejected
an annotated async result at a Promise parameter and lost generators' `next`
interface. Regressions cover explicit/implicit returns, generator overrides,
curried and nominal interfaces, local nominal payload cloning, and an imported
pattern cloned in another unit. B03 annotates the extracted cloned payloads
and `counted` example so they work independently of inference; preserve the
original unannotated coverage when integrating it. The full-suite golden
changes outside those regressions are two existing diagnostic line numbers in
T/newres/Overrides.mls.

B04 replaces separate parameter/signature reconstruction with a plain shared
`FunDefn.Signature`, checked by the private constructor and explicit `copy`.
Binding copies refresh the symbol and parameters together; changes to the
calling convention prepare a new signature and symbol before rewriting calls.
Regressions cover simple and curried async capture wrappers, generators,
tail-recursive parameter refresh, DPE/eta specialization, nested and forward
calls, declared return representations, and optional parameters before a
variadic with trailing source parameters. Its full upstream suite passed
1,163 tests.

E12 moves from B04 to B07: typing constructor companions removes checked casts
that previously hid constructor applications from fusion, exposing unsafe
optional-field fusion without the optimizer-safety changes. Keep constructor
typing and those safety checks together. This integration preserves E12 and
the remaining B07/B08 implementation on the inference branch, and adapts its
retyped parameter bindings and specialized functions to shared signatures.

## What independently mergeable means

Every standalone batch targets `hkmc2`, includes its own tests and current golden
outputs, and must work on its target. Once #575 lands, later fixes can use its
retained implementation. Do not target another unmerged extraction branch.

A dash means no semantic prerequisite was identified by source inspection.
It is a standalone candidate, not a claim that the batch has already passed
tests. The remaining B07–B10 work has not been built in isolation. The complete original source
snapshot passed 1,165 tests, and E01–E03 and B01–B04 passed their own full suites,
but these results do not establish the correctness of the remaining
intermediate subsets.

Prefer explicit annotations in extracted regressions so that representation
fixes can be demonstrated before inference is enabled. Keep the original
unannotated variants for the final integration tests. Preserve a regression's
purpose when doing this: an annotation must not hide the very bug being tested.
If a proposed batch cannot pass independently without a workaround, reassess
its actual prerequisites or retain the inseparable logic in #575.

Paths below use these repository-relative roots:

- **S**: `hkmc2/shared/src/main/scala/hkmc2/`
- **T**: `hkmc2/shared/src/test/mlscript/`
- **C**: `hkmc2/shared/src/test/mlscript-compile/`
- **J**: `hkmc2/jvm/src/test/scala/hkmc2/`

The following sections retain the detailed work-item scopes and regression
checks. Their E-number dependencies describe implementation relationships;
the revised scope above controls which work remains in #575.

## 1. Source and diagnostic work items

E01–E03 are complete. E04–E07 belong to B01; E08 belongs to B05. None requires
new representation inference.

| ID | Work item | Implementation dependencies | Scope and regression checks |
| --- | --- | --- | --- |
| E01 | Fix binary-operator application nodes in the parser example | — | In C/apps/parsing/{Parser,Rules,Tree}.mls, wrap binary operands in `Tree.Tuple` when constructing and matching `Tree.App`. Keep the parser and printer agreement in one PR. Exercise multiplication and mixed-precedence expressions; regenerate T/apps/parsing/{ParserTest,LoopExpressions,ParserErrorTest}.mls outputs as applicable. Exclude the EOF error fix. |
| E02 | Construct a valid error tree for trailing parser input | — | Only the final unexpected-token branch in C/apps/parsing/Parser.mls: produce `Tree.Error(Tree.Sequence(tree), message) :: Nil`. Completed in #595. Review confirmed that current parsing consumes all tokens; the full suite passed without a golden change. Do not claim that existing parser-error tests exercise this defensive fallback. |
| E03 | Use a list accumulator in the fish benchmark | — | Replace `showl(xs, "")` by `showl(xs, Nil)` in C/nofib/fish.mls. Completed in #596 with additional empty/singleton/multiple-item formatter regressions in the existing nofib test. Both nonempty cases reproduced the invalid-tail failure before the fix. Preserve the separate main benchmark stack-overflow expectation. |
| E04 | Correct the Haskell string aliases in two nofib ports | — | Add `type String = List[Char]` in C/nofib/{lambda,lastpiece}.mls. These are two instances of the same porting error; keep them together. Compile and run both ports without changing the compiler or expected benchmark results merely to accommodate the aliases. |
| E05 | Pass class objects to reflection fixtures | — | Use `A.class` / `Pair.class` for `ConcreteClassSymbol` in T/block-staging/PrintCode.mls and T/newres/ShapeFixture.mls. Distinguish the constructor function from the class object. Check the existing generated-code and shape expectations. |
| E06 | Declare the public open-method contracts in library fixtures | — | The signature additions in C/Iter.mls, C/ObjectBuffer.mls, and `NonLocalReturn.ret` in C/Runtime.mls. Keep actual parameter/result choices visible for review; this is a library-contract change, not an inferred-type implementation. Compile these libraries and run their consumers, including handlers and object-buffer tests. |
| E07 | Declare the types of exported mutable storage in fixtures | — | The mutable-slot annotations in C/{Runtime,TreeTracer,ModuleReceiverCapture}.mls and C/apps/Accounting.mls. Retain intentional `Any` and nullable slots. Include matching declaration-only adjustments in existing tests when they document the same contract, but leave new exposure diagnostics in #575. Compile and run the affected library/application consumers. |
| E08 | Locate representation-conversion diagnostics at their source | — | S/codegen/Lowering.scala: the constructor-field name fallback and `castTo` value-location fallback. S/codegen/wasm/text/WatBuilder.scala: the `loc` argument and propagation in `castConserve`. Track the diagnostic-location hunks separately from the surrounding E14/E15 changes within B05. Use explicitly annotated failing field, argument, and return conversions to verify useful spans on JS and Wasm. |

For B01, compile and run the `lambda` and `lastpiece` nofib ports with the
corresponding `cntest` / `ndtest` selectors, alongside the affected fixture
consumers. The general prerequisites and full-suite gate below apply to every
completed batch.

## 2. Resolution and representation fixes that do not need inference

| ID | Work item | Implementation dependencies | Scope and regression checks |
| --- | --- | --- | --- |
| E09 | Give builtin applications consistent result information | — | S/semantics/BuiltinOperatorResults.scala, `NewResolver.builtinApplication` and its primitive-interface helpers, the Elaborator application hook, `ErasedType.builtinOperatorResult`, and the corresponding `Result.erasedType` case in Block.scala. Keep the resolver and IR rules together. Test arithmetic, comparisons, string concatenation, unknown operands, and operand-forwarding operators; retain the Wasm unknown-result rule. Use T/newres/CurriedFunctions.mls, the affected PartialApps tests, codegen/CheckedCasts.mls, and wasm/BuiltinOperators.mls. Review the documented Int-overflow approximation explicitly; this is the existing workaround, not a new overloading design. |
| E10 | Separate async body payloads from callable Promise results | — | Extract the async part of `Erasure.bodyResultType`, completed body-result storage in Elaborator.State, `copyBodyResultType` in Cloner, and the Lowering consumers. Callable signatures describe Promise; explicit and implicit returns are coerced to the annotated payload. Use existing async tests and the AsyncResult pattern in T/slop/ClonedBindings.mls, with annotated payloads where needed. Keep body-result state with the defining unit so imported/cloned bodies remain valid. Do not enable inferred results. |
| E11 | Model generator calls as iterators | E10 | Extend the preceding wrapper handling to generators: `TermDefinition.generatorAnnotation/resultWrapperAnnotation`, `WrappedResult`, Iterator lookup, and NewResolver's callable-result wrapping through all curried lists. Include the generator erasure branch in the same PR so resolution and IR agree. Remove the relevant fixme in T/newres/GeneratorResults.mls; extract the GeneratorResult cloned-pattern test and the generator override case from T/slop/Erasure.mls. Preserve the current treatment of combined async/generator annotations. |
| E12 | Preserve constructor-companion signatures through cloning | — | Initialize source ClassCtorSymbols from their class's physical parameter lists and nominal result in Erasure, using declared parameter types on this base. Include the deferred ClassCtorSymbol initialization, generated-constructor initialization in Lifter, and constructor erasure copying in Cloner/SymbolRefresher. All callers must obey write-once initialization, including legacy resolution. Test annotated private and auxiliary constructors, forward classes, and cloned constructors. Do not re-extract #592's already-merged ordinary-function cloning fix. |
| E13 | Give generated function definitions function signatures | — | `FunDefn.withFreshSymbol` in S/codegen/Block.scala: retain the parameter-list structure and parameter representations for generated callables, while getters remain value slots. Test lambdas assigned to annotated function slots without a redundant Function cast, including the relevant codegen/ErasedTypes and generated-function naming cases. Exclude unrelated changes to Block.scala. |
| E14 | Enforce override representations and their physical Wasm signatures | — | Merged as #602 with the source-layout and exposed-signature fixes. `OverrideChecks` and `OverrideLayout` validate argument correspondence before erasure inherits representations. Unannotated results inherit a specified base result unchanged. Wasm uses inherited physical parameter slots; ordinary returns retain their IR representation checks. Physical result context for undefined emission remains with E15. |
| E15 | Let undefined inhabit every runtime representation | E14 | Merged as #606. `Nothing` leaves representation joins unconstrained; the Cast smart constructor preserves bottom-typed paths. Wasm materializes placeholders at storage/call/result boundaries, including non-null nominal storage, while preserving effects and ordinary null checks. Keep the upstream implementation when integrating later inference and optimizer work. |
| E16 | Stop treating abortive splits and exhaustive loops as normal results | — | NewResolver.resultFlow's ordered split traversal, irrefutable patterns and loop continuation handling; Elaborator's guarded Unit publication; and Normalization's unreachable-continuation handling. Test an explicitly typed early return followed by an unrelated unreachable value, an exhaustive repeating/returning loop, and nested returns. Adapt the relevant T/newres/wasm/Erasure.mls blocks and T/codegen/ScopedBlocks.mls. Keep resolver and lowering changes together. |
| E17 | Coerce tuple-extracted arguments into their declared slots | — | Completed in #610. `bindFromTuple` coerces required and optional slots, preserving once-only evaluation and omission-as-null semantics. |
| E18 | Align typed arguments with optional and trailing parameter positions | E17 | Completed in #610 through shared `ArgumentLayout`, including under-applied calls. The integration keeps the additional source-branch override regressions. |

B03 keeps E10/E11 together: generator result shapes and the callable wrapper
signature must agree. E14 has landed independently. E15 supplies the physical
result context needed specifically for undefined emission; it must preserve
#602's checks on ordinary return values.

Useful existing suites: `dtest codegen/ErasedTypes`,
`dtest newres/GeneratorResults`, `sdtest ClonedBindings`,
`sdtest VariadicParams`, `wdtest VirtualMethods`, and the relevant
`newres/wasm/Erasure` blocks moved into dedicated slop regressions as necessary.
Do not move inference-dependent expectations into an earlier PR unchanged.

## 3. Optimizer improvements and correctness fixes

Several optimizer changes were exposed by more precise source types but also
apply to existing explicitly annotated programs. Extract the safety restrictions
before broadening the set of casts/constructors through which fusion operates.

| ID | Work item | Implementation dependencies | Scope and regression checks |
| --- | --- | --- | --- |
| E19 | Eliminate casts made redundant by propagation and inlining | — | Covered by #614's `RefinesCasts` and refined smart constructors. The original special cases in BlockSimplifier.applyPath/applyResult have been removed during integration. |
| E20 | Preserve checked argument evaluation when propagating partial calls | — | The unsaturated direct-member-call case in BlockSimplifier. Evaluate checked/effectful arguments at the original site and snapshot preceding arguments before later effects. Extract checkedPrefix/capturePrefix from T/opt/PureCallPropagation.mls and discardPartial from T/wasm/Casts.mls. Verify discarded partial applications still execute failing checks and later source-variable mutation does not change captured arguments. |
| E21 | Preserve constructor and superclass effects during elision | — | `ConstructorElision.isHarmless/harmlessClass`, its DCE use, and fusion's constructor/qualifier/argument-replay eligibility checks. Missing definitions, inheritance cycles, checks, calls and other unproved effects stay conservative. Extract CastEffect and EffectfulParent/Child tests from T/slop/Erasure.mls and exercise both DCE and fusion. Include the E22 field-position proofs in the same B07 batch. |
| E22 | Validate the parameter-to-field mapping before field fusion | E21 | `ConstructorElision.preservesParameterFields` and its use in fusion eligibility. A constructor can be harmless yet replace or reassign a field, so effect freedom alone is insufficient. Check the current IR layout, pre-constructor, parameter writes and actual field stores. Extract ChangedField and Captured/readCaptured from T/slop/Erasure.mls. |
| E23 | Preserve ordered match selection and producer-specific default layouts in fusion | E21, E22 | `DeforestFusionSolver.matches/selectedBranch`, its eligibility use, and the corresponding Rewrite branch selection and BranchId changes. Unknown earlier predicates must block choosing a later arm; inheritance and tuple/Object tests must agree with runtime matching. A shared default body must still have different field parameters for different constructor layouts. Extract the Parent/Child, arrayKind/objectKind, and A/B/Target default tests from T/slop/Erasure.mls. |
| E24 | Keep stored constructors unfused when their container cannot hold the replacement | — | `FlowWebComputation.impliedProducers`, DPE's empty callback, the unconsumed-constructor roots, and the field-storage constraints in Deforest.scala. Preserve an unfused nominal field's declared representation; do not store a replacement closure into it. Extract the two H/Box cases in T/deforest/erasedTypes.mls: nominal field stays unfused, Any field permits fusion. Verify propagation through nested containers. |
| E25 | Type generated deforestation callables and nullary closure temporaries | — | The erased signatures for branch/rest functions and the `deforest$lam` temporary's type in Rewrite.scala. Preserve the two physical parameter lists of branch functions and the captured-value list. On this base use the original slots' representations; E29 later substitutes retyped slots. Exercise an explicitly annotated nullary singleton match and inspect its generated signature/temporary. |
| E26 | Preserve the result slot when fusion replaces a return with a call | E25 | The scoped enclosing-return context and `returnCall` at fused matches and extracted rest calls in Rewrite.scala. Coerce the replacement call to the original annotated result. Test boxed reference/Int returns and nested extracted bodies. Carry T/slop/wasm/loose/DeforestPrimitiveReturn.mls as a known failing regression, not as a claimed fix: an unknown closure result still cannot represent an unboxed Int32 without further calling-signature work. |
| E27 | Keep flow-analysis effects separate from runtime values | — | The separate `unknownEffect` fallback and the distinction between effect and value strategy variables in FlowAnalysis.scala. Introduce each bookkeeping part with its consumer: E29 adds the runtime-slot collection, while this item fixes the fallback that currently mixes effects into primitive value flow. Exercise effect-analysis suites and the counted getter in T/slop/EffectValueFlows.mls, retaining effects and conservative eta behavior. No representation inference is needed. |
| E28 | Keep erased function signatures in sync with eta expansion and DPE | — | The function-signature part of PolyInstantiationRewrite's replacement-symbol machinery, `etaTargetLists/etaParamType`, and FlowAnalysisBasedRewrite's complete rewritten signatures. Use fresh symbols for changed write-once signatures, including in-place roots and copied functions; preserve optional/rest list structure. Add SymbolRefresher helpers only as used here. Extract the typed eta example from T/opt/EtaExpansion.mls, annotating g and f's results as necessary; retain DPE and mixed-target coverage. Leave value-slot retyping to E29. |
| E29 | Retype every slot and function instance affected by deforestation | E15, E21–E28 | The remaining `StratVar.instantiationId/symbolFlows` bookkeeping, value-symbol replacement in PolyInstantiationRewrite/SymbolRefresher, and Rewrite's producer-based parameter/result/local/capture typing, instance-copy selection and boundary coercions. Exercise mono/poly recursion, identity forwarding, nested instances, field projection, mixed fused/unfused sources, and effectful non-returning paths from T/deforest/erasedTypes.mls. This is one representation-changing transformation: do not land parameter retyping while leaving its locals, return slots, captures or callers stale. |
| E30 | Prove casts against all incoming producers before allowing fusion | E29 | `CastConsumer`, propagation/copying/solver invalidation, the required context plumbing, and removal of casts whose operand representation actually changes through fusion. Keep narrowing casts needed for physical Wasm slots when fusion does not change the operand. Extract makeOpaqueBox/mixedBox and mixed-source cases in T/deforest/erasedTypes.mls plus T/slop/wasm/loose/FlowCastProofs.mls. A single unknown or incompatible producer must invalidate the proof, including across copied/recursive schemes. |

B08 is one of the largest batches. Splitting E29's implementation
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

| ID | Work item | Implementation dependencies | Scope and regression checks |
| --- | --- | --- | --- |
| E31 | Follow only surviving record fields during interface exposure | — | The reverse, shadow-aware traversal and contextual memoization in InterfaceExposure's record case, including initializer exposure. Preserve unknown-key conservatism and nested spread contexts. Re-express overwrittenSource, direct/spread replacement, and computed-key cases from T/slop/strictres/MutableFields.mls using escaping callbacks, so they test resolution/exposure without the later missing-field-annotation diagnostic. E31 is now extracted independently while mutable reads remain conservative; add assignment-flow handling with E32. |
| E32 | Account for every write when resolving and exposing mutable fields | E31 | NewResolver's `assignField/writeField/listenAssignedValues/assignableTargets`, projected lookup, class/record read paths, Elaborator's assignment hook, owned caches, and InterfaceExposure's unknown writes and assigned-value traversal. Include the structural input/output representation and constraints: RecordTypeShape/MemberLookup.Typed carry TypeArgument pairs through identity, substitution, support, transport, intersections and reads; `declaredField`, `constrainRecord` and `listenFieldInput` propagate writes negatively and reads positively. Exercise classes and existing `mut {f: T}` syntax, including existing interval type arguments, before introducing per-field syntax. Test projections, all receiver forms, multiple classes, escaping callbacks, late assignments, nested spreads, immutable-copy controls and both structural constraint directions. Adapt TypeRelationTest while preserving its bounded-growth property. Exclude erasure observations and the requirement to annotate exposed fields. |
| E33 | Support explicit input/output bounds on mutable record fields | E32 | The typeArgument elaboration helper, direct field-bound syntax, missing-output provenance, and immutable-field rejection. Test `mut {f: in S out T}`, parenthesized bounds, input-only/output-only fields, nested negative positions, aliases and recursive interfaces. Use the relevant MutableFieldVariance blocks with both whole-record and per-field mutability alongside E34 in B10. Do not claim complete structural subtype checking or add it in this extraction. |
| E34 | Allow individual record fields to be declared mutable | E32, E33 | The `RcdField.mut` metadata, value/type elaboration, pretty-printing, cloning, RecordShape lookup, exposure and structural-interface flag threading, and Lowering's `allocatesMutable`. Support `{mut f: value, label: other}` end to end, including its type form and spread copies. Extract the mixed-field and copied-record tests from MutableFields, the MutableRecord pattern from ClonedBindings, and the BadMut expectation change. Move the corresponding reference documentation here. Keep source erasure deferral for record slots in #575. |

E32 keeps direct assignments and writes admitted by declared interfaces together.
Separating them would let a newly precise read ignore a write through a
structural interface. The input/output representation is therefore used by its
actual readers and writers in B09, alongside E31's exposure traversal. Keep
this batch separate from B10's declaration extensions and from B08's optimizer
transformations.

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
  B10 lands.

B10 is a language-feature review covering E33/E34. It preserves the syntax and
behavior already proposed by #575; extraction does not authorize inventing
further syntax, changing dispatch, or extending the public library API.

Use `dtest newres/Records`, the appropriate split blocks from
`sdtest strictres/MutableFields` and `sdtest strictres/MutableFieldVariance`,
and the existing TypeRelationTest for bounded recursive intersections. New
files belong under T/slop/. Keep any genuine remaining resolution limitations
as fixmes rather than weakening their expectations.

## 5. Test consolidation and one optional cleanup

| ID | Work item | Implementation dependencies | Scope and regression checks |
| --- | --- | --- | --- |
| E35 | Consolidate optional-binding regressions without losing coverage | E15, E17, E18 | Reconcile T/slop/OptionalBinding.mls and T/slop/strictres/OptionalNull.mls into T/slop/strictres/OptionalBinding.mls, along with the duplicated tail-recursive case removed from strictres/OptionalParams.mls. Audit cases one by one: omission, supplied null/undefined, lambdas, currying, spreads, tail recursion, closures, constructor elimination and dynamic construction. E17/E18 are already merged; the standalone consolidation is validated above. Do not copy current golden output into an older compiler or treat unsafe.undefined observations as new semantics. |
| E36 (approved) | Remove the unused Runtime Int31 addition prototype | — | The deletion of `Runtime.plus_impl` at the end of C/Runtime.mls and its generated output. No callers were found on the extraction base, and removal was explicitly approved on 2026-11-07. The `wasm.plus_impl` intrinsic is a different symbol and remains. |

E35 originally belonged to B06, whose implementation has since merged; its audited
consolidation now has an independent branch. E36 was initially deferred pending
approval; the user approved removal on 2026-11-07 and its independent branch is
now validated. Neither item is a prerequisite for compiler implementation work.

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
- changed override parameter layouts are now checked by #602's shared source
  correspondence rules; keep those checks when integrating inferred representations.

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
   behavior. For each selected batch, create a branch such as
   `codex/pr575-fixture-corrections` from current `hkmc2`, after its
   prerequisites have merged.
2. Extract the complete implementation, documentation and regressions for that
   theme. Check the implementation size separately from test/golden volume,
   and use the shared-file map. The historical commits are research aids, not
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
5. For extractions that land before #575, merge the actual new `hkmc2` commit
   into this branch and preserve both the fix and remaining inference logic.
   The explicitly deferred fixes follow the reduced #575; adapt their shared
   files and remove the corresponding temporary fixmes when they land.
6. Recompute `git diff hkust-taco/hkmc2...HEAD`, record the merged PR link/status
   in this plan, and inspect what remains. Validate any retained code/test
   changes from synchronization, including new upstream regressions. The
   extraction is fully integrated only when its independent behavior is
   upstream and its corresponding diff has disappeared here.

GitHub may squash the extracted PRs. Merge the real upstream commits back;
their original extraction commit IDs are not a substitute for that ancestry.
The earlier #592 reconciliation used an unchanged-tree merge only after exact
tree equality was established. Do not apply that strategy blindly to future
extractions, whose patches may have been adapted to a smaller base.

The upstream synchronization target is `4967bcd7d8c525e310c3dfcccd7da0ba88fb8bbd`,
including E17–E18 (#610), the cast refactor (#614), retained MIR definition symbols,
JDK 25, Wasm file imports (#576), structural Iterator, E27, E31, E35 and E36. Measure each
proposed extraction against this updated target before starting it.

The previous integration kept the upstream override checker, source layouts and unchanged
inherited result representations while retaining shape-based inference. Override
checks use declarations in the current program; imported observations may supply
already-erased definitions but must not replay earlier worksheet diagnostics.
Undefined returns use the physical Wasm result slot, while ordinary returns keep
the upstream representation checks. The updated collection annotations also require
`Iterator[T]` to describe the structural `next` protocol: this approved interface
change uses the same alias for generator results and library implementations.
That integration passed `hkmc2AllTests/test` with 1,200 tests.

The integration through `a95f0e1ba0` adopted upstream's `Nothing` coercion rules, non-null Wasm
placeholders and backend-owned calling conventions. The remaining optimizer's
`coerceToOr` callback now accepts the `Path` returned by the Cast smart constructor.
The new nullable-record graph-growth test retains its assertions while using this
branch's separate field input/output types. The optional-argument forwarding fixture
now declares its heterogeneous input as `Any`, so later worksheet calls can supply
Unit after the initial integer call. `hkmc2AllTests/test` passed all 1,210 tests
with an 8 GB SBT heap.

The pre-reduction integration adopted the shared argument layout and both cast forms while
retaining flow-based cast proofs and representation-changing deforestation. Calls
whose definitions keep their symbols use saved original signatures and planned
result representations during rewriting. Erasure visits pattern-local aliases as
well as exported bindings, including unused transform inputs. New upstream
optional-binding regressions join the consolidated strict-resolution file. The
Wasm session-field regression now passes with transitive type imports, and i64
expectations use the runner's BigInt rendering.
Metals compilation and `hkmc2AllTests/test` passed; the full suite ran 1,294 tests
with an 8 GB SBT heap. All resulting golden-output changes accompany the merge.

The independent local branches and measured Scala counts are listed above.
E20 and the other ready work have now been extracted and validated on `bae948bd5`.

The current order is to review the reduced #575 with E12 and E32 retained,
then land E29–E30 and E33–E34 separately. E20–E24 also have independent PRs;
adapt their temporary-failure markers if they land after #575. E31, E35 and E36
are already upstream. Regenerate shared golden outputs when combining the
follow-ups.

## 9. Validation and review gates

For every completed code/test batch:

- Use Metals for quick Scala inspection and compilation feedback.
- Keep a persistent SBT shell. Before individual diff tests, run `ctest`;
  before Wasm diff tests also run `cwtest`. Run the relevant `catest` or
  `cntest` before application/nofib consumers.
- Use `dtest` for the main suite, `sdtest` for slop, `wdtest` for the Wasm
  suite, and `adtest` / `ndtest` for the corresponding application/nofib tests.
  Main-suite newres/wasm tests still use `dtest`.
- Finish with `hkmc2AllTests/test` on the complete batch. A focused pass or
  Metals compile is not a substitute. Commit the latest generated .mls/.mjs
  output with the owning PR; do not create a separate golden-update PR.
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

Validation of an integrated inference branch does not establish that the
remaining consolidated batches work independently on their extraction bases.
