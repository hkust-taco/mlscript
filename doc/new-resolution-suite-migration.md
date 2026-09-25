# New-resolution suite migration

## Scope and status

This is the worklist for migrating existing worksheets and compilation fixtures
to new resolution. Language rules live in the [language reference](reference.md#resolution-interfaces);
resolver invariants and regression coverage live in the
[resolver design notes](new-resolution-design.md). Backend-specific constraints
are in [WASM resolution](new-resolution-wasm.md).

The checked-in worksheet headers give the following status. Counts exclude shared
`.mls` configurations, new-resolution regression tests, and the 51 files under
`ucs/staging`, which the test runner excludes.

| Suite | Migrated | Legacy configuration | Active files |
| --- | ---: | ---: | ---: |
| basics | 61 | 29 | 90 |
| codegen | 86 | 39 | 125 |
| ucs | 52 | 18 | 70 |
| ups | 49 | 22 | 71 |
| apps | 13 | 3 | 16 |
| Total | 261 | 111 | 372 |
| wasm (separate backend) | 19 | 2 | 21 |

All twelve `apps/parsing` worksheets use new resolution, but some implementation
modules they import still use legacy resolution. Worksheet migration does not
imply that its dependencies have been migrated.

| Compilation suite | New resolution | Legacy resolution | Total |
| --- | ---: | ---: | ---: |
| Main (including quotes, UPS, and regression/compatibility fixtures) | 26 | 23 | 49 |
| Applications | 6 | 14 | 20 |
| Nofib | 12 | 27 | 39 |
| WASM | 0 | 1 | 1 |
| Total | 44 | 65 | 109 |

These totals include the new-resolution `NamedFieldLibrary` regression fixture
and the temporary legacy `LegacyOption` compatibility fixture.

## Migration procedure

- Start migrated worksheets with `:.` before any blank line. Suite `.mls` files
  inherit the common `#lang(0.3.x)` configuration through `:..`, including in
  nested directories. The general suites use non-strict resolution; `newres`
  enables strict resolution and `newres/loose` explicitly overrides it.
- Preserve each worksheet's execution flags. The common language configuration
  disables JS execution; a parser-only test must not acquire runtime execution
  merely because its resolution configuration changes. WASM has its own flags.
- Add `#lang(0.3.x)` to compilation fixtures only after checking both standalone
  compilation and existing consumers. Real files check their exposed interfaces
  even in non-strict mode. Add the callable, nominal, or structural interfaces
  their public APIs require. Making a helper private changes the exported API;
  using `dyn` to bypass a missing interface changes the language contract.
- Preserve successful results and negative-test intent. Existing invalid
  operations may need compilation-error expectations in addition to runtime-error
  expectations. Do not remove an expectation without resolving the intended
  behavior, or rewrite a callable-constructor test to avoid the feature it tests.
- Keep blocked files on their existing configuration with their source and
  goldens intact. Do not add per-file `:todo`, `:fixme`, `:ignore`, or resolution
  exceptions to claim a port. Use focused regressions for unresolved compiler bugs.

## Remaining work

### Mixed-mode imports and fixture interfaces

`Option` uses new resolution, but legacy consumers such as `apps/parsing/Parser`
inspect imported return annotations through `Resolver.resolveType`/`resolveSign`.
This queries legacy symbols on new-resolution syntax. The affected dependency
graph imports `LegacyOption` temporarily; consumers exchanging `Some`/`None`
values, including reflection and `Block`, must share the same constructor identities.
Port these consumers together and delete `LegacyOption`, restoring `Option` imports.
The same signature boundary blocks independent ports of `Token` and `Keywords`.
A general interoperability bridge must consume completed type information without
re-resolving imported nodes or querying erased types before erasure.

Many fixtures also need source interfaces: for example, `QuoteExample.bind` calls
an unannotated callback, and Nofib helpers expose comparators and printers.
The inventory below separates these from compiler and prelude gaps.

### Shape propagation and capture precision

- **Generators:** `newres/GeneratorResults.mls` records a call whose result is
  treated as the generator body's return value, leaving `.next` unresolved.
  Model the iterator result produced by lowering; use `codegen/Generators` as
  the worksheet acceptance case.
- **Mutation and control flow:** mutable-array reads use the element shapes
  collected from the initializer and subsequent writes, as described in the
  [resolver notes](new-resolution-design.md). Tracking individual positions and
  lengths is out of scope. Complete the
  [type-argument constraint design](new-resolution-type-value-flow.md), including
  authoritative instantiation at explicit type applications and by-name invocations,
  specialized inferred results observed before term application, supplied member-input
  constraints, reconstructed receiver contexts, inferred missing member types,
  and the whole graph's termination bound. Concrete outstanding cases are in
  `newres/InstantiationSites.mls`, `StoredSpecializations.mls`, `ConstructorInstances.mls`,
  `InferenceHoles.mls`, `PartialSignatures.mls`, and `TypeGraphTermination.mls`.
  Decide how reassignment affects mutable storage's inferred interface, including
  across compiled worksheet blocks. `newres/MutationFlow.mls` records a reassigned
  array still checked against its initializer's tuple length; accumulating both
  shapes would still reject valid later indexing. `codegen/SetStmt` also lacks
  argument flow through its update callback. Member-variable definitions still
  need work. Handler inference needs separate flows for the receiver, values
  passed to resumptions, and abortive results (`newres/HandlerResults.mls` and
  `codegen/ScopedBlocksAndHandlers`). Agree these designs before implementation.
- **Captured activations:** preserve activation identity through captured
  functions, constructor aliases, reconstruction of the same class, and partial
  construction. Existing regressions include `CtxSens`, `ValCtxSens`,
  `Projections`, `RecursiveEnvironment`, `SpreadCalls`, and `InterfaceExposure`
  under `newres`. Do not turn unknown shapes into dynamic values or truncate
  capture paths to make these cases pass.
- **Exposed nominal results:** `newres/InterfaceExposure.mls` records a returned
  private class whose callable methods are not checked through its nominal result
  annotation. Follow declared member interfaces back to their implementations
  without exposing initializer shapes hidden by annotations.
- **Cross-block flow:** remaining cases include parameter flow in
  `basics/MiscArrayTests`, unfinished closures in `codegen/FirstClassFunctionTransform`,
  and the unresolved receiver in `codegen/ObjectMethodDebinding`. Coordinate
  cross-block method changes with the separate implementation work before porting.

### Patterns and generated references

Complete record, conjunction/negation, string concatenation, guarded and
transforming pattern flow, and pattern values such as `.unapply`. Representative
worksheets are `ucs/general/BooleanPatterns`, `ucs/patterns/RecordPattern`,
`ucs/patterns/String`, `ups/RecursiveTransformations`, and `ups/examples/HindleyMilner`.
`Char.AnyChar` also loses its string interface before its `length` guard.

`ucs/examples/EitherOrBoth` and the imported parser implementation expose
synthetic selections entering new resolution. Generated matcher code should retain
the source reference's completed target and receiver path through the `Lowering`
capability, without re-running lookup or cloning listener hosts with no candidates.
Transfer rules must distinguish matched inputs, bound fields, and transformed
outputs. Union alternatives, filter conjunctions successively, and avoid inventing
positive bindings for negation. Recursive patterns need cycle-aware subscriptions
and demonstrated convergence.

Acceptance coverage should include tuple/record extraction, nested and imported
constructors, aliases, guards, transformed results, repeated references, and
recursive UPS matchers. Preserve both runtime results and matcher structure.

### Calls, declarations, and diagnostics

- Implement automatic contextual argument insertion for `Lexer` calls to
  `Token.integer`, `symbol`, and related APIs with trailing `using` lists.
  Resolve the opened binary `~`/builtin-operator conflict without removing those APIs.
- Complete type-argument validation (`basics/GenericClasses`), constructor-value
  member lookup (`codegen/ParamClasses`, `basics/DynamicInstantiation`), and
  module/call checks. Decide nominal module-forwarding compatibility for
  `basics/CyclicModuleForwarders` before changing its expected outcomes.
- Extend host interfaces where needed: `Array.reduce` accumulator/callback
  contracts, keyword-named `Map.set` and `Reflect.set`, and WebAssembly exports.
  `Array.concat` currently returns `Array[Any]`; improving precision needs a
  declared element constraint on its rest arguments. `Array.splice` must separate
  its optional deletion count from inserted elements before those elements can
  constrain `T`; `newres/MutableArrays.mls` records the gap.
- Complete quasiquote type-selection and wildcard-reference lowering (`CSP`,
  `QuoteExample1`).
- Preserve source origins in synthesized references and diagnostics. In particular,
  check the lost undefined-binding use sites in `ups/UpsBugsBacklog` and
  `ups/syntax/MixedParameters` without changing the selected symbol.

Retry remaining legacy worksheets against the current compiler and prelude before
treating a previously observed diagnostic as an implementation gap.

## Deferred compilation fixtures

Paths are relative to `hkmc2/shared/src/test/mlscript-compile/`. These are the
last recorded obstructions, not a fresh failure audit or an exhaustive diagnosis.
Retry each fixture before implementing a fix: subsequent compiler and prelude
changes may have removed its first blocker. Deferred fixtures retain legacy
resolution; imports that exchange options must use `LegacyOption` consistently.

| Main fixture | Observed obstruction |
| --- | --- |
| `Benchmark.mls` | Exposed `suite.run` and callback interfaces. |
| `Block.mls` | `Str.replaceAll`, `Any.toString`, and pattern-value interfaces. |
| `CSP.mls` | Quasiquote type selections and wildcard opens. |
| `CachedHash.mls` | Retry candidate: implicit Object inheritance supplies the required `this.toString` interface. |
| `Char.mls` | `AnyChar` loses the string shape before its `length` guard. |
| `FingerTreeList.mls` | `Array.reduce` and numeric projection on an array rather than a fixed tuple. |
| `Iter.mls` | Exposed callbacks and iterator `next` interfaces. |
| `LazyArray.mls` | `null.next` and missing pattern-field shapes through mutation. |
| `LazyFingerTree.mls` | Exposed `xs.length` and pattern-field interfaces. |
| `MutMap.mls` | Exposed `m.underlying` and keyword-named `Map.set`. |
| `ObjectBuffer.mls` | Exposed `cls.size` and constructor interfaces. |
| `LegacyOption.mls` | Temporary copy for legacy consumers; delete when those consumers are ported. |
| `Predef.mls` | Exposed generic callbacks and rest-argument `.call`. |
| `QuoteExample.mls` | Exposed callback `k` in `bind`. |
| `QuoteExample1.mls` | Quasiquote wildcard-open references. |
| `Rendering.mls` | Nullable string flow, callbacks, and pattern-field interfaces. |
| `Runtime.mls` | `Map.set` and nullable `contTrace` flow. |
| `Shape.mls` | Pattern-derived receivers for `join`, `every`, `length`, and `name`. |
| `Stack.mls` | Exposed `arr.length` and predicate callbacks. |
| `Term.mls` | `Map.set` and generic pattern/value interfaces. |
| `TreeTracer.mls` | Exposed `message.split` and pattern-reference forms. |
| `XML.mls` | Exposed `value.toValue`. |
| `ups/EvaluationContext.mls` | Exposed `target.freeVars` and context interfaces. |

| Application fixture | Observed obstruction |
| --- | --- |
| `apps/Accounting.mls` | Array callback arity, `reduce`, and receiver interfaces. |
| `apps/CSV.mls` | Retry with the mutable-array element flow; regexp/nullish result interfaces and `at` results still need checking. |
| `apps/parsing/Extension.mls` | Receivers for `display`, `add`, and `extendChoices` have no resolved target. |
| `apps/parsing/Keywords.mls` | Legacy `Parser` consumers cannot inspect its new-resolution signatures. |
| `apps/parsing/Lexer.mls` | Missing automatic contextual argument insertion and opened binary `~` resolution. |
| `apps/parsing/ParseRule.mls` | Flow through private module/class `let` bindings and imported mutable maps. |
| `apps/parsing/ParseRuleVisualizer.mls` | Imported JS railroad API lacks member interfaces. |
| `apps/parsing/Parser.mls` | Synthetic selections from imported legacy forms reach new resolution. |
| `apps/parsing/Rules.mls` | An `extendChoices` receiver has no resolved target through mutable map lookup. |
| `apps/parsing/Test.mls` | `flags.has` and `tracer.reset` lose shapes through tuple/import flow. |
| `apps/parsing/Token.mls` | Legacy contextual-argument consumers cannot read its new-resolution signatures. |
| `apps/parsing/Tree.mls` | Chained `JSON.stringify(...).slice(...)` lacks a result interface; also coupled to legacy consumers. |
| `apps/parsing/TreeHelpers.mls` | Coupled to `Tree` and its consumers. |
| `apps/parsing-web-demo/main.mls` | String callback interfaces, dynamic receiver flow through aliases/mutation, and tuple-bound `example.name`. |

| Nofib fixture (under `nofib/`) | Observed obstruction |
| --- | --- |
| `NofibPrelude.mls`, `ansi.mls`, `atom.mls`, `awards.mls`, `constraints.mls`, `cse.mls`, `fish.mls`, `integer.mls`, `lambda.mls`, `lastpiece.mls`, `life.mls`, `mate.mls`, `minimax.mls`, `para.mls`, `power.mls`, `pretty.mls`, `primetest.mls`, `scc.mls`, `secretary.mls` | Exposed callback parameters need callable interfaces. |
| `eliza.mls`, `knights.mls`, `sorting.mls` | Unannotated string receivers and callbacks. |
| `circsim.mls` | Exposed record receivers such as `p.pid` and `p.compType`. |
| `cryptarithm2.mls` | Callable interface for an unannotated constructor field. |
| `cichelli.mls` | Callback interfaces. |
| `treejoin.mls` | Pattern flow. |
| `lcss.mls` | Function result has no interface for `toString`. |

The remaining WASM fixture, `wasm/Wasm.mls`, needs interfaces for
`WebAssembly.Instance.exports` and its exposed `wasmInst.imports` receiver.

## Validation and completion gates

Follow the [repository test workflow](../README.md#running-the-tests-1):

1. Rebuild compilation fixtures before running their worksheet consumers: `ctest`
   for main fixtures, `catest` for applications, `cntest` for Nofib, and `cwtest`
   for WASM. In particular, runtime tests need the generated `.mjs` dependencies.
2. Run affected consumers, including negative cases, and review golden changes.
   Keep nonmigrated files intact; do not retain trial-generated failures.
3. Run `hkmc2AllTests/test` for each retained batch. Commit intentional golden
   updates together with the change, using the agent's identity for agent commits.
4. Remove legacy suite configurations only after all covered files migrate,
   without new failure suppressions or lost negative diagnostics. Remove
   `LegacyOption` once its consumers use the new interfaces consistently.

Update the counts and blocker inventory after each retained batch. Test totals
include configurations and regression tests, so they are not migration counts.
