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
Check each fixture's public API and its consumers when porting it; the source
headers identify the remaining legacy fixtures.

### Shape propagation and capture precision

- **Generators:** `newres/GeneratorResults.mls` records a call whose result is
  treated as the generator body's return value, leaving `.next` unresolved.
  Model the iterator result produced by lowering; use `codegen/Generators` as
  the worksheet acceptance case.
- **Mutation and control flow:** mutable arrays propagate initializer and write
  shapes through their element parameter. Position and length tracking is out of
  scope. [Type-flow design improvements](new-resolution-future-work.md) are deferred:
  receiver reconstruction, inferred missing member types through nominal views,
  omitted-argument caller separation, and a more precise regularity check. These
  do not block the current implementation batch. The whole-graph convergence audit
  remains open; local allocation and replay bounds are documented in the
  [type-flow reference](new-resolution-type-value-flow.md#canonical-references-and-termination-obligations).
  For broader mutation migration, decide how reassignment changes storage's
  inferred interface, including across worksheet blocks. `newres/MutationFlow.mls`
  records a reassigned array checked against its initializer's tuple length;
  accumulating both shapes would still reject valid later indexing.
  `codegen/SetStmt` needs argument flow through its update callback. Member-variable
  definitions also need work. Handler inference needs separate flows for the
  receiver, values passed to resumptions, and abortive results
  (`newres/HandlerResults.mls` and `codegen/ScopedBlocksAndHandlers`). Review these
  designs before implementation.
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

Retry legacy worksheets and compilation fixtures against the current compiler and
prelude before diagnosing a blocker. Keep deferred fixtures on legacy resolution;
imports exchanging options must use `LegacyOption` consistently. The WASM fixture
`wasm/Wasm.mls` needs interfaces for `WebAssembly.Instance.exports` and its exposed
`wasmInst.imports` receiver.

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

Update the counts and remaining work after each retained batch. Test totals
include configurations and regression tests, so they are not migration counts.
