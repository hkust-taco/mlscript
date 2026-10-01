NOTE: This document was written by Codex Astra and has not been deeply reviewed;
it is not meant to be official documentation and
is in fact likely to contain parts that are unintelligible to readers who lack sufficient context.


# New-resolution suite migration

## Scope and status

This is the worklist for migrating existing worksheets and compilation fixtures
to new resolution. Language rules live in the [language reference](reference.md#resolution-interfaces);
resolver invariants and regression coverage live in the
[resolver design notes](new-resolution-design.md). Backend-specific constraints
are in [WASM resolution](new-resolution-wasm.md).

The checked-in worksheet headers give the following status as of 2026-10-01.
Counts exclude shared `.mls` configurations, new-resolution regression tests, and the 51 files under
`ucs/staging`, which the test runner excludes.

| Suite | Migrated | Legacy configuration | Active files |
| --- | ---: | ---: | ---: |
| basics | 67 | 23 | 90 |
| codegen | 93 | 33 | 126 |
| ucs | 69 | 1 | 70 |
| ups | 58 | 13 | 71 |
| apps | 15 | 1 | 16 |
| Total | 302 | 71 | 373 |
| wasm (separate backend) | 22 | 1 | 23 |

All twelve `apps/parsing` worksheets use new resolution, but some implementation
modules they import still use legacy resolution. Worksheet migration does not
imply that its dependencies have been migrated.

| Compilation suite | New resolution | Legacy resolution | Total |
| --- | ---: | ---: | ---: |
| Main (including quotes, UPS, and regression fixtures) | 42 | 7 | 49 |
| Applications | 17 | 3 | 20 |
| Nofib | 37 | 2 | 39 |
| WASM | 1 | 0 | 1 |
| Total | 97 | 12 | 109 |

These totals include the new-resolution `NamedFieldLibrary` regression fixture
and the deliberately legacy `LegacyGenericLibrary` mixed-mode regression fixture.
They count language directives in source files, not test-runner test cases.

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
  Review successful values and logs as well as failure markers: unsupported
  contextual calls can return function values without failing the test runner.
- Open operators explicitly when overriding builtins, as in `codegen/ImportedOps`
  and `ucs/examples/ListFold`.
- Use dynamic selection for reflective host access whose effects are not described
  by the static interface. For example, `ups/examples/DoubleTripleList` uses
  `testList!head` to observe an installed JavaScript getter; reads through the
  declared `val` interface are pure and may be discarded when unused.
  `newres/GetterReadEffects.mls` covers getters, dynamic reads, and field interfaces.
- Keep blocked files on their existing configuration with their source and
  goldens intact. Do not add per-file `:todo`, `:fixme`, `:ignore`, or resolution
  exceptions to claim a port. Use focused regressions for unresolved compiler bugs.

## Remaining work

### Mixed-mode imports and fixture interfaces

Some migrated worksheets import legacy compilation fixtures. An import across
resolution modes is supported and is not itself a migration blocker. Check each
fixture's exposed interfaces and its consumers together. Routine annotations and
source corrections should be attempted before attributing a failure to the
resolver. The remaining fixtures need the following work:

| Legacy fixtures | Concrete work and known failures |
| --- | --- |
| `LazyFingerTree` | Supply indexable interfaces and check its consumers. Imported generic method results are covered by the passing `newres/LegacyGenericMethods.mls`, including `FingerTreeList.mk(42).at(0)`. |
| `FingerTreeList` | Enabling new resolution exceeds the compilation test's time limit. Diagnose inference growth around recursive trees and tuple spreads before calling this an annotation-only port. |
| `Runtime`, `Rendering` | Audit callable and host interfaces. No separate design blocker is established for their missing annotations. |
| `CSP`, `QuoteExample1` | Quasiquote type selections and wildcard-reference lowering. |
| `parsing/Lexer` | Calls to token constructors with trailing `using` parameters need automatic contextual argument insertion; `newres/LexerMigration.mls` records the missing behavior. |
| `parsing/ParseRule` | Correct `andThen`'s helper signature: it transforms a rule's result into a pair with the following rule's result, rather than preserving `B`. Recheck migration with lexical type captures preserved in legacy signatures. |
| `parsing/Extension` | Give rules their `ParseRule[Tree]` interfaces and validate calls to `ParseRule.andThen` together with that dependency's migration. |
| `nofib/lastpiece`, `nofib/sorting` | Both exceed the compilation time limit under new resolution. `sorting` first needs `int_of_char(c: Str)`; adding it reveals the timeout. Diagnose inference growth before retrying these ports. |

Array callbacks must accept the arguments supplied by the JS API: three for
`map`/`filter`/`forEach` and four for `reduce`. Use `pass1(f)` or `pass2(f)` when
adapting a function that uses fewer arguments. An unused rest parameter also satisfies
this existing rule (`newres/Arrays.mls`); it does not require relaxing callback
arity checking. Missing host declarations and ordinary parameter annotations do
not require a language-design discussion. Compiler assertions and timeouts need
reproductions and fixes; a design question should name the unresolved semantic
choice, rather than merely name the failing subsystem.

To reproduce a blocker, temporarily add the language directive to the named
compilation fixture and run `ctest <name>` or `catest <name>` as appropriate.
The blocked fixtures retain their existing resolution mode.

`Predef`, `Block`, `Shape`, `LazyArray`, `Accounting`, `CSV`, `Parser`,
`ParseRuleVisualizer`, and the parser web demo use new resolution. Nullable host
results use pattern matching where possible; mutable traversal arrays use `mut`.
Parser map interfaces carry their element types through `Option`, so ordinary
`Some(rule)` bindings retain the rule interface. Member `let` bindings contribute
their initializer and assignment shapes, including in the web demo.
The parser unwraps optional continuation rules and resumes module parsing after
leading separators. The virtual `source` fields expand in both resolution modes
(`newres/SourceLocations`); constructor metadata is covered by `newres/ShapeFixture`.

The web demo compiles, but serving its checked-in HTML directly still encounters
Node-only imports (`fs`, `process`, `path`, and `url`) through `Predef` and `Term`.
Browser packaging must separate that dependency before direct startup works.
Parser and visualizer worksheets run under Node and do not exercise this browser
packaging constraint.

### Shape propagation and capture precision

- **Generators:** `newres/GeneratorResults.mls` records a call whose result is
  treated as the generator body's return value, leaving `.next` unresolved.
  Model the iterator result produced by lowering; use `codegen/Generators` as
  the worksheet acceptance case.
- **Mutation and control flow:** `newres/MutationFlow.mls` records a reassigned
  array checked against its initializer's tuple length; accumulating both shapes
  would still reject valid later indexing. `newres/MemberVariables.mls` covers
  shape accumulation through local and member-variable assignments.
  Handler inference needs separate flows for the receiver, values passed to
  resumptions, and abortive results (`newres/HandlerResults.mls` and
  `codegen/ScopedBlocksAndHandlers`).
- **Captured activations:** preserve activation identity through captured
  functions, constructor aliases, reconstruction of the same class, and partial
  construction. Existing regressions include `CtxSens`, `ValCtxSens`,
  `Projections`, `RecursiveEnvironment`, `SpreadCalls`, and `InterfaceExposure`
  under `newres`. Local modules capturing outer binders are covered by
  `newres/InheritedTypeArguments.mls` and `ScopePaths.mls`. Do not turn unknown
  shapes into dynamic values or truncate capture paths to make these cases pass.
- **Exposed nominal results:** `newres/InterfaceExposure.mls` records a returned
  private class whose callable methods are not checked through its nominal result
  annotation. Follow declared member interfaces back to their implementations
  without exposing initializer shapes hidden by annotations.
- **Cross-block flow:** remaining cases include parameter flow in
  `basics/MiscArrayTests`, unfinished closures in `codegen/FirstClassFunctionTransform`,
  and the unresolved receiver in `codegen/ObjectMethodDebinding`.
- **Recursive inference:** `newres/RecursiveEquality.mls` now runs the unannotated
  deep-equality function and mutually recursive array callbacks. Pattern refinement
  reuses synthesized type arguments for the same test, constructor path, and input,
  allowing publisher deduplication to close the cycle. See the
  [scope and graph invariants](new-resolution-scopes.md).

### Patterns and generated references

Constructor tests in named-pattern definitions refine `as` bindings, including
uses in guards and transformations (`newres/PatternDefinitionBindings`). Compound
pattern outputs remain incomplete: conjunctions can produce pairs, chains feed
outputs into subsequent matches, and concatenations and rebuilt constructors need
appropriate result interfaces. Remaining worksheet blockers include:

- `ups/examples/Computation`: a numeric range does not yet refine its bound
  minute value enough for `toString` and `padStart`.
- `ups/examples/ListPredicates`: the transformation in a higher-order pattern
  argument leaves the result of `toString` without a resolved `length` selection.
- `ucs/patterns/where`, `ups/MatchResult`, `ups/SimpleTransform`, and several regex
  worksheets: pattern values and direct `.unapply`/`.unapplyStringPrefix` access.
- `ups/examples/{EvaluationContext,EvaluationContext2,HindleyMilner}`: unresolved
  member selections in worksheet-local definitions, despite the migration of the
  separate `ups/EvaluationContext` compilation fixture.

Generated matcher code must retain source targets and receiver paths through
lowering. Transfer rules must distinguish matched inputs, bound fields, and
transformed outputs; negation must not export positive bindings. Recursive pattern
flow still needs cycle-aware subscriptions and demonstrated convergence.

Acceptance coverage should include tuple/record extraction, nested and imported
constructors, aliases, guards, transformed results, repeated references, and
recursive UPS matchers. Preserve both runtime results and matcher structure.

### Calls, declarations, and diagnostics

- Implement contextual instance lookup and automatic argument insertion for calls
  with trailing `using` lists (`newres/LexerMigration.mls`). This blocks
  `parsing/Lexer` and `basics/CompanionModules_Classes`: contextual calls leave
  function values where completed results are expected. Passing instances
  explicitly would bypass the feature these tests need to exercise.
- Complete constructor-value member lookup (`codegen/ParamClasses`,
  `basics/DynamicInstantiation`) and module/call checks. Decide nominal
  module-forwarding compatibility for `basics/CyclicModuleForwarders` before
  changing its expected outcomes.
- Extend host interfaces where needed, including static descriptions of arbitrary
  WebAssembly exports. `Array.reduce` requires an initial value because declared
  methods cannot be overloaded by arity; the form without one would need
  an accumulator type that also includes the element type.
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
prelude before diagnosing a blocker. Keep deferred fixtures on legacy resolution.
The remaining legacy WASM worksheet, `wasm/Binaryen`, fails when given the common
language configuration. It exercises JavaScript host tooling alongside backend
directives and needs its configuration and backend diagnostics reviewed separately.

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
   without new failure suppressions or lost negative diagnostics.

Update the counts and remaining work after each retained batch. Test totals
include configurations and regression tests, so they are not migration counts.
