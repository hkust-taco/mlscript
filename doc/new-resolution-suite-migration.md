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
| apps | 13 | 3 | 16 |
| Total | 300 | 73 | 373 |
| wasm (separate backend) | 22 | 1 | 23 |

All twelve `apps/parsing` worksheets use new resolution, but some implementation
modules they import still use legacy resolution. Worksheet migration does not
imply that its dependencies have been migrated.

| Compilation suite | New resolution | Legacy resolution | Total |
| --- | ---: | ---: | ---: |
| Main (including quotes, UPS, and regression fixtures) | 38 | 10 | 48 |
| Applications | 12 | 8 | 20 |
| Nofib | 37 | 2 | 39 |
| WASM | 1 | 0 | 1 |
| Total | 88 | 20 | 108 |

These totals include the new-resolution `NamedFieldLibrary` regression fixture.
They count language directives in source files, not test-runner test cases.
`CachedHash` and `parsing/TreeHelpers` already use new resolution and are included
in the totals; the earlier table undercounted them.

### Recent compilation ports

The following 39 fixtures migrated after the previous documentation revision:

| Suite | Migrated fixtures |
| --- | --- |
| Main | `Benchmark`, `Char`, `Iter`, `MutMap`, `ObjectBuffer`, `QuoteExample`, `Stack`, `TreeTracer`, `XML`, `ups/EvaluationContext` |
| Applications | `parsing/Rules`, `parsing/Test`, `parsing/Tree` |
| Nofib | `NofibPrelude`, `ansi`, `atom`, `awards`, `cichelli`, `circsim`, `constraints`, `cryptarithm2`, `cse`, `eliza`, `fish`, `integer`, `knights`, `lambda`, `lcss`, `life`, `mate`, `minimax`, `para`, `power`, `pretty`, `primetest`, `scc`, `secretary`, `treejoin` |
| WASM | `wasm/Wasm` |

These ports add exposed callback, collection, and nominal interfaces. The `Iter`
and `cse` investigations also fixed lexical-scope transport for omitted type
arguments; `newres/InferenceHoleScopes` records the regression coverage.
`Char.AnyChar` now uses `s.length` directly: named-pattern definitions propagate
shapes from class tests into alias bindings, guards, and transformation parameters.
The WASM utility fixture declares its JavaScript/WebAssembly boundary explicitly
with `dyn`; its migration does not mean that all host exports have static interfaces.

### Worksheet retry, 2026-10-01

All 115 then-legacy worksheets in the suites above were tried with `:.`, after
rebuilding their compilation fixtures. Forty-one ports were retained: 6 basics,
6 codegen, 17 UCS, 9 UPS, and 3 WASM worksheets. Thirty need only the configuration
change and regenerated goldens. The other eleven need these small changes:

| Worksheets | Source or expectation changes |
| --- | --- |
| `basics/Classes`, `ucs/syntax/SimpleUCS` | Structural interfaces for the `id` and `get` callbacks used by otherwise unconstrained parameters. |
| `ucs/normalization/Deduplication` | `Str` on the helper that selects `length`. |
| `ups/examples/BasicSeqStackParse` | Array interfaces for the parser stack and token input, and `Str` for the text input. Existing parser results and known limitations are preserved. |
| `codegen/ImportedOps`, `ucs/examples/ListFold` | Explicitly open the binary `~` operator to override the builtin. |
| `ucs/examples/EitherOrBoth` | Explicitly open `~` and correct the binary callback signature to `(A, B) -> C`; runtime checks cover all three fold branches. |
| `ups/examples/DoubleTripleList` | Use `testList!head` and `testList!tail` for the reflectively installed getters in the explicit logging check. Reads through `Cons`'s `val` interface are pure. |
| `basics/Inheritance`, `basics/CompanionModules_Functions`, `basics/Overloading` | Remove resolved `:todo`/`:fixme` expectations. The separate non-inlined overload failures remain covered. |

Newly migrated pattern worksheets include `ucs/general/BooleanPatterns`,
`ucs/patterns/{BooleansOps,ConjunctionPattern,RecordPattern,String}`,
`ups/RecursiveTransformations`, and `ups/examples/Record`. The WASM ports are
`Basics`, `DeadConstructorElim`, and `DeadParamElim`.

`basics/CompanionModules_Classes` passed the runner's failure policy but was not
retained: its contextual call returns a function instead of `42` because automatic
`using` insertion remains unsupported. Reviewing successful values as well as
failure markers is necessary when accepting a migration.

Blocked worksheets keep their original source and goldens. No new failure
suppressions were added to obtain these ports.

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

Legacy consumers can read completed new-resolution symbols in imported signatures.
The prelude, `Option`, `apps/parsing/Token`, and `apps/parsing/Keywords` use new
resolution; all option consumers share `Option`'s constructor identities. Imported
nodes must not be re-resolved, and erased types must not be queried before erasure.
Other parser implementation modules retain legacy resolution and need individual
migration checks even though their worksheets use new resolution.

The remaining compilation fixtures are listed below. The 2026-10-01 worksheet
retry did not re-probe these fixtures in new resolution; the interface and compiler
issues are investigation leads from earlier compilation attempts, not a claim that
every listed file still needs a compiler change.

| Legacy fixtures | Outstanding checks |
| --- | --- |
| `Block`, `Shape` | Nominal members, callback arity, and the public interface for `showArm`. |
| `LazyArray`, `FingerTreeList`, `LazyFingerTree` | Collection interfaces and shape propagation. An earlier `FingerTreeList` probe exceeded the 25-second limit while combining tuple spreads; the candidate-storage fix is on `LPTK/new-resolution-no-hashing`. Retry against the current resolver before attributing a new timeout to that cause. |
| `Runtime`, `Rendering`, `Predef` | Runtime/host interfaces and their consumers; `Predef.use` also depends on contextual arguments. |
| `CSP`, `QuoteExample1` | Quasiquote type selections and wildcard-reference lowering. |
| `apps/Accounting`, `apps/CSV` | Public interfaces and their worksheet consumers. |
| `parsing/Extension`, `ParseRule`, `Parser`, `ParseRuleVisualizer`, `parsing-web-demo/main` | Remaining exposed interfaces and mixed-mode parser dependencies. `Rules`, `Test`, `Tree`, and `TreeHelpers` are already migrated. |
| `parsing/Lexer` | Calls with trailing contextual parameters leave function values where tokens are expected. The binary `~` is explicitly imported. |
| `nofib/lastpiece`, `nofib/sorting` | Remaining Nofib interface and flow issues; all other Nofib fixtures use new resolution. |

To reproduce a blocker, temporarily add the language directive to the named
compilation fixture and run `ctest <name>` or `catest <name>` as appropriate.
The blocked fixtures retain their existing resolution mode.

The 2026-09-30 `Lexer` investigation fixed an assertion encountered before its
listed blockers: ancestor constraints applied a nominal value's caller path to
its parent annotation without first leaving the subclass's instance scope.
The trigger is passing `Lexer.string`'s `[Int, Token.Literal]` result to the
helper expecting `[Int, Token.Token]`.
Parent type arguments now enter that scope before substitution, and ancestor
constraints and inherited member lookup share the corresponding exit. Only
parameters used by the parent are captured, including when recursively observing
a legacy imported type. `newres/InheritedTypeArguments.mls` covers qualified
subclass annotations, tuple transport, multiple parent steps, callback inputs,
and caller separation. A local module's captured outer binder still has a
separate scope failure recorded there with `:fixme`.

The earlier 2026-09-30 probe of 61 legacy compilation fixtures found no additional
ports from the ancestor-constraint correction alone. Subsequent interface
annotations and the omitted-type-argument scope fix enabled the compilation ports
listed above. Do not use the old probe as the current migration inventory.

`newres/LexerMigration.mls` covers the explicit operator import and records missing
contextual argument insertion. Completing that migration requires contextual
instance lookup and argument insertion in the new resolver; passing every instance
explicitly would bypass that missing feature rather than complete it.

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
  do not block the current implementation batch. The reproduced alias/projection
  termination failures now have fixes and regressions; the remaining
  [whole-graph convergence audit](new-resolution-future-work.md#whole-graph-convergence-audit)
  and local allocation/replay bounds are documented in the
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

### Reflective getter instrumentation

`ups/examples/DoubleTripleList` uses `Object.defineProperty` to replace `Cons.head`
and `Cons.tail` with getters. New resolution identifies their direct reads as
reads of the original `val` members, which are pure and may be discarded when
unused. Reflectively replacing those data properties does not change the contract
of their declared interface. This is not a getter-preservation bug.

The migrated worksheet uses `testList!head` and `testList!tail` in its explicit
logging check to observe the JavaScript getters dynamically. Both log lines and
all existing matcher results and logs are preserved. `newres/GetterReadEffects.mls`
covers direct and abstract getters, both dynamic-selection forms, and the nominal,
structural, and abstract field interfaces whose unused reads are eliminated.
Ordinary MLscript getter reads remain effectful; an effectful getter cannot be
assumed to satisfy a pure `val` interface merely because it returns the right type.
The abstract-val case also exhibits the same elimination under legacy resolution.

### Patterns and generated references

Named-pattern definitions now analyze an unknown input through the same shape
matcher used for direct matches. Constructor tests refine `as` bindings; guards
retain their binding symbols, and transformations receive those shapes through
their generated parameters. `newres/PatternDefinitionBindings` covers this flow,
and `Char.AnyChar` no longer needs its redundant `Str` annotation.

This does not supply every compound pattern's output interface. Conjunctions test
both operands against the input and can produce a pair; chains feed one output
into the next match. Concatenations and rebuilt constructor outputs remain
conservative. Remaining worksheet blockers include:

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

- Implement automatic contextual argument insertion for `Lexer` calls to
  `Token.integer`, `symbol`, and related APIs with trailing `using` lists.
  Operators that override builtins must be imported explicitly, as in `Lexer`.
- Complete constructor-value member lookup (`codegen/ParamClasses`,
  `basics/DynamicInstantiation`) and module/call checks. `basics/GenericClasses`
  now migrates with its type-argument-count diagnostics intact. Decide nominal
  module-forwarding compatibility for `basics/CyclicModuleForwarders` before
  changing its expected outcomes.
- Extend host interfaces where needed. `Map.set`, `Reflect.set`, and the array
  methods needed by `Iter` now have declarations; statically describing arbitrary
  WebAssembly exports remains separate work. `Array.reduce` requires an initial
  value because declared methods cannot be overloaded by arity; the form without one would need
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
The WASM fixture `wasm/Wasm.mls` is migrated. The remaining legacy WASM worksheet,
`wasm/Binaryen`, still fails when given the common language configuration; it
exercises JavaScript host tooling alongside backend directives and needs its
configuration and backend diagnostics reviewed separately.

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
