NOTE: This document was written by Codex Astra and has not been deeply reviewed;
it is not meant to be official documentation and
is in fact likely to contain parts that are unintelligible to readers who lack sufficient context.


# New-resolution suite migration

This document must describe only the **current state** of the migration: active
configuration, remaining work, and validation requirements. Remove obsolete blockers
and historical progress notes when updating it; Git history records earlier states.

## Scope and status

Language rules are in the [language reference](reference.md#resolution-interfaces).
Resolver invariants are in the [design notes](new-resolution-design.md), and
backend constraints are in [WASM resolution](new-resolution-wasm.md).

The table counts semantic worksheets, following their `:.` and `:..` configuration
imports. It excludes configuration files, shared declarations, dedicated `newres`
regressions, root scratch files, parser-only tests, the separate InvalML checker,
and the inactive `ucs/staging` directory. A migrated worksheet can import a legacy
compilation fixture; mixed-mode imports are supported.

| Diff-test suite | New resolution | Legacy resolution | Total |
| --- | ---: | ---: | ---: |
| apps | 17 | 0 | 17 |
| backlog | 5 | 3 | 8 |
| basics | 78 | 12 | 90 |
| block-staging | 4 | 3 | 7 |
| codegen | 106 | 20 | 126 |
| ctx | 3 | 10 | 13 |
| dead-param-elim | 14 | 0 | 14 |
| deforest | 21 | 0 | 21 |
| flows | 0 | 7 | 7 |
| handlers | 9 | 29 | 38 |
| interop | 10 | 0 | 10 |
| lifter | 11 | 5 | 16 |
| meta | 7 | 0 | 7 |
| nofib | 38 | 0 | 38 |
| objbuf | 2 | 1 | 3 |
| opt | 30 | 0 | 30 |
| std | 8 | 2 | 10 |
| syntax | 11 | 0 | 11 |
| tailrec | 2 | 3 | 5 |
| ucs | 69 | 1 | 70 |
| ups | 60 | 11 | 71 |
| wasm | 23 | 0 | 23 |
| Total | 528 | 107 | 635 |

| Compilation suite | New resolution | Legacy resolution | Total |
| --- | ---: | ---: | ---: |
| Main | 46 | 4 | 50 |
| Applications | 18 | 2 | 20 |
| Nofib | 38 | 1 | 39 |
| WASM | 1 | 0 | 1 |
| Total | 103 | 7 | 110 |

`LegacyGenericLibrary` deliberately uses legacy resolution to test mixed-mode
imports. The other legacy compilation fixtures are listed below. Counts describe
source configuration, not the number of test cases reported by SBT.

## Remaining compilation fixtures

| Fixtures | Remaining work |
| --- | --- |
| `FingerTreeList` | New resolution exceeds the compilation time limit around recursive trees and tuple spreads. |
| `CSP`, `QuoteExample1` | Quasiquote type selections and wildcard-reference lowering are unsupported. |
| `parsing/Lexer` | Token constructors with trailing `using` parameters need automatic contextual argument insertion. `newres/LexerMigration` reproduces the missing behavior. |
| `parsing/ParseRule` | Recursive rule inference exceeds the compilation time limit when compiling consumers. Callback inputs exposed by `Iter.mapping` also leave `rule.map` with an unknown receiver. |
| `nofib/sorting` | New resolution exceeds the compilation time limit, including with the required `int_of_char(c: Str)` parameter annotation. |

## Remaining worksheet constraints

Legacy worksheets require more than enabling the language configuration. The
following constraints identify the current failing behavior and representative tests.

- **Contextual calls and module checks:** `basics/CompanionModules_Classes` can
  produce a function instead of the completed result because implicit `using`
  arguments are not inserted. Several `ctx` and module worksheets also lose
  required negative diagnostics. `basics/CyclicModuleForwarders` needs a decision
  about nominal module-forwarding compatibility. Passing contextual arguments
  explicitly would bypass the feature these tests exercise.
- **Constructor and anonymous-object interfaces:** `codegen/ParamClasses`,
  `basics/ValMemberSymbols`, and `lifter/AnonClasses` exercise constructor members, partially
  constructed objects, or anonymous refinements that lack the required interfaces.
  `lifter/PrivateMutableFields` cannot resolve anonymous `new with` expressions.
- **Mutation and returned shapes:** `codegen/SetStmt` retains an initializer's
  tuple length after reassignment (`newres/MutationFlow`). `basics/Records` needs
  callable result precision across branches with different parameter lists.
  `std/LazyFingerTreeTest` loses the private view interface through slicing helpers;
  its general slice result also includes finger trees without `materialize`.
  `lifter/Loops` includes an implicit unit result after an unconditional loop return,
  preventing the returned closure from being called directly.
- **Generators:** `codegen/Generators` needs the iterator interface produced by
  generator lowering. `newres/GeneratorResults` records the unresolved `.next`.
- **Handlers:** handler-generated receiver and member references remain unresolved
  in `handlers`, `codegen/ScopedBlocksAndHandlers`, and handler cases in `lifter`.
  Receiver flow, resumption arguments, and abortive results need distinct handling
  (`newres/HandlerResults`).
- **Recursive definitions and staged functions:** `basics/FunDefs` and recursive
  getter cases in `tailrec` can overflow during resolution. `block-staging/Functions`
  and `codegen/FirstClassFunctionTransform` encounter unfinished generated symbols.
- **Legacy flow analysis:** the `flows` worksheets run a separate flow pass that
  does not handle new-resolution selections and can throw on `NewSel` nodes.
- **Runtime instrumentation and privacy:** `codegen/ObjectMethodDebinding` loses
  an expected runtime error. `codegen/PrivateMembers` loses privacy diagnostics
  and required runtime errors. These worksheets must preserve their checks.
- **Pattern values and transformations:** `ucs/patterns/where`, `ups/MatchResult`,
  `ups/SimpleTransform`, `std/RenderingTest`, and regex worksheets use pattern
  values or direct `.unapply`/`.unapplyStringPrefix` access. Range and higher-order
  transformations lack result interfaces in `ups/examples/Computation` and
  `ups/examples/ListPredicates`. `ups/examples/EvaluationContext2` and the
  Hindley–Milner worksheets additionally need recursive member interfaces.
- **Quasiquotes:** `codegen/Quasiquotes` needs type-selection and generated-reference
  support. Pattern and quote lowering must preserve source targets and receiver paths.

Focused coverage for capture identity and nominal interfaces is in `newres/CtxSens`,
`ValCtxSens`, `Projections`, `RecursiveEnvironment`, `SpreadCalls`, `ScopePaths`,
`InheritedTypeArguments`, and `InterfaceExposure`. These tests constrain fixes to
recursive and exposed interfaces; unknown shapes must not silently become dynamic.

## Migration rules

- Load the common language configuration before the first blank line. Most suites
  use `:.` and a local `.mls` containing `:..`. Lifter worksheets use `:..` for the
  language configuration and `:.` for their existing lifting flags. Preserve all
  execution flags. `wasm/Binaryen` imports the parent language configuration with
  `:..` because it tests JavaScript host tooling rather than the compiler's WASM backend.
- Add ordinary parameter and result interfaces before attributing a failure to
  language design. Use shared `Indexable` and `IterableIndexable` aliases from
  `decls/Prelude`; avoid invariant `Any` arguments and unnecessary casts.
- Keep host declarations accurate. Array callbacks receive three arguments for
  `map`/`filter`/`forEach` and four for `reduce`; use `pass1`, `pass2`, or unused
  rest parameters where appropriate. Static callbacks must retain these arities.
- Explicitly open names that shadow builtins, including operators and helpers such
  as `equals`, `render`, and `Symbol`. Use dynamic selectors for deliberate host
  reflection and undeclared property additions, preserving observable effects.
  For tests of checked dynamic access, annotate receivers as `dyn` and keep ordinary
  selections: raw `!` selectors omit checks that these tests need to exercise.
- Review values and logs as well as test-runner success. A tolerated error or
  an uncalled function can hide a regression. Existing invalid operations may
  need compilation-error expectations in addition to runtime-error expectations.
- Keep blocked worksheets on their existing configuration with their source and
  goldens intact. Do not add failure suppressions or dynamic escapes to bypass
  unresolved language features.
  Reproduce compiler failures in focused `.mls` regressions.

Host-interface precision still needs work for `Array.concat`, `Array.splice`, and
`Array.from`. `Array.reduce` without an initial accumulator also needs a signature
that includes the element type; declared methods cannot overload by arity.
`newres/MutableArrays` covers the missing insertion constraint for `splice`.

## Validation

Follow the [repository test workflow](../README.md#running-the-tests-1):

1. Run `ctest` before worksheet tests to regenerate main runtime dependencies.
   Use `catest`, `cntest`, and `cwtest` for application, Nofib, and WASM fixtures.
2. Run affected worksheets with `dtest`, `adtest`, `ndtest`, or `wdtest`; inspect
   all rewritten goldens and retain existing successful results and negative intent.
3. Run `hkmc2AllTests/test` for the retained changes. Commit the final golden output
   together with the migration, using the agent's own identity for agent commits.
4. Update this inventory and remove resolved blockers. Remove legacy configurations
   only when every covered worksheet can migrate without lost coverage.
