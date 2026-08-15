# `#dbg` directive progress

## Requirements

- Add a `#dbg` directive whose settings are stored in `Config`, analogously to `#lang`.
- Support the compiler phases represented by the existing diff-test debug commands:
  - parsing (`:dp`),
  - elaboration (`:de`),
  - resolution (`:dr`),
  - lowering (`:dl`), and
  - optimizations (`:dopt`).
- Mirror the existing IR display commands with `showIR` (`:sir`) and
  `showOptimizedIR` (`:soir`).
- Mirror the parsed, elaborated, and lowered tree displays with `showParsedTree`
  (`:pt`), `showElaboratedTree` (`:elt`), and `showLoweredTree` (`:lot`).
- Accept both shorthand flags and named booleans, including:
  - `#dbg('parsing)`;
  - `#dbg(elaboration: true)`.
- Support a selectable debug destination:
  - `StdIO`, which is the default and may be omitted;
  - `File("out.mls")`, resolved relative to the active configuration's base directory.
- Support the annotation form on individual definitions, for example
  `@dbg('elaboration) fun foo() = ...`, without enabling the same phase for unrelated definitions.
- Keep the feature available in diff-test files as well as through `MLsCompiler`.
- Diagnose unknown flags, malformed boolean values, malformed destinations, and unsupported arguments.

## Implementation plan

1. Add immutable debug settings and output-destination types to `Config`, with all phase flags disabled and `StdIO` selected by default.
2. Extend `ConfigParser` with one parser shared by `#dbg(...)` and `@dbg(...)`; support quoted phase names, named phase booleans, and `out`.
3. Elaborate `#dbg` into the existing persistent `SetConfig` representation and `@dbg` into a per-definition configuration annotation.
4. Reuse the existing phase trace loggers, with destination-aware dynamic scoping only where a definition annotation must temporarily change their configuration.
5. Discover module/block-level parsing debug settings after an initial parse and, when requested, repeat parsing with lexer/parser tracing sent to the selected destination.
6. Drive elaboration, resolution, lowering, optimization, and IR display from the effective `Config`; retain the legacy diff-test commands by sharing their existing code paths.
7. Add positive and negative diff tests covering shorthand/named syntax, persistence, destination selection, and definition-local elaboration output.
8. Run `ctest`, focused diff tests while iterating, and finally `hkmc2AllTests/test`; review and commit all intentional golden changes.

## Progress

- [x] Requirements summarized and implementation plan recorded.
- [x] Configuration model and parser implemented.
- [x] Compiler and diff-test tracing integrated.
- [x] Definition-local scoping implemented.
- [x] Regression tests and golden outputs added.
- [x] Full prescribed test suite passes.
- [x] Custom optimization reporting removed in favor of the existing `:dopt` trace path.
- [x] `showIR` and `showOptimizedIR` share the existing `:sir` and `:soir` display paths.
- [x] `@dbg` configuration overrides remain attached to lowered IR definitions, including methods.
- [x] Definition-local IR display prints only definitions selected by `@dbg`, through the existing IR printer.
- [x] Parsed, elaborated, and lowered tree displays support both `#dbg` and definition-local `@dbg`.
