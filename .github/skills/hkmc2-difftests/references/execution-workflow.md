# Execution Workflow

## Prerequisites
- Install JDK, `sbt`, and Node.js.
- **Run `npm install` in the repository root** to install all required npm packages (TypeScript, Binaryen, etc.).
  This step is **mandatory** for JS and WASM test paths. In particular, the WASM tests
  (`hkmc2/shared/src/test/mlscript/wasm/`) depend on the `binaryen` npm package for
  WAT validation, formatting, and compilation to WebAssembly binary. Skipping `npm install`
  will cause all WASM tests to fail with module-not-found errors at runtime.

## Core Commands
- Full HKMC2 test pass: `sbt hkmc2AllTests/test`
- Compiler compile tests: `sbt hkmc2JVM/test`
- Diff tests only: `sbt hkmc2DiffTests/test`
- Diff watcher: `sbt "~hkmc2DiffTests/Test/run"`

Use direct `sbt` commands for this repo. Avoid `cs launch sbt` because of known environment differences.

## Typical Loop
1. Edit a `.mls` test file under `hkmc2/shared/src/test/`.
2. Use `hkmc2/shared/src/test/mlscript/HkScratch.mls` for temporary checks, or create a dedicated new `.mls` file for durable test coverage.
3. Run `sbt hkmc2DiffTests/test` or watcher mode.
4. Inspect rewritten `//│ ...` lines and diagnostics.
5. Check `git status` and `git diff`.
6. Keep intentional output updates; discard accidental rewrites and rerun.
7. Revert temporary `HkScratch.mls` edits before committing.

## Targeted Runs And Updates
- Use README-guided focused execution when iterating on specific test files:
  - `testOnly ... -- -z <pattern>` for name-filtered runs.
  - Focused test path sets in the Scala test harness when needed.
  - `ChangedTests.cmd` with watcher mode to rerun only unstaged changed tests.
- Treat `README.md` as source of truth for exact syntax and current project-specific examples.

## If Results Look Wrong
- Confirm you are running from repo root.
- Confirm `npm install` completed.
- Check whether command markers in the test block changed behavior (`:js`, `:silent`, `:expect`, `:e`, `:re`, etc.).
- Re-run with direct `sbt`.
