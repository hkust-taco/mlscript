---
name: hkmc2-difftests
description: Work with HKMC2 DiffTests where golden snapshots are embedded in `.mls` files as `//│ ...` lines and updated in place by the test runner. Use when editing or reviewing files under `hkmc2/shared/src/test/**/*.mls`, running `hkmc2DiffTests` or watcher loops, diagnosing mismatches between diagnostics and expectations (`:e`, `:re`, `:expect`, etc.), or deciding whether rewritten snapshot lines should be committed.
---


# General

Please review `/AGENTS.md`.


# HKMC2 DiffTests

Run HKMC2 inline golden-file tests and treat file rewrites as first-class test output.

## Quick Workflow
1. Verify local environment once per machine.
2. Edit `.mls` test blocks and test commands. Use `hkmc2/shared/src/test/mlscript/HkScratch.mls` for temporary experiments, or create a new `.mls` file for a new test case.
3. Run direct `sbt` commands (never `cs launch sbt` for this repo).
4. Review rewritten `//│` lines with git diff.
5. Keep intentional rewrites, then rerun until clean.
6. Revert temporary `HkScratch.mls` edits before committing.

Read [execution-workflow.md](references/execution-workflow.md) for exact commands and onboarding flow.

## Block Model And Rewrite Model
- Parse each `.mls` file as sequential blocks, usually split by blank lines.
- Parse `:command` lines as per-block options.
- Ignore existing `//│ ...` lines as old snapshots.
- Compile/run the block and emit fresh `//│ ...` lines.
- Rewrite the file in place when generated output differs.
- Fail only on policy violations (unexpected diagnostics, missing expected diagnostics, failed `:expect`, etc.).

Do not treat rewritten files as automatic failures. Treat them as candidate snapshot updates and review them.

## Command Semantics To Apply
- `:js`: execute JS backend for the block.
- `:silent`: suppress auto-printing of defined values.
- `:expect <text>`: assert final rendered result equals exact text.
- `:pe`, `:e`, `:re`, `:ge`, `:w`: expect parse/type/runtime/codegen/warning diagnostics.
- `:fixme` or `:todo`: tolerate temporary failures under current policy.
- `:wasm`, `:wat`, `:fwat`, `:swat`, `:llir`: enable lower-level backend outputs.

Read [commands-and-policies.md](references/commands-and-policies.md) when you need deeper behavior details or troubleshooting logic.

## Discovery Scope
- Discover test files from `hkmc2/shared/src/test/**/*.mls`.
- Diff runs exclude paths containing `staging` and `mlscript-compile`.
- Assume `.mls` is the only supported extension for these diff tests.

## Guardrails
- Use repo README commands as source of truth for test execution.
- Use direct `sbt ...` commands for this project.
- For focused runs or updates on specific test files, follow the targeted workflows documented in `README.md` (for example `testOnly ... -- -z ...`, focused sets, and `ChangedTests.cmd` with watcher).
- Run `npm install` before JS/Wasm-heavy test workflows when dependencies are missing.
- Prefer reviewing `git diff`/`git status` immediately after a diff-test run.
- Reset only unintended rewritten test files; keep intentional snapshot updates.
