# Commands And Policies

## Runner And Discovery
- Discovery root: `hkmc2/shared/src/test`.
- File type: `.mls`.
- Diff test runs exclude paths containing `staging` and `mlscript-compile`.
- `DiffMaker.run()` rewrites file content whenever generated output differs from current file text.

## Per-Block Processing Model
1. Read lines sequentially.
2. Parse `:command` lines and update command state.
3. Skip old snapshot lines starting with `//│ ` as input.
4. Execute compilation/runtime pipeline for the block.
5. Emit new `//│ ` output lines.
6. Compare full generated content to original file content; write back if changed.

## High-Value Commands
- `:js`: run JS backend path and print/evaluate runtime results.
- `:silent`: suppress automatic value printing.
- `:expect <text>`: assert the rendered final result equals `<text>`.
- `:pe`: expect parse errors.
- `:e`: expect type errors.
- `:re`: expect runtime errors.
- `:ge`: expect compilation/codegen errors.
- `:w`: expect warnings.
- `:fixme` and `:todo`: expect and tolerate failures (failing in their absence).
- `:breakme`: tolerate temporary expected lack of failures.
- `:ignore`: ignore failures, but do not expect them, either.
- `:wasm`: enable Wasm path.
- `:wat`, `:fwat`, `:swat`: print Wasm text variants.

## Debugging Commands
- `:dp`: Debug parsing.
- `:de`: Debug elaboration.
- `:dr`: Debug resolution.
- `:dl`: Debug lowering.
- `:dopt`: Debug optimizations.
- `:sir`: Show intermediate representation (IR).
- `:soir`: Show optimized IR.
- `:sjs`: Show generated JS.

## Failure Policy
- Unexpected diagnostics fail (error/warning kind mismatches).
- Missing expected diagnostics fail (for `:pe`, `:e`, `:re`, `:ge`, `:w`) unless tolerated by `:todo`/`breakme` policy paths.
- `:expect` mismatch fails as a runtime diagnostic.
- Rewritten files alone are not a failure; they are snapshot updates to review.

## Practical Review Rules
- Treat `//│` changes as test artifacts, not source edits.
- Commit snapshot rewrites only when behavior changes are intentional.
- Prefer narrow reruns (`hkmc2DiffTests/test` or watcher) while iterating on a small set of `.mls` files.
