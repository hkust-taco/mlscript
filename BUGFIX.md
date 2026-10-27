# PR title

fix: avoid retaining lowering frames across statement sequences

# PR description

Statement lowering calls the rest of a block from inside each statement's continuation. This keeps the lowering frames for earlier initializers on the call stack while compiling later ones. Large module initializers can therefore overflow the JavaScript stack when the compiler itself runs under Scala.js.

Schedule the next statement as a local continuation, let the current statement finish lowering, and then run that continuation in a loop. Reconnect the resulting prefixes with the IR's `Begin` constructor. Each continuation retains its lowering context and accumulated record fields; `Begin` preserves scopes, statement order, fallthrough, and abortive control flow. Assert that each prefix schedules at most one continuation, so an unexpected change to this invariant cannot silently discard work.

Add a Scala.js compiler regression for a module containing many record-valued field initializers. A Scala test is needed here because the `.mls` diff-test runners compile on the JVM and cannot exercise the JavaScript compiler's stack limit. This change addresses stack growth across statement sequences; it does not claim to eliminate recursion from every compiler phase.

## Validation

- Reproduced `RangeError: Maximum call stack size exceeded` with `Lowering.blockImpl` in the trace on unmodified `hkmc2`.
- `ctest` and the focused Scala.js compiler regression pass with the fix.
- `hkmc2AllTests/test`: all 1,132 tests pass.
- Reviewed the complete diff from `hkmc2`; the full run produces no golden output changes.
