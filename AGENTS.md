# Using the MLscript code base


## Workflow

When working on Scala code, use the Metals MCP tools when available for semantic
symbol searches, inspection, documentation, and finding usages, and for quick
file or module compilation feedback. The project configurations for Codex
(`.codex/config.toml`) and Claude Code (`.mcp.json`) can launch the headless
Metals server automatically; keep their Metals versions in sync.
If Metals is unavailable, continue with source searches and SBT, and report the
connection problem. Metals compilation and test tools do not replace the SBT
test prerequisites and final validation below.

It is best to leave the SBT shell open (by just typing the `sbt` command line)
and issue commands directly in that shell, as SBT startup is very slow.

Before running individual tests, make sure to first run `ctest`,
so that the compilation-tests (in `hkmc2/shared/src/test/mlscript-compile/`) are run
and produce the JS files that are needed at runtime for the other tests (in `hkmc2/shared/src/test/mlscript/`).
Note that this only affects the main compilation tests;
there is also `cntest` for nofib compilation tests, `catest` for application compilation tests,
and `cwtest` for WASM compilation tests.

Before finishing work with retained code or test changes, run `hkmc2AllTests/test`
to make sure the codebase compiles and all tests succeed;
this covers `ctest`, so no need to run `ctest` separately.
Full validation is not required for read-only investigations, documentation-only edits,
and temporary experiments whose changes have all been reverted.

After you are done fixing all the problems and all the tests pass,
*you need to commit the resulting golden test output changes*.
Any commit that does not include the latest changes to test outputs will fail the CI.

Please also read the files in `.github/skills/hkmc2-difftests`.

Use `*.mls` diff tests for compiler behavior. Do not add Scala tests that duplicate
that coverage or merely pin internal representation or assertion details. Reserve
unit tests for properties diff tests cannot reliably observe, such as concurrency,
cache isolation, bounded graph growth, or algebraic laws; state the extra coverage.

Before adding new diff tests, make sure they are not already covered by existing tests.
All new diff-test files you create should go into `hkmc2/shared/src/test/mlscript/slop/`
unless there is a good reason to put them elsewhere.

When you create a commit, author it under your (the agent's) own identity,
not under the user's identity.
Set this identity for the commit command only
(e.g., `git -c user.name=... -c user.email=... commit ...`).
Do not change repository-local or global Git identity configuration.


## Design Philosophy

**Confirm language-design decisions before implementing them.** Propose changes
to source syntax, language semantics, or public library contracts and obtain the
user's confirmation unless that specific design is already explicitly approved.
Authorization to fix compiler behavior does not by itself authorize introducing
annotations, changing member naming or dispatch rules, or extending public APIs.

You are working on an industry-strength compiler codebase.
Although its test suite is extensive, tests alone are not enough to determine the quality of a change;
the goal is not just to "make everything green".

When making a change, you must reason about whether it is *completely correct*,
including with respect to edge cases that may not be covered by existing tests
or that will only become relevant later:
you should take into account the future maintainability of the code,
preferring principled designs over ad-hoc short-term solutions.

The worst possible outcome would be to introduce changes that might lead to silent miscompilation.
If you are not sure about whether some invariants you need do hold,
assert them using `softAssert` or `assert` (if `softAssert` is not available).
If you know that some invariants temporarily do not hold but will be fixed in the future, use `softTODO`.

It is very much preferable to add regression tests and `:fixme`s for bugs that should be fixed later
rather than to introduce temporary workarounds that bypass bugs just to make the tests pass.


## Coding Style

Never use `asInstanceOf` unless absolutely necessary. If you find yourself using `asInstanceOf`, it's a sign that your code may need to be refactored to be more type-safe.

Never use non-local mutation unless absolutely necessary.
In particular, you should always refrain from adding new global mutable state to things like the Symbol classes
unless there is no reasonable alternative, in which case you should document in the code
exactly where the mutable state is supposed to be defined and used.

Never use default arguments in core business logic.
Default arguments should be reserved for user-facing APIs.
Do NOT encode default arguments through overloading to skirt this rule.

Keep it DRY: if you find yourself copying and pasting code,
consider refactoring it into a reusable function or class.
The goal of minimizing code duplication is to improve maintainability:
the logic for handling cases that ought to be similar should be centralized.

**Document your code**:
Use comments to explain the intent behind complex logic,
especially if it is not immediately clear from the code itself.
When appropriate, explain the history of what led to the current implementation,
especially if it involves non-obvious decisions/trade-offs
or if alternative approaches were considered and rejected.

Comments must be understandable from the current code alone, without the conversation,
commit history, or an earlier version of the implementation. Explain the concrete
invariant, behavior, or failure being prevented. Name the relevant data and operations;
avoid vague claims about where a "lifecycle" or "responsibility" belongs. If history
or a rejected alternative matters, include enough context to explain the tradeoff
after commits are squashed.

Do NOT include comments that simply describe what the code is doing
without adding any additional insight, or comments that talk about
parts of the system that are not directly related to the code being commented on.


## User-Facing Diagnostics

Never use `showDbg`, `shwDbg`, raw AST/IR `toString` output, or other debug-only
representations in user-facing error messages, warnings, or diagnostic notes.
Use source-level names and user-facing descriptions, with source locations to
identify the relevant definitions or expressions. Do not expose internal symbol
IDs, resolution marks, or compiler representation details to users.
Debug representations belong only in internal logs and explicitly requested
debug output, not in ordinary diagnostics.


## Editing Style

Do not remove existing `end` markers.

Never strip indentation whitespace.

Empty lines in this project are usually significant.
They help to visually identify blocks and groups of blocks of code
(multiple empty lines separates groups of blocks hierarchically).
You should never remove pre-existing empty lines as part of your changes
unless they are at the very end of the file:
while we often leave some there for easier future editing by programmers,
it seems AI agent toolings like `apply_patch` reliably removes them anyway, which is okay
(note: this is discussed at https://github.com/openai/codex/issues/21121#issuecomment-4608911199).

When removing a block of code separated by empty lines, remove the separating empty lines as well,
eg, `A\nB\nC` -> `A\nC` (not `A\n\nC`) and `A\n\nB\nC` -> `A\n\nC` (not `A\nC` nor `A\n\n\nC`).

**Important:** When working on a PR, make sure to check the diff of the whole PR (including all commits)
for accidental empty-line or indentation changes introduced by AI agents. Distinguish that diff noise
from intentional edits by the user or other human contributors by checking the commit history.
Preserve intentional contributor edits, including added indentation on empty lines.


## Manipulating IR representations

When working with IR representations, please refer to the "Important design notes" in `hkmc2/shared/src/main/scala/hkmc2/codegen/Block.scala`.

