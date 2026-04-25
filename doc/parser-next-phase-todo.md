# Parser Next Phase Todo

Created: 2026-04-25

This is the working board for the next parser and web-demo phase. Do not start
implementation until the user explicitly says "yes you can continue".

## Ground Rules

- Keep this file updated after each completed task so progress is visible.
- If work feels unclear or gets interrupted, reread this file before proceeding.
- Limit each implementation phase to the specific part named by that phase.
- Make a commit after each specific small task is finished.
- Each commit title should include the phase label, for example
  `Parser P1: Add pattern syntax kind`.
- Do not stop until all tasks in this board are completed unless a truly fatal
  error blocks further work.
- If a truly fatal error occurs, write a separate Markdown file under `doc/`
  explaining exactly why work stopped, what was attempted, what failed, and what
  remains blocked.
- For `.mls` DiffTests, follow the HKMC2 DiffTests workflow and commit
  intentional generated `//│` output changes.
- Before focused app/runtime tests, make sure `hkmc2JVM/test` has been run in
  the current work session.
- Before final handoff for the whole phase set, run `hkmc2AllTests/test`.
- `doc/Parsing.md` is irrelevant to this work. Do not include its advanced
  indentation TODOs in this phase's implementation or future-work notes unless
  the user explicitly reprioritizes them later.

## Status Legend

- `Pending`: not started.
- `In Progress`: actively being implemented.
- `Done`: implemented, tested, documented where needed, and committed.
- `Deferred`: intentionally left for future work.
- `Blocked`: cannot proceed without clarification or a prerequisite.
- `Skipped`: investigated and intentionally not changed, with reason recorded.

## Phase P0: Approval Gate

| ID | Status | Task | Commit |
| --- | --- | --- | --- |
| P0-01 | Done | Consolidate the user's full instruction into this todo file. | Not required unless requested. |
| P0-02 | Done | Show this file to the user and wait for explicit approval. | Not required. |

## Phase P1: Parser Pattern Implementation

Goal: complete all three high-priority pattern items from
`doc/parser-project-follow-up-review.md`.

| ID | Status | Task | Commit Label |
| --- | --- | --- | --- |
| P1-01 | Done | Introduce a dedicated `pattern` syntax kind with dedicated parser rules instead of parsing patterns through `term`. | `Parser P1` |
| P1-02 | Done | Support pattern aliases such as `p as x`, then restore/adapt Caml Light examples that previously removed `as` aliases. | `Parser P1` |
| P1-03 | Done | Support pattern alternatives inside one branch, such as a space-character case sharing a branch with a tab-character case, then restore/adapt the Word Count example. | `Parser P1` |
| P1-04 | Done | Add or update focused parser DiffTests for the new pattern behavior and commit generated output. | `Parser P1` |

## Phase P2: Parser Cleanup

Goal: finish the two medium/low parser cleanup items after pattern work.

| ID | Status | Task | Commit Label |
| --- | --- | --- | --- |
| P2-01 | Done | Clean up top-level `let` handling so it no longer relies on the current manual `Tree.LetIn(..., Tree.Empty)` repair path where practical. | `Parser P2` |
| P2-02 | Done | Implement the conservative Caml Light fixed prefix-operator rule for `-`, `-.`, and `!`, avoiding a broad arbitrary-prefix-operator mechanism. | `Parser P2` |
| P2-03 | Done | Add or update tests for top-level `let` and fixed prefix behavior. | `Parser P2` |

## Phase F1: Fix Porting Workarounds Caused By Bugs

Goal: remove example adaptations that were only needed because of parser bugs.

| ID | Status | Task | Commit Label |
| --- | --- | --- | --- |
| F1-01 | Done | Support `mutable` annotations in type-level record fields. | `Fix F1` |
| F1-02 | Done | Fix the lexer/parser misunderstanding of identifiers like `in_channel`; `in` must not be treated as a keyword prefix inside a longer identifier. | `Fix F1` |
| F1-03 | Done | Model Caml Light `#open` directives rather than removing them from examples. | `Fix F1` |
| F1-04 | Pending | Investigate support for reserved keywords as field names, especially `val`; implement only if it is a small localized change. If it requires broad parser architecture changes, mark `Skipped` and document why. | `Fix F1` |
| F1-05 | Pending | Restore affected Caml Light examples toward their original source where the new support allows it. | `Fix F1` |

## Phase W1: Web Demo Major Tasks

Goal: fix the two major web-demo correctness issues first.

| ID | Status | Task | Commit Label |
| --- | --- | --- | --- |
| W1-01 | Pending | Isolate parser state per parse so extension keywords/categories from one parse cannot leak into the next parse unless an explicit keep-state mode is added. | `Web W1` |
| W1-02 | Pending | Refresh extension diagrams and the precedence table clearly after every successful parse that changes or depends on grammar extensions. | `Web W1` |

## Phase W2: Web Demo Minor Tasks

Goal: improve debugging and diagnostics with a small footprint.

| ID | Status | Task | Commit Label |
| --- | --- | --- | --- |
| W2-01 | Pending | Add tabs for syntax tree, tokens, parser trace/debug information, and rule diagrams. Keep parser tracing changes minimal and avoid large parser-code growth. | `Web W2` |
| W2-02 | Pending | Improve errors with source locations and inline highlighting. Prefer a small lexer change that records original token positions and passes that information through where nodes/errors are created. | `Web W2` |

## Phase W3: Web Demo UI Refurbish

Goal: make the demo easier to use and more presentable.

| ID | Status | Task | Commit Label |
| --- | --- | --- | --- |
| W3-01 | Pending | Make output easier to compare and reuse; choose a practical design for raw output, copying, or similar controls. | `Web W3` |
| W3-02 | Pending | Improve prototype-level polish: title, labels, responsive layout, parse status, and general presentation. | `Web W3` |

## Phase W4: Web Demo Limited Provenance

Goal: do only the requested provenance subset.

| ID | Status | Task | Commit Label |
| --- | --- | --- | --- |
| W4-01 | Pending | After selecting an example, show a nearby message naming the original example it was adapted from and linking to the original GitHub repository. | `Web W4` |
| W4-02 | Deferred | Do not implement a built-in browser regression command in this phase. | None |

## Phase D1: Future Work Documentation

Goal: document the remaining future items not assigned to implementation now.

| ID | Status | Task | Commit Label |
| --- | --- | --- | --- |
| D1-01 | Pending | Write a separate Markdown document elaborating the future/reserved items from `Future Or Maybe Items Still Not Implemented`. | `Docs D1` |
| D1-02 | Pending | Include optional `symbol` terminal kind, character-literal terminal kind if not implemented, term/type Pratt-pair unification, and any skipped reserved-keyword field-name work. Do not include `doc/Parsing.md`. | `Docs D1` |

## Phase V: Validation

Run validation as appropriate after each task, and the full suite before final
handoff.

| ID | Status | Task |
| --- | --- | --- |
| V-01 | Done | Run `hkmc2JVM/test` before focused parser/runtime testing in this work session. |
| V-02 | Done | Run focused parser compile tests after parser changes. |
| V-03 | Done | Run focused parser DiffTests after parser/test output changes and commit intentional golden output. |
| V-04 | Done | Run focused web-demo compile tests after web-demo changes. |
| V-05 | Pending | Verify web-demo behavior in a browser when UI behavior changes. |
| V-06 | Pending | Run `hkmc2AllTests/test` before final handoff. |
| V-07 | Pending | Confirm `git status --short` is clean after the final commit. |

## Current Stop Point

Phase F1-03 is complete and ready to commit. Continue with F1-04 next unless a
truly fatal error occurs.
