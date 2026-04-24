# Caml Light Parser Demo Todo

Created: 2026-04-25

This file is the working checklist for the next parser-demo phase. Do not start
implementation until the user confirms that this plan is acceptable.

## Ground Rules

- Keep this file updated whenever progress, scope, blockers, or ordering changes.
- Do not stop this work until all tasks are completed unless a truly fatal
  error blocks further progress.
- If a truly fatal error occurs, write a separate Markdown file under
  `doc/caml-light-parser-demo/` explaining exactly why work stopped, with full
  details of the situation and attempted recovery.
- Use the HKMC2 DiffTests workflow for `.mls` tests: run focused tests, review
  rewritten `//│` golden output, and commit intentional generated output.
- Keep an SBT shell open when doing test work.
- Before focused parser or runtime tests, make sure `hkmc2JVM/test` has been run
  in the current work session.
- Make a commit after each finished example or web-demo task.
- Parser fixes must be general parser fixes, not special cases for one example.
- If a Caml Light example is too difficult to adapt quickly, skip it, leave a
  commented note in the test/memo, and move on.
- Put per-example and per-web-task notes under `doc/caml-light-parser-demo/`.

## Status Legend

- `Pending`: not started.
- `In Progress`: actively being worked on.
- `Blocked`: waiting on a decision or external issue.
- `Done`: implemented, tested, documented, and committed.
- `Skipped`: considered but intentionally not ported, with memo explaining why.

## Phase 0: Approval Gate

| ID | Status | Task |
| --- | --- | --- |
| P0-01 | Done | Write this consolidated todo file. |
| P0-02 | Done | Show this file to the user and wait for explicit approval before continuing. |

## Phase 1: Source Discovery

| ID | Status | Task |
| --- | --- | --- |
| P1-01 | Pending | Visit the official Caml Light site at `https://caml.inria.fr/caml-light/`. |
| P1-02 | Pending | Find the official Caml Light GitHub repository from that site. |
| P1-03 | Pending | Clone the repository into a temporary folder outside this repo. |
| P1-04 | Pending | Inventory candidate example files, including multi-file examples and French-named examples. |
| P1-05 | Pending | Choose at least 10 examples that are meaningful and likely portable. |

## Phase 2: Port 10 Caml Light Examples

Target test style: follow
`hkmc2/shared/src/test/mlscript/apps/parsing/CamlLightTest.mls`. Each accepted
example must parse successfully and print the syntax tree in golden output.

For each example:

1. Record the original source in a per-example Markdown memo.
2. Record the adapted source in the same memo.
3. Translate French names/comments where appropriate.
4. If the original is multi-file, pick the core file rather than bootstrap code.
5. If lexer stack overflow occurs, split the adapted source into smaller parsed
   pieces; otherwise keep the example whole.
6. If parsing fails, diagnose and fix the parser generally.
7. Add or update the parser DiffTest with syntax-tree output.
8. Run focused compile/DiffTests and review generated output.
9. Commit with progress in the title, for example `Port Caml Light example 1/10`.

| Example | Status | Memo | Commit Requirement |
| --- | --- | --- | --- |
| 1/10 | Pending | `doc/caml-light-parser-demo/example-01.md` | Commit after done. |
| 2/10 | Pending | `doc/caml-light-parser-demo/example-02.md` | Commit after done. |
| 3/10 | Pending | `doc/caml-light-parser-demo/example-03.md` | Commit after done. |
| 4/10 | Pending | `doc/caml-light-parser-demo/example-04.md` | Commit after done. |
| 5/10 | Pending | `doc/caml-light-parser-demo/example-05.md` | Commit after done. |
| 6/10 | Pending | `doc/caml-light-parser-demo/example-06.md` | Commit after done. |
| 7/10 | Pending | `doc/caml-light-parser-demo/example-07.md` | Commit after done. |
| 8/10 | Pending | `doc/caml-light-parser-demo/example-08.md` | Commit after done. |
| 9/10 | Pending | `doc/caml-light-parser-demo/example-09.md` | Commit after done. |
| 10/10 | Pending | `doc/caml-light-parser-demo/example-10.md` | Commit after done. |

## Phase 3: Extensible Parser Examples

Add two concise, meaningful examples that exercise the paper-style extensible
parser feature, such as `#keyword` plus `#extend`. Each one must parse
successfully, print syntax-tree output, have a memo, and be committed separately.

| Example | Status | Memo | Commit Requirement |
| --- | --- | --- | --- |
| Extensible 1/2 | Pending | `doc/caml-light-parser-demo/extensible-example-01.md` | Commit after done. |
| Extensible 2/2 | Pending | `doc/caml-light-parser-demo/extensible-example-02.md` | Commit after done. |

## Phase 4: Web Demo Error Reporting

Goal: the web demo must not silently hide errors. Errors should be shown in an
eye-catching HTML `dialog` element with the error message and a pretty-printed
stack trace.

| ID | Status | Task | Memo | Commit Requirement |
| --- | --- | --- | --- | --- |
| W1-01 | Pending | Reproduce current console failures on built-in examples. | `doc/caml-light-parser-demo/web-demo-error-dialog.md` | Commit after task done. |
| W1-02 | Pending | Add visible dialog-based error reporting with stack trace formatting. | Same memo | Same commit. |
| W1-03 | Pending | Verify the dialog appears for failures and does not obscure successful output. | Same memo | Same commit. |

## Phase 5: Web Demo Example Integration

Goal: import every newly added Caml Light and extensible parser example into the
web demo, and verify that each can be parsed correctly there.

| ID | Status | Task | Memo | Commit Requirement |
| --- | --- | --- | --- | --- |
| W2-01 | Pending | Add the 10 Caml Light examples to the web-demo examples list. | `doc/caml-light-parser-demo/web-demo-example-imports.md` | Commit after task done. |
| W2-02 | Pending | Add the 2 extensible parser examples to the web-demo examples list. | Same memo | Same commit. |
| W2-03 | Pending | Test the web demo in a browser and confirm all imported examples parse. | Same memo | Same commit. |

## Phase 6: Final Validation

| ID | Status | Task |
| --- | --- | --- |
| V-01 | Pending | Run focused parser compile tests. |
| V-02 | Pending | Run focused parser and web-demo DiffTests. |
| V-03 | Pending | Run browser verification for the web demo. |
| V-04 | Pending | Run `hkmc2AllTests/test`. |
| V-05 | Pending | Confirm `git status --short` is clean after the final commit. |

## Current Stop Point

Stop after showing this file. Continue only after the user explicitly approves.
