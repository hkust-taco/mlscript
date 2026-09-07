# Parser Project Follow-Up Review

Date: 2026-04-25

## Scope

This report reviews the documentation produced during the parser-alignment
round and the Caml Light examples plus web-demo round. The goal is to collect
unfinished future/maybe items, record the concrete porting issues and
workarounds, and identify missing core functionality in the web demo.

Documents reviewed:

- `doc/generalized-pratt-parser-notes.md`
- `doc/inconsistency-resolution.md`
- `doc/parser-alignment-track-board.md`
- `doc/parser-terminal-kinds-proposal.md`
- `doc/caml-light-prefix-operators.md`
- `doc/caml-light-parser-demo-todo.md`
- `doc/caml-light-parser-demo/source-discovery.md`
- `doc/caml-light-parser-demo/example-01.md` through `example-10.md`
- `doc/caml-light-parser-demo/extensible-example-01.md`
- `doc/caml-light-parser-demo/extensible-example-02.md`
- `doc/caml-light-parser-demo/web-demo-error-dialog.md`
- `doc/caml-light-parser-demo/web-demo-example-imports.md`
- `doc/Parsing.md`

## Future Or Maybe Items Still Not Implemented

Several items that were initially described as future work have since been
implemented. The remaining unimplemented items are below.

| Item | Source | Current State | Suggested Priority |
| --- | --- | --- | --- |
| Dedicated `pattern` syntax kind with dedicated pattern rules | `parser-alignment-track-board.md` PA-12; `inconsistency-resolution.md`; example 02/03/07/08 memos | Still deferred. `Rules.mls` has helper categories such as `pattern-list`, but they parse patterns through `term`, so pattern aliases and alternatives were avoided in examples. | High |
| Proper pattern alias support, such as `p as x` | Example 02, 03, 07 memos | Not implemented as parser support. Ports rewrote aliases by reconstructing values in branch bodies. This is part of the dedicated-pattern work. | High |
| Pattern alternatives inside one branch, such as a space-character case sharing a branch with a tab-character case | Example 08 memo | Not implemented. The port split one branch into two branches. This is also part of dedicated-pattern work. | High |
| Top-level `let` cleanup | `inconsistency-resolution.md`; `generalized-pratt-parser-notes.md` | Still manual. `Parser.mls` parses a `let` term and then repairs `Tree.LetIn(bindings, Tree.Empty)` into a top-level `Tree.Define`. | Medium |
| Conservative fixed prefix-operator rule for Caml Light `-`, `-.`, and `!` | `caml-light-prefix-operators.md` | Not implemented as a narrow rule. Current parser behavior is broader: symbolic operators with known precedence can be parsed in prefix position, while infix excludes `!` and `~`. The note says no immediate change was needed, but the stricter Caml Light rule remains a possible cleanup. | Low |
| Optional `symbol` terminal kind | `parser-terminal-kinds-proposal.md` | Not implemented. The proposal said `symbol` was only possible if `Choice.Infix` needed it. `Choice.Infix` was implemented without adding this terminal, so this remains optional rather than blocked work. | Low |
| Character-literal terminal kind for extensions | Implied by example 08's character-literal parser fix, not explicitly in the terminal proposal | Not implemented as a closed syntax kind. The parser can tokenize and parse character literals as ordinary term literals, but extensions cannot currently request `["character-literal", "x"]`. | Low to Medium |
| Reconsider unification of term/type Pratt pairs | `inconsistency-resolution.md` | Not implemented. The alignment round intentionally split `expr`/`exprCont` and `typeExpr`/`typeExprCont`; shared helper code now exists, but a full unification pass was not done and may conflict with the paper-facing structure. | Low |
| Advanced indentation continuation rules | `doc/Parsing.md` | Still marked `[TODO actually implement]`. This appears older and outside the two parser-demo rounds, but it is still parser documentation that advertises unimplemented syntax. | Medium, if still relevant |

Items that are no longer outstanding:

- `Choice.Infix` was implemented.
- Paper-style `#keyword` and `#extend` syntax was implemented.
- Literal terminal kinds from the proposal were implemented for `literal`,
  `string-literal`, `integer-literal`, `decimal-literal`, and
  `boolean-literal`.
- AST names were aligned to `Tree.Reference` and `Tree.Application`.
- Token names were split into `Token.Reference` and `Token.Symbol`.
- The web demo now has a precedence table.
- The web demo now shows visible errors through an HTML `dialog`.

## Example Porting Issues And Workarounds

### Parser Fixes Added During Porting

| Area | Examples | Fix |
| --- | --- | --- |
| Exception handling | Fibonacci, Pascal values, Word count | Added `try ... with ...` parsing and `Tree.Try`. |
| Equality versus binding `=` | Integer sets | Added term-level `=` parsing, a `binding` parse kind, and a stop marker so binding left-hand sides do not consume the binding `=` as equality. |
| Alphabetic Caml Light infix operators | Bit buffer, also corrected Sieve | Added keyword-level infix parsing for `mod`, `land`, `lor`, `lxor`, `lsl`, `lsr`, and `asr`. |
| Character literals | Word count | Added backtick character literal tokenization, such as `` `\n` ``. |
| `for` headers | Word count | Parsed loop variables with binding-stop behavior, matching let-binding left-hand sides. |
| Prefix dereference | Word count, Bubble sort | Split prefix-only symbolic operators such as `!` away from generic symbolic infix parsing so `!x` parses as prefix application. |

### Workarounds In Adapted Examples

| Issue | Examples | Workaround | Residual Debt |
| --- | --- | --- | --- |
| Pattern aliases using `as` | Sieve, Integer sets, Priority queue | Removed the alias and reconstructed the value in the branch body. | Needs dedicated pattern syntax. |
| Pattern alternatives in one branch | Word count | Split the original space-or-tab character branch into two separate branches. | Needs dedicated pattern syntax. |
| French names and accented source text | Integer sets, Pascal values, Picomach constants, Bit buffer, Priority queue | Translated identifiers and messages to English and ASCII. | Probably acceptable for tests, but the parser's real Caml Light coverage remains narrower than the original source set. |
| `#open` bootstrap directives | Pascal values, Bubble sort, Insertion sort | Removed `#open` lines and kept the core file body. | The parser still does not model Caml Light `#open` as a source-level directive. |
| Multi-file dependency on external declarations | Priority queue | Added a local `exception Empty_queue` because the original relied on another file. | Full multi-file example support is not represented in this parser test style. |
| Type-level `mutable` record fields | Bit buffer | Omitted `mutable` annotations from the record type. The expression-level field mutation was kept. | Parser lacks a dedicated mutability node for type declarations. |
| Reserved-looking field name `val` | Bit buffer | Renamed `val` to `value`. | Could be revisited if exact Caml Light field-name compatibility matters. |
| Identifier containing keyword prefix | Word count | Renamed `in_channel` to `input_channel` to avoid interaction with the `in` keyword. | Lexer/keyword boundary behavior may need a focused test if exact Caml Light identifiers are required. |
| Operator spacing in compact original examples | Bubble sort, Insertion sort | Added spaces around arithmetic operators. | No parser workaround was required, but the tests are less exact than the originals. |
| DiffTest block splitting by blank lines | Sieve and other multiline examples | Removed blank lines inside parsed snippets so the whole string stays in one test block. | This is a test-harness formatting constraint, not a parser issue. |

No selected example hit the remembered lexer stack-overflow problem, so no file
had to be split for stack safety. Some candidate examples from source discovery
were not selected because they appeared to require larger unsupported surfaces,
including stream parser syntax, `#open`, character literals before that fix, or
accented identifiers.

## Web Demo Critique

The web demo is now useful as a smoke test: examples load, parsing errors appear
in a visible dialog, successful parses render collapsible syntax trees, and the
page includes syntax diagrams plus a precedence table. However, it is still
missing several pieces that are core for a paper/demo artifact.

### 1. Parser State Is Not Isolated Per Parse

The extensible parser mutates global keyword and syntax-kind registries. The
demo does not reset parser extension state before each parse, so parsing one
extensible example can affect later parses in the same browser session. The
current examples avoid conflicting names, but a user can create conflicts easily.

Recommended next step: add a parser-session reset or snapshot/restore mechanism
around each parse. The demo should make a fresh base parser state for each parse
unless it intentionally offers an interactive "keep extensions" mode.

### 2. Errors Lack Source Locations And Inline Highlighting

The dialog shows the JavaScript error message and stack trace. Parse error trees
are detected by looking for the warning marker in `Tree.summary()`. That is a
useful safety net, but it is not a structured diagnostic interface.

Recommended next step: return structured parse diagnostics with token location,
line, column, expected form, and offending token. The editor should highlight
the failing range and the dialog should show the source location first, with the
JavaScript stack folded below it.

### 3. No Token Or Trace View

When a parse fails, the demo does not expose the lexer output, parser trace, or
rule decisions. This makes it hard to diagnose the exact class of parser bug
from the browser.

Recommended next step: add tabs for Syntax Tree, Tokens, Parser Trace, and Rule
Diagrams. The parser already has tracing infrastructure; the demo should surface
it behind an explicit debug toggle.

### 4. Extension Diagrams Do Not Clearly Refresh With Every Parse

The page renders base diagrams on load and refreshes diagrams for `#diagram`.
The imported extensible examples do not include `#diagram`, so users can parse
them successfully without seeing the newly added categories reflected in the
diagram area.

Recommended next step: refresh diagrams and the precedence table after any
successful parse that processes extension directives, or add a visible "Render
current grammar" command.

### 5. Examples Are Detached From Their Provenance

The selector shows only display names. It does not link to the per-example memo,
show the original Caml Light source, or explain adaptations. This weakens the
demo as evidence that the parser handles real Caml Light examples.

Recommended next step: store metadata with each example: original path, memo
path, adaptation summary, and whether parser fixes were required. Add an
example-details panel with original/adapted toggle or diff.

### 6. Output Is Hard To Compare Or Reuse

The syntax tree is collapsible but there is no raw text output panel, copy
button, download button, or stable serialization mode. This makes regression
inspection less convenient than the DiffTest output.

Recommended next step: add a raw tree tab and copy/download controls. Use the
same string form as the tests so browser output and golden output can be
compared directly.

### 7. No Built-In Browser Regression Command

The final verification used Playwright manually, but there is no checked-in
browser test command that opens the demo and parses every example.

Recommended next step: add a script or documented SBT/browser-test target that
serves `mlscript-compile`, opens the demo, parses every example, asserts no
dialog opens, and checks non-empty output.

### 8. Demo Polish Still Looks Prototype-Level

The page title is `Document`, controls are minimal, and the two-pane layout is
mostly desktop-only. This is acceptable for engineering validation but weak for
a public paper demo.

Recommended next step: give the page a real title, add clear labels, make the
layout responsive, preserve editor content when switching examples, and add
explicit parse status such as "Parsed N top-level items".

## Recommended Next Order

1. Implement the dedicated `pattern` syntax kind and cover `as` aliases plus
   pattern alternatives. This pays down the most visible example-porting debt.
2. Add parser state reset/snapshot support for the web demo so extension
   examples are isolated and reproducible.
3. Replace summary-marker error detection with structured diagnostics and
   source-location highlighting.
4. Add example provenance metadata and original/adapted views to the web demo.
5. Add a repeatable browser regression command for all demo examples.
6. Revisit lower-priority cleanup: fixed Caml Light prefix forms, optional
   `symbol` or `character-literal` terminal kinds, and top-level `let`
   cleanup.
