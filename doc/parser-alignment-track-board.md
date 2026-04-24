# Parser Alignment Track Board

Created: 2026-04-24

This board tracks the work needed to align the parsing implementation with the
paper after the responses in `doc/inconsistency-resolution.md`.

Sources:

- `doc/generalized-pratt-parser-notes.md`
- `doc/inconsistency-resolution.md`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing-web-demo`
- `/Users/chengluyu/Developer/generalized-pratt-parsing/paper.tex`

## Ordering Strategy

The order below is based on three constraints:

1. Fix concrete low-risk correctness issues first.
2. Stabilize the core rule representation before changing extension syntax or
   adding more rule constructors.
3. Keep independent presentation and paper-polish work for the end.

Before starting implementation work, verify that `HEAD` still matches the latest
`origin/hkmc2`. The latest check for this board was clean:
`HEAD == origin/hkmc2 == 8e1a1efa265ff563a1f665b1bf3cb30bdb5391c8`.

## Status Legend

- `Ready`: prepared to start.
- `Blocked`: needs an earlier item or a design decision.
- `Deferred`: intentionally left for the final wrap-up phase or later work.
- `Done`: implemented and validated.

## Validation Loop

For any code-changing task:

1. Run `hkmc2JVM/test` in an SBT shell before focused app or diff tests.
2. Run focused parser app tests, usually:
   `hkmc2AppsTests/testOnly hkmc2.AppsCompileTestRunner -- -z parsing/`
3. Run focused parser diff tests when generated output can change, usually:
   `hkmc2AppsTests/testOnly hkmc2.AppsDiffTestRunner -- -z mlscript/apps/parsing/`
4. Review `git status --short` and `git diff`.
5. Keep intentional golden-output rewrites and revert only unintended generated
   test output.
6. Before finishing a larger phase, run `hkmc2AllTests/test`.

## Ordered Board

| Order | ID | Status | Priority | Difficulty | Code Impact | Item |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | PA-01 | Done | P0 | Low | Low | Audit registered keywords and remove `class` plus any other truly unused registered keywords. |
| 2 | PA-02 | Done | P1 | Medium | Medium | Collapse `Choice.Ref` from `outerPrec`/`innerPrec` to one optional binding-power field. |
| 3 | PA-03 | Done | P1 | Medium | Medium | Replace `Choice.Siding` with standalone helper-generated rules and remove the `Siding` constructor from the rule model. |
| 4 | PA-04 | Done | P1 | Medium | Medium | Add an explicit `afterRef` helper and route continuation loops through it. |
| 5 | PA-05 | Done | P1 | Medium | Medium | Split the parameterized `expr`/`exprCont` pair into explicit `expr`/`exprCont` and `typeExpr`/`typeExprCont` pairs. |
| 6 | PA-06 | Done | P1 | High | High | Add the paper's `Infix` choice so symbolic infix operators are represented in rules instead of hard-coded in `exprCont`. |
| 7 | PA-07 | Done | P2 | Low | Documentation | Write a proposal for built-in terminal syntax kinds beyond `ident` and `typevar`, especially `literal` and `string-literal`. |
| 8 | PA-08 | Done | P1 | High | High | Align dynamic extension directives with the paper's `#keyword` and `#extend` syntax and replacement-expression scheme. |
| 9 | PA-09 | Ready | P2 | Medium | Investigation | Investigate whether Caml Light prefix operators have precedence; do not implement prefix precedence until this is resolved. |
| 10 | PA-10 | Deferred | P2 | Medium | Low | Add a generated precedence-table renderer and wire it into the web demo. |
| 11 | PA-11 | Deferred | P3 | High | High | Simplify AST names and shapes to match the paper, including `Tree.Reference`, `Tree.Application`, and token naming cleanup. |
| 12 | PA-12 | Deferred | P3 | High | High | Future work: introduce `pattern` as a separate syntax kind with dedicated rules. |

## Task Cards

### PA-01: Keyword Registry Audit

Goal: remove accidental or unused registered keywords.

Implementation sketch:

- Remove `Keywords._class`; it is explicitly called out as an error.
- Search all parser app and parser diff-test sources for registered keywords
  that are never used in rules, parser logic, directives, examples, or tests.
- Remove only keywords that are truly unused. Keep delimiter keywords that are
  used indirectly by parser control flow, such as `;;`, unless tests show they
  are dead.
- Update parser app output and diff-test golden comments if parsing changes.

Acceptance criteria:

- `class` is no longer treated as a reserved parser keyword.
- No rule references a deleted keyword.
- Parser app tests pass with reviewed golden output.

Likely files:

- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Keywords.mls`
- `hkmc2/shared/src/test/mlscript/apps/parsing/*.mls`

### PA-02: Single Binding Power for `Ref`

Goal: align `Choice.Ref` with the paper's single optional binding-power field.

Implementation sketch:

- Replace `Ref(kind, process, outerPrec, innerPrec, rest)` with
  `Ref(kind, process, bp, rest)`.
- Update `Choice.reference` to accept `bp` while temporarily accepting
  `outerPrec` as a compatibility alias during migration if useful.
- Update `Parser.mls`, `ParseRule.mls`, `ParseRuleVisualizer.mls`,
  `Extension.mls`, and rule definitions that currently pass `outerPrec`.
- Preserve the current behavior by treating the old `outerPrec` as the new entry
  binding power. Remove uses of `innerPrec`.

Acceptance criteria:

- There is no `innerPrec` field or parser branch.
- Remaining binding-power checks read like the paper's `bp > currentBp` test.
- Application precedence still works for terms and types.

Likely files:

- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/ParseRule.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Parser.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Rules.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Extension.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/ParseRuleVisualizer.mls`

### PA-03: Remove `Siding` from the Core Rule Model

Goal: make siding a helper that expands into ordinary `Keyword`, `Ref`, and
`End` choices, because the paper does not treat siding as a core choice.

Implementation sketch:

- Design helper functions that generate equivalent rules for the current
  optional and alternative siding use cases.
- Replace `Choice.optional` and `Choice.siding` call sites in `Rules.mls`.
- Remove the `Choice.Siding` data constructor and all special handling from
  `map`, `andThen`, `endChoice`, `keywordChoices`, `refChoice`, and `display`.
- Keep diagram output structurally equivalent where possible.

Acceptance criteria:

- No `Siding` constructor remains in `ParseRule.mls`.
- Existing optional fragments still parse, including `let rec`, optional leading
  `|` in matching, and `for ... to/downto ...`.
- Existing parser rule displays and diagrams remain understandable, even if
  exact grouping changes.

Likely files:

- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/ParseRule.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Rules.mls`
- Parser display and visualizer tests under `hkmc2/shared/src/test/mlscript/apps/parsing`

### PA-04: Expose and Use `afterRef`

Goal: make continuation extraction explicit and consistent with the paper.

Implementation sketch:

- Add `ParseRule.afterRef`, derived from the first applicable `Ref` choice.
- Return a structure close to the paper: referenced kind plus a continuation
  rule that produces an optional transformer.
- Rewrite the self-reference loop in `parseKind` to use `afterRef`.
- Rewrite `exprCont` and later `typeExprCont` to use the same continuation
  concept instead of manually unpacking `refChoice`.

Acceptance criteria:

- The name `afterRef` exists in the implementation.
- Left-recursive extension behavior still works.
- `ParseRule.refChoice` remains only for lower-level inspection if still needed.

Likely files:

- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/ParseRule.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Parser.mls`

### PA-05: Separate Term and Type Pratt Pairs

Goal: match the paper's explicit `expr`/`exprCont` and
`typeExpr`/`typeExprCont` design.

Implementation sketch:

- Replace `termOptions` and `typeOptions` dispatch with dedicated functions.
- Keep shared local helpers for common token, keyword, and continuation behavior
  only where doing so does not hide the paper-level structure.
- Ensure type expressions continue to reject symbolic identifiers and term-only
  literals if that remains intended.

Acceptance criteria:

- `parseKind("term", bp)` calls `expr(bp)`.
- `parseKind("type", bp)` calls `typeExpr(bp)`.
- The code has separate continuation functions for terms and types.

Likely files:

- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Parser.mls`

### PA-06: Add `Infix` Choice

Goal: make symbolic infix operators part of the rule representation.

Implementation sketch:

- Add a new choice constructor, likely `Infix(op, rhsKind, process)`.
- Extend rule mapping, display, visualization, and parser interpretation.
- Move the `Keywords.opPrecOpt` branch out of hard-coded `exprCont` logic and
  into a rule choice under the term rule.
- Model cross-kind infix where appropriate, especially term `:` type.

Acceptance criteria:

- Symbolic infix parsing is driven by rules.
- `exprCont` no longer contains a special branch that directly calls
  `Keywords.opPrecOpt` for non-keyword symbolic identifiers.
- Existing symbolic operator tests keep their behavior.

Likely files:

- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/ParseRule.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Parser.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Rules.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/ParseRuleVisualizer.mls`

### PA-07: Built-In Terminal Kind Proposal

Goal: decide how to handle terminal kinds before changing the extension syntax.

Implementation sketch:

- Document the current limitation: `parseKind` only recognizes `ident` and
  `typevar`, while literals are parsed through term/type atom logic.
- Propose a minimal set of built-ins: `literal`, `string-literal`,
  `integer-literal`, possibly `symbol` if `Infix` needs it.
- Specify whether these are closed syntax kinds and how they appear in diagrams.
- Decide whether this proposal should become code in PA-08 or remain a design
  note for a later implementation pass.

Acceptance criteria:

- A short proposal exists in this board or a linked document.
- PA-08 has a clear decision for references like `["string-literal", "f"]`.

Likely files:

- `doc/parser-terminal-kinds-proposal.md` or this board
- Later: `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Parser.mls`

### PA-08: Paper-Compatible Dynamic Extension Syntax

Goal: replace the current `#newKeyword`, `#newCategory`, and `#extendCategory`
surface with the paper's directive shape.

Implementation sketch:

- Add `#keyword "name" lbp rbp`.
- Add `#extend [targetKind, sequence, replacementExpression]`.
- Parse labeled fragments such as `["term", "x"]` and
  `["string-literal", "f"]`.
- Replace the current function-identifier application scheme with the paper's
  replacement-expression scheme.
- Update web-demo examples and parser diff tests.

Acceptance criteria:

- Paper-style examples parse.
- Old directive tests are either migrated or intentionally retained only as
  compatibility tests if we choose a transition period.
- `Extension.mls` no longer centers on `parseChoiceTree` returning a function
  identifier application.
- Closed literal terminal kinds are available to dynamic extensions:
  `literal`, `string-literal`, `integer-literal`, `decimal-literal`, and
  `boolean-literal`.
- `#extend` creates a target syntax kind when the target is not closed and does
  not already exist, so a separate `#newCategory` directive is unnecessary.

Likely files:

- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Extension.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Parser.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing-web-demo/Examples.mls`
- `hkmc2/shared/src/test/mlscript/apps/parsing/DirectiveTest.mls`
- `hkmc2/shared/src/test/mlscript/apps/parsing/LeftRecursion.mls`
- `hkmc2/shared/src/test/mlscript/apps/parsing-web-demo/ExamplesTest.mls`

### PA-09: Prefix Operator Precedence Investigation

Goal: check whether Caml Light has prefix precedence before implementing any
prefix-precedence support.

Implementation sketch:

- Review Caml Light syntax references and existing parser tests.
- Determine whether prefix operators should be parsed as precedence-bearing
  symbolic operators or as ordinary identifiers/applications.
- Record the conclusion before any code work.

Acceptance criteria:

- A dated investigation note states whether implementation is needed.
- No prefix implementation is started before this note.

Likely files:

- A future note under `doc/`
- Existing parser tests for symbolic operators

### PA-10: Precedence Table Renderer

Goal: generate a precedence table alongside railroad diagrams.

Implementation sketch:

- Extract keyword and operator precedence data from `Keywords.mls` and rule
  choices.
- Render an HTML table in the web demo near the syntax diagrams.
- Include dynamically added keywords and, after PA-06, `Infix` choices.

Acceptance criteria:

- The web demo displays railroad diagrams and a precedence table.
- Dynamic keyword additions appear in the table after parsing directives.

Likely files:

- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Keywords.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing-web-demo/main.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing-web-demo/index.html`

### PA-11: AST and Naming Simplification

Goal: align implementation naming and AST shape with the paper during final
wrap-up.

Implementation sketch:

- Rename or wrap `Tree.Ident` and `Tree.App` to match paper terminology such as
  `Tree.Reference` and `Tree.Application`.
- Decide whether token constructors should distinguish symbols from identifiers
  or keep the current `Token.Identifier(name, symbolic)` shape.
- Keep this late because it causes broad snapshot churn and can obscure parser
  behavior changes.

Acceptance criteria:

- Paper examples and source names agree where practical.
- Golden output changes are reviewed as intentional naming churn.

Likely files:

- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Tree.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Token.mls`
- Parser tests and web-demo rendering helpers

### PA-12: Separate Pattern Syntax Kind

Goal: record the future direction for patterns without mixing it into the
current parser-alignment pass.

Implementation sketch:

- Introduce `pattern` as its own syntax kind later.
- Migrate matching and binding rules away from term parsing when that work is
  explicitly prioritized.

Acceptance criteria:

- No current task rewrites patterns unless required by another parser change.
- Future pattern work has a clear tracker item.

Likely files:

- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Rules.mls`
- `hkmc2/shared/src/test/mlscript-compile/apps/parsing/Parser.mls`

## Next Fix

Continue with PA-09. It is an investigation task and should settle the prefix
operator question before any remaining presentation or naming cleanup work.
