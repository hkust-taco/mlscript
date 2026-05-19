# Phase 4: Diagnostics Inspector Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [x] In progress
- [x] Browser verified
- [x] Tests passed
- [x] Committed

## Goal

Replace the old reserved panel with a prototype-style diagnostics inspector that supports list, tree, and source-card views while preserving the diagnostics entrypoint needed by the current compiler flow.

## Deliverables

- [x] Add a diagnostics-focused custom element, such as `<diagnostics-inspector>`.
- [x] Preserve a `setDiagnostics(diagnosticsPerFile)` method.
- [x] Add severity counts in the inspector header.
- [x] Add List, Tree, and Source modes with native controls.
- [x] Render mock diagnostics when no compiler diagnostics are available for framework verification.
- [x] Render real diagnostics passed through `setDiagnostics` where available.
- [x] Add rich source-card layout for Source mode.
- [x] Update the Mock Inventory for diagnostics quick actions and any mock diagnostic data.

## Visible Functionality

- [x] List mode shows diagnostic rows and selected mode state.
- [x] Tree mode groups diagnostics by severity and selected mode state.
- [x] Source mode shows cards with source excerpts and selected mode state.
- [x] Severity counts match the visible diagnostics dataset.
- [x] Clicking a diagnostic backed by a real file dispatches `open-file-at-location`.
- [x] Quick fix, explain, and ignore are stateful mocks or disabled with clear titles.
- [x] Hide diagnostics collapses the inspector and a visible control reopens it.

## Mock Inventory Impact

- Expected mock entries:
  - Diagnostics sample dataset
  - Diagnostics quick actions
- Added the sample dataset to the parent Mock Inventory because it is visible before the first compiler diagnostics update.

## Verification

- [x] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [x] Run `git diff --check`.
- [x] Run `git status --short` and confirm only intended files changed.
- [x] Browser-check List, Tree, and Source mode switching.
- [x] Browser-check severity counts against visible items.
- [x] Browser-check diagnostic click-to-open behavior for real diagnostics.
- [x] Browser-check quick-action controls against the functionality standard.
- [x] Browser-check Compile still updates diagnostics.

## Completion Notes

- Commit: this phase commit.
- Browser notes: Playwright CLI verified the inspector exists, sample counts are 1 error / 1 warning / 1 internal / 0 info, Tree and Source modes switch selected state, Source mode renders three cards, Open dispatches `/main.mls:5`, Explain shows feedback, Ignore updates counts, the status-bar Diagnostics control hides and restores the inspector, and Compile swaps the inspector to compiler diagnostics with the success empty state. Screenshot: `docs/web-ide-ui-framework-screenshots/phase-04/diagnostics-inspector-1920x1080.png`.
- Test output: `hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide` passed 24 tests.
