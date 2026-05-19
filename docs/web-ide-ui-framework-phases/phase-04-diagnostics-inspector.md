# Phase 4: Diagnostics Inspector Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [ ] In progress
- [ ] Browser verified
- [ ] Tests passed
- [ ] Committed

## Goal

Replace the old reserved panel with a prototype-style diagnostics inspector that supports list, tree, and source-card views while preserving the diagnostics entrypoint needed by the current compiler flow.

## Deliverables

- [ ] Add a diagnostics-focused custom element, such as `<diagnostics-inspector>`.
- [ ] Preserve a `setDiagnostics(diagnosticsPerFile)` method.
- [ ] Add severity counts in the inspector header.
- [ ] Add List, Tree, and Source modes with native controls.
- [ ] Render mock diagnostics when no compiler diagnostics are available for framework verification.
- [ ] Render real diagnostics passed through `setDiagnostics` where available.
- [ ] Add rich source-card layout for Source mode.
- [ ] Update the Mock Inventory for diagnostics quick actions and any mock diagnostic data.

## Visible Functionality

- [ ] List mode shows diagnostic rows and selected mode state.
- [ ] Tree mode groups diagnostics by severity and selected mode state.
- [ ] Source mode shows cards with source excerpts and selected mode state.
- [ ] Severity counts match the visible diagnostics dataset.
- [ ] Clicking a diagnostic backed by a real file dispatches `open-file-at-location`.
- [ ] Quick fix, explain, and ignore are stateful mocks or disabled with clear titles.
- [ ] Hide diagnostics collapses the inspector and a visible control reopens it.

## Mock Inventory Impact

- Expected mock entries:
  - Diagnostics quick actions
- Add entries for mock diagnostic datasets if they remain visible after real diagnostics are wired.

## Verification

- [ ] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [ ] Run `git diff --check`.
- [ ] Run `git status --short` and confirm only intended files changed.
- [ ] Browser-check List, Tree, and Source mode switching.
- [ ] Browser-check severity counts against visible items.
- [ ] Browser-check diagnostic click-to-open behavior for real diagnostics.
- [ ] Browser-check quick-action controls against the functionality standard.
- [ ] Browser-check Compile still updates diagnostics.

## Completion Notes

- Commit:
- Browser notes:
- Test output:
