# Phase 7: Native Dialogs Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [x] In progress
- [x] Browser verified
- [x] Tests passed
- [x] Committed

## Goal

Add native dialog-based command surfaces for command palette and sharing, using `<dialog>` and MLscript custom elements without introducing a JavaScript framework.

## Deliverables

- [x] Add a `<command-palette-dialog>` custom element backed by `<dialog>`.
- [x] Add a command palette button in the titlebar.
- [x] Add keyboard shortcut support for opening the command palette.
- [x] Add command search/filtering.
- [x] Add commands for current real actions where possible.
- [x] Add mocked or disabled future commands only when documented in the Mock Inventory.
- [x] Add a `<share-dialog>` custom element backed by `<dialog>`.
- [x] Add ZIP download behavior for the share dialog.

## Visible Functionality

- [x] Command palette opens from the titlebar button.
- [x] Command palette opens from the keyboard shortcut.
- [x] First useful field is focused when the palette opens.
- [x] Search input filters command rows.
- [x] Escape closes the palette through native dialog behavior.
- [x] Real commands dispatch real events.
- [x] Mock commands visibly change UI state or are disabled with clear titles.
- [x] Share dialog opens and closes.
- [x] Share dialog downloads the workspace as a ZIP.

## Mock Inventory Impact

- Expected mock entries:
  - Command palette future commands
- Update the parent plan for every command that is visible but not backed by real functionality.

## Verification

- [x] Run `timeout 300s sbt --client "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [x] Run `git diff --check`.
- [x] Run `git status --short` and confirm only intended files changed.
- [x] Browser-check command palette button and shortcut.
- [x] Browser-check search filtering and focus behavior.
- [x] Browser-check Escape and close behavior.
- [x] Browser-check each visible command against the functionality standard.
- [x] Browser-check share dialog open, close, and copy behavior.

## Completion Notes

- Commit: this phase commit.
- Browser notes: Playwright verified command palette opening from toolbar button and Cmd/Ctrl+K, search filtering, delayed focus on the search input, native Escape close behavior, real compile command dispatch, mock wasm target selection, disabled theme command title, share dialog open/close, share focus, and copy feedback. Console check reported 0 errors and 0 warnings.
- Test output: Focused web-ide package test passed with 27 tests. Screenshot captured at `docs/web-ide-ui-framework-screenshots/phase-07/native-dialogs-1920x1080.png`.
