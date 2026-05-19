# Phase 7: Native Dialogs Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [ ] In progress
- [ ] Browser verified
- [ ] Tests passed
- [ ] Committed

## Goal

Add native dialog-based command surfaces for command palette and sharing, using `<dialog>` and MLscript custom elements without introducing a JavaScript framework.

## Deliverables

- [ ] Add a `<command-palette-dialog>` custom element backed by `<dialog>`.
- [ ] Add a command palette button in the titlebar.
- [ ] Add keyboard shortcut support for opening the command palette.
- [ ] Add command search/filtering.
- [ ] Add commands for current real actions where possible.
- [ ] Add mocked or disabled future commands only when documented in the Mock Inventory.
- [ ] Add a `<share-dialog>` custom element backed by `<dialog>`.
- [ ] Add copy-link behavior for the share dialog using mock URL text unless real sharing exists.

## Visible Functionality

- [ ] Command palette opens from the titlebar button.
- [ ] Command palette opens from the keyboard shortcut.
- [ ] First useful field is focused when the palette opens.
- [ ] Search input filters command rows.
- [ ] Escape closes the palette through native dialog behavior.
- [ ] Real commands dispatch real events.
- [ ] Mock commands visibly change UI state or are disabled with clear titles.
- [ ] Share dialog opens and closes.
- [ ] Share copy action copies mock URL text or shows a visible failure.

## Mock Inventory Impact

- Expected mock entries:
  - Command palette future commands
  - Share dialog
- Update the parent plan for every command that is visible but not backed by real functionality.

## Verification

- [ ] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [ ] Run `git diff --check`.
- [ ] Run `git status --short` and confirm only intended files changed.
- [ ] Browser-check command palette button and shortcut.
- [ ] Browser-check search filtering and focus behavior.
- [ ] Browser-check Escape and close behavior.
- [ ] Browser-check each visible command against the functionality standard.
- [ ] Browser-check share dialog open, close, and copy behavior.

## Completion Notes

- Commit:
- Browser notes:
- Test output:
