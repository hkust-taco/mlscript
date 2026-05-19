# Phase 6: Editor Workbench Chrome Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [ ] In progress
- [ ] Browser verified
- [ ] Tests passed
- [ ] Committed

## Goal

Add prototype-like editor chrome and a framework-only compiled-output split view without changing core CodeMirror editor behavior.

## Deliverables

- [ ] Polish the editor tab strip inside the new workbench shell.
- [ ] Add a breadcrumbs row for the active editor context.
- [ ] Add editor action buttons only when each has real or mocked behavior.
- [ ] Add a compiled-output split view shell.
- [ ] Add static/mock output for `mjs`, `wasm`, and `c` targets.
- [ ] Add target selection controls.
- [ ] Add Copy, Download, and Close controls for the compiled-output pane.
- [ ] Update the Mock Inventory for the compiled output split view.

## Visible Functionality

- [ ] Existing editor open, edit, tab switch, and scroll behavior still works.
- [ ] Breadcrumbs reflect the active file or use a clearly mocked value.
- [ ] Compiled split view opens and closes without destroying the current editor tab.
- [ ] Target controls switch mock output content and selected state.
- [ ] Copy writes the selected mock output to the clipboard or shows a visible failure message.
- [ ] Download creates a downloadable mock artifact for the selected target.
- [ ] Closing compiled view preserves editor scrollability and diagnostics.
- [ ] No editor chrome control is dead.

## Mock Inventory Impact

- Expected mock entries:
  - Compiled output split view
- Update the parent plan if breadcrumbs or editor action buttons use mocked data.

## Verification

- [ ] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [ ] Run `git diff --check`.
- [ ] Run `git status --short` and confirm only intended files changed.
- [ ] Browser-check editor open, edit, scroll, and tab switching.
- [ ] Browser-check compiled split open/close behavior.
- [ ] Browser-check target switching.
- [ ] Browser-check Copy and Download controls.
- [ ] Browser-check Compile, Execute, diagnostics, and bottom output still work with the split view closed and open.

## Completion Notes

- Commit:
- Browser notes:
- Test output:
