# Phase 6: Editor Workbench Chrome Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [x] In progress
- [x] Browser verified
- [x] Tests passed
- [x] Committed

## Goal

Add prototype-like editor chrome and a framework-only compiled-output split view without changing core CodeMirror editor behavior.

## Deliverables

- [x] Polish the editor tab strip inside the new workbench shell.
- [x] Add a breadcrumbs row for the active editor context.
- [x] Add editor action buttons only when each has real or mocked behavior.
- [x] Add a compiled-output split view shell.
- [x] Add static/mock output for `mjs`, `wasm`, and `c` targets.
- [x] Add target selection controls.
- [x] Add Copy, Download, and Close controls for the compiled-output pane.
- [x] Update the Mock Inventory for the compiled output split view.

## Visible Functionality

- [x] Existing editor open, edit, tab switch, and scroll behavior still works.
- [x] Breadcrumbs reflect the active file or use a clearly mocked value.
- [x] Compiled split view opens and closes without destroying the current editor tab.
- [x] Target controls switch mock output content and selected state.
- [x] Copy writes the selected mock output to the clipboard or shows a visible failure message.
- [x] Download creates a downloadable mock artifact for the selected target.
- [x] Closing compiled view preserves editor scrollability and diagnostics.
- [x] No editor chrome control is dead.

## Mock Inventory Impact

- Expected mock entries:
  - Compiled output split view
- Parent plan already contains the compiled output split view mock entry. Breadcrumbs are backed by the real active-file event, and the only editor action opens the documented compiled-output mock surface.

## Verification

- [x] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [x] Run `git diff --check`.
- [x] Run `git status --short` and confirm only intended files changed.
- [x] Browser-check editor open, edit, scroll, and tab switching.
- [x] Browser-check compiled split open/close behavior.
- [x] Browser-check target switching.
- [x] Browser-check Copy and Download controls.
- [x] Browser-check Compile, Execute, diagnostics, and bottom output still work with the split view closed and open.

## Completion Notes

- Commit: this phase commit.
- Browser notes: Playwright CLI verified active-file breadcrumbs, editor open/edit/tab switch behavior, active CodeMirror scroll behavior in a constrained viewport, split open/close without losing editor tabs, `mjs`/`wasm`/`c` target switching, Copy feedback, Download of `mlscript-output.mjs`, diagnostics after Compile, Execute output with the split open, and output after the split closes. Screenshot: `docs/web-ide-ui-framework-screenshots/phase-06/editor-workbench-chrome-1920x1080.png`.
- Test output: `hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide` passed 26 tests.
