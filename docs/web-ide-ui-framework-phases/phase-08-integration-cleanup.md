# Phase 8: Integration And Cleanup Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [x] In progress
- [x] Browser verified
- [x] Focused tests passed
- [x] Full tests passed
- [x] Committed

## Goal

Integrate the new UI framework with the current Web IDE runtime behavior, remove obsolete shell assumptions, and ensure every visible element is functional, mocked and documented, disabled with a reason, or removed.

## Deliverables

- [x] Update `main.mls` to query and coordinate the new workbench components.
- [x] Route diagnostics through `<diagnostics-inspector>`.
- [x] Route output visibility through `<bottom-panel>`.
- [x] Route titlebar/workbench status through the new shell.
- [x] Keep compile, execute, terminate, file open, diagnostics, and output flows working together.
- [x] Remove old placeholder panels and old right-rail assumptions.
- [x] Audit all visible controls for functionality.
- [x] Update the Mock Inventory to match the final visible mock surfaces.

## Visible Functionality

- [x] No visible dead controls remain.
- [x] Real compile flow works.
- [x] Real execute flow works.
- [x] Execute opens Output when hidden.
- [x] Real diagnostics appear and can navigate to file locations where supported.
- [x] File explorer opens files.
- [x] Editor remains editable for writable files and readonly for readonly files.
- [x] Left panel switching works.
- [x] Bottom panel switching works.
- [x] Diagnostics inspector modes work.
- [x] Command palette and share dialogs work according to their documented real or mocked behavior.
- [x] Mock-only panels are visibly coherent and do not block real editor workflows.

## Mock Inventory Impact

- Expected action: reconcile the parent plan's Mock Inventory with the final UI.
- Remove inventory rows for mocks that were replaced by real functionality.
- Add inventory rows for any remaining mocked or disabled future actions.
- Do not commit Phase 8 until the Mock Inventory matches the screen.
- The parent plan Mock Inventory still matches the final visible mock surfaces: Search, Source Control, Outline, Examples, Diagnostics sample/quick actions, Problems, Terminal, compiled-output split view, command palette future commands, and Share remain intentionally mocked or disabled. No mock row was removed or added in this cleanup phase.

## Verification

- [x] Run `timeout 300s sbt --client "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [x] Run `git diff --check`.
- [x] Run `git status --short` and confirm only intended files changed.
- [x] Browser-check every visible control using the functionality standard.
- [x] Browser-check baseline workflow: open file, edit, compile, inspect diagnostics, execute, inspect output.
- [x] Browser-check desktop and narrow viewport layouts.
- [x] Browser-check no console errors were introduced.
- [x] Run `timeout 1800s sbt --client "hkmc2AllTests/test"`.

## Completion Notes

- Commit: this phase commit.
- Browser notes: Playwright CLI verified custom element registration, removal of obsolete `reserved-panel`/`console-panel` DOM and CSS variable usage, file explorer open flow, real `.mls` compile, disabled Compile on `.mjs`, Execute reopening Output, left panel switching and hide/reopen, diagnostics mode switching and hide/reopen, bottom tabs, compiled-output mock split, command palette filtering, share copy feedback, file/editor scrolling, editable std files, sidebar resize handles bounded above the bottom panel, desktop no horizontal overflow, narrow viewport side-panel auto-close with a usable editor width, and 0 console errors/warnings. Screenshot captured at `docs/web-ide-ui-framework-screenshots/phase-08/integration-cleanup-1920x1080.png`.
- Focused test output: `hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide` passed 25 tests.
- Full test output: `hkmc2AllTests/test` passed 574 tests.
