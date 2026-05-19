# Phase 8: Integration And Cleanup Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [ ] In progress
- [ ] Browser verified
- [ ] Focused tests passed
- [ ] Full tests passed
- [ ] Committed

## Goal

Integrate the new UI framework with the current Web IDE runtime behavior, remove obsolete shell assumptions, and ensure every visible element is functional, mocked and documented, disabled with a reason, or removed.

## Deliverables

- [ ] Update `main.mls` to query and coordinate the new workbench components.
- [ ] Route diagnostics through `<diagnostics-inspector>`.
- [ ] Route output visibility through `<bottom-panel>`.
- [ ] Route titlebar/workbench status through the new shell.
- [ ] Keep compile, execute, terminate, file open, diagnostics, and output flows working together.
- [ ] Remove old placeholder panels and old right-rail assumptions.
- [ ] Audit all visible controls for functionality.
- [ ] Update the Mock Inventory to match the final visible mock surfaces.

## Visible Functionality

- [ ] No visible dead controls remain.
- [ ] Real compile flow works.
- [ ] Real execute flow works.
- [ ] Execute opens Output when hidden.
- [ ] Real diagnostics appear and can navigate to file locations where supported.
- [ ] File explorer opens files.
- [ ] Editor remains editable for writable files and readonly for readonly files.
- [ ] Left panel switching works.
- [ ] Bottom panel switching works.
- [ ] Diagnostics inspector modes work.
- [ ] Command palette and share dialogs work according to their documented real or mocked behavior.
- [ ] Mock-only panels are visibly coherent and do not block real editor workflows.

## Mock Inventory Impact

- Expected action: reconcile the parent plan's Mock Inventory with the final UI.
- Remove inventory rows for mocks that were replaced by real functionality.
- Add inventory rows for any remaining mocked or disabled future actions.
- Do not commit Phase 8 until the Mock Inventory matches the screen.

## Verification

- [ ] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [ ] Run `git diff --check`.
- [ ] Run `git status --short` and confirm only intended files changed.
- [ ] Browser-check every visible control using the functionality standard.
- [ ] Browser-check baseline workflow: open file, edit, compile, inspect diagnostics, execute, inspect output.
- [ ] Browser-check desktop and narrow viewport layouts.
- [ ] Browser-check no console errors were introduced.
- [ ] Run `timeout 1800s sbt hkmc2AllTests/test`.

## Completion Notes

- Commit:
- Browser notes:
- Focused test output:
- Full test output:
