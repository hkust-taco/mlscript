# Phase 1: Workbench Shell Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [x] In progress
- [x] Browser verified
- [x] Tests passed
- [x] Committed

## Goal

Create the native custom-element workbench shell that owns the IDE layout. This phase establishes the structure for the titlebar, left activity rail, left panel host, editor region, right diagnostics inspector, bottom panel region, and status bar without trying to complete visual parity.

## Deliverables

- [x] Add a top-level `<ide-workbench>` custom element implemented in MLscript.
- [x] Move shell panel selection and layout state out of `main.mls` into the workbench shell.
- [x] Embed the existing `<file-explorer>` as the real Files panel.
- [x] Embed the existing `<editor-panel>` as the real editor region.
- [x] Replace the current right activity rail with a permanent diagnostics inspector region.
- [x] Route titlebar Compile and Execute controls through the existing `compile-requested` and `execute-requested` events.
- [x] Add status bar structure with only functional controls; render non-interactive status as plain text.

## Visible Functionality

- [x] Compile dispatches the current compile flow.
- [x] Execute dispatches the current execute flow and opens the output area if present.
- [x] Left rail buttons switch panels.
- [x] Clicking the active left rail item hides and reopens the left panel.
- [x] Diagnostics inspector hide/show control toggles the inspector.
- [x] No visible shell control is a dead button.

## Mock Inventory Impact

- Expected new mock entries: none.
- If any framework-only visible control is added, update the Mock Inventory in the parent plan before commit.

## Verification

- [x] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [x] Run `git diff --check`.
- [x] Run `git status --short` and confirm only intended files changed.
- [x] Start the local Web IDE server and open `http://127.0.0.1:8123/index.html?<cache-buster>` with Playwright.
- [x] Verify the page loads without console errors.
- [x] Verify Files, editor open, Compile, Execute, diagnostics display, and panel scrolling still work.
- [x] Verify desktop and narrow viewport layouts do not overflow horizontally.
- [x] Capture a 1920x1080 Playwright screenshot.

## Completion Notes

- Commit: this phase commit.
- Browser notes: Playwright CLI verified clean console output, Files collapse/reopen, diagnostics hide/show, active-file status updates, `.mls` compile, disabled `.mjs` compile, Execute reopening the collapsed console, and no horizontal overflow at 390x844. Screenshot: `docs/web-ide-ui-framework-screenshots/phase-01/workbench-shell-1920x1080.png`.
- Test output: `hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide` passed 21 tests.
