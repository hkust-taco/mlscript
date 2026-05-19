# Phase 5: Bottom Panel Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [x] In progress
- [x] Browser verified
- [x] Tests passed
- [x] Committed

## Goal

Replace the single console surface with a native tabbed bottom panel that separates Output, Problems, and Terminal while preserving the current runtime output flow.

## Deliverables

- [x] Add a `<bottom-panel>` custom element.
- [x] Add Output, Problems, and Terminal tabs with native tab state.
- [x] Route current console/runtime output into Output.
- [x] Add mocked Problems content.
- [x] Add mocked Terminal content.
- [x] Add Preserve logs, Clear, Download, and Hide controls.
- [x] Ensure Execute opens the Output tab if the bottom panel is hidden.
- [x] Update the Mock Inventory for Problems and Terminal.

## Visible Functionality

- [x] Output tab shows current output messages.
- [x] Problems tab shows mock problem rows.
- [x] Terminal tab shows mock terminal transcript or mutable mock lines.
- [x] Tab switching updates visible content and ARIA selected state.
- [x] Preserve logs changes Clear behavior.
- [x] Clear removes visible output when preserve logs is off.
- [x] Download creates a text download from the visible panel content.
- [x] Hide collapses the bottom panel without overlaying editor or side panels.
- [x] Execute reopens Output when hidden.

## Mock Inventory Impact

- Expected mock entries:
  - Problems tab
  - Terminal tab
- Parent plan already contains the Problems and Terminal mock entries. No additional mocked bottom-panel controls were introduced beyond those entries.

## Verification

- [x] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [x] Run `git diff --check`.
- [x] Run `git status --short` and confirm only intended files changed.
- [x] Browser-check Output, Problems, and Terminal tab switching.
- [x] Browser-check Preserve logs and Clear behavior.
- [x] Browser-check Download behavior.
- [x] Browser-check Hide and Execute-reopen behavior.
- [x] Browser-check bottom panel occupies layout space and does not overlay editor content.

## Completion Notes

- Commit: this phase commit.
- Browser notes: Playwright CLI verified the `<bottom-panel>` exists, Output/Problems/Terminal tabs switch with ARIA selected state, Output receives runtime-style log messages, Preserve logs prevents Clear from deleting output, Clear removes output when Preserve logs is off, Download creates `mlscript-output.txt`, Problems renders three mock rows and dispatches `/main.mls:5`, Terminal accepts a mock `help` command and can be cleared, Hide collapses the panel, Execute reopens Output, and the editor bottom edge stays above the bottom panel. Screenshot: `docs/web-ide-ui-framework-screenshots/phase-05/bottom-panel-1920x1080.png`.
- Test output: `hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide` passed 25 tests.
