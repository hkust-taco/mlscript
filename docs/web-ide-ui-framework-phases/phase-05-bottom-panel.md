# Phase 5: Bottom Panel Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [ ] In progress
- [ ] Browser verified
- [ ] Tests passed
- [ ] Committed

## Goal

Replace the single console surface with a native tabbed bottom panel that separates Output, Problems, and Terminal while preserving the current runtime output flow.

## Deliverables

- [ ] Add a `<bottom-panel>` custom element.
- [ ] Add Output, Problems, and Terminal tabs with native tab state.
- [ ] Route current console/runtime output into Output.
- [ ] Add mocked Problems content.
- [ ] Add mocked Terminal content.
- [ ] Add Preserve logs, Clear, Download, and Hide controls.
- [ ] Ensure Execute opens the Output tab if the bottom panel is hidden.
- [ ] Update the Mock Inventory for Problems and Terminal.

## Visible Functionality

- [ ] Output tab shows current output messages.
- [ ] Problems tab shows mock problem rows.
- [ ] Terminal tab shows mock terminal transcript or mutable mock lines.
- [ ] Tab switching updates visible content and ARIA selected state.
- [ ] Preserve logs changes Clear behavior.
- [ ] Clear removes visible output when preserve logs is off.
- [ ] Download creates a text download from the visible panel content.
- [ ] Hide collapses the bottom panel without overlaying editor or side panels.
- [ ] Execute reopens Output when hidden.

## Mock Inventory Impact

- Expected mock entries:
  - Problems tab
  - Terminal tab
- Update the parent plan if additional mocked bottom-panel controls are introduced.

## Verification

- [ ] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [ ] Run `git diff --check`.
- [ ] Run `git status --short` and confirm only intended files changed.
- [ ] Browser-check Output, Problems, and Terminal tab switching.
- [ ] Browser-check Preserve logs and Clear behavior.
- [ ] Browser-check Download behavior.
- [ ] Browser-check Hide and Execute-reopen behavior.
- [ ] Browser-check bottom panel occupies layout space and does not overlay editor content.

## Completion Notes

- Commit:
- Browser notes:
- Test output:
