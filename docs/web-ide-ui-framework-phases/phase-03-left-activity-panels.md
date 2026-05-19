# Phase 3: Left Activity Panels Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [x] In progress
- [x] Browser verified
- [x] Tests passed
- [x] Committed

## Goal

Build the left activity panel framework with mocked but functional tool surfaces. Files remains real; Search, Source Control, Outline, and Examples are UI-framework mocks that prove switching, selection, filtering, and scrolling behavior.

## Deliverables

- [x] Keep Files backed by the existing `<file-explorer>`.
- [x] Add a Search panel custom element with static results.
- [x] Add a Source Control panel custom element with static changed-file data.
- [x] Add an Outline panel custom element with static symbol data.
- [x] Add an Examples panel custom element with static examples.
- [x] Add a small mock data module for these panels.
- [x] Ensure each panel can scroll when content overflows.
- [x] Update the Mock Inventory in the parent plan for every mocked surface added or changed.

## Visible Functionality

- [x] Left rail switches Files, Search, Source Control, Outline, and Examples.
- [x] Clicking the active rail item hides and reopens the left panel.
- [x] Search input filters visible mock results.
- [x] Search clear button empties the query and restores results.
- [x] Source Control stage/unstage controls move mock files between sections and update counts.
- [x] Outline entries visibly navigate, scroll the editor, or dispatch a visible mocked navigation signal.
- [x] Examples selection updates selected state and detail/preview content.
- [x] No mock panel contains dead buttons.

## Mock Inventory Impact

- Expected mock entries:
  - Search panel
  - Source Control panel
  - Outline panel
  - Examples panel
- Update the parent plan if any additional mock controls, badges, commands, or datasets are introduced.

## Verification

- [x] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [x] Run `git diff --check`.
- [x] Run `git status --short` and confirm only intended files changed.
- [x] Browser-check every left rail item.
- [x] Browser-check each panel's visible controls against the functionality standard.
- [x] Browser-check panel scroll behavior with long mock content.
- [x] Browser-check Files, editor open, Compile, Execute, and diagnostics still work.
- [x] Capture a 1920x1080 Playwright screenshot.

## Completion Notes

- Commit: this phase commit.
- Browser notes: Playwright CLI verified clean console output, rail switching across Files/Search/Source Control/Outline/Examples, active rail collapse/reopen, Search filter and clear, Source Control stage/unstage counts, Outline mock navigation feedback, Examples selection/detail updates, scrollable Search and Source Control mock content, no narrow viewport horizontal overflow, and preserved file open/compile/execute/diagnostics flow. Screenshot: `docs/web-ide-ui-framework-screenshots/phase-03/left-activity-panels-1920x1080.png`.
- Test output: `hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide` passed 23 tests.
