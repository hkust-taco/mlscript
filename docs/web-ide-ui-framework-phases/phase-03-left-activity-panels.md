# Phase 3: Left Activity Panels Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [ ] In progress
- [ ] Browser verified
- [ ] Tests passed
- [ ] Committed

## Goal

Build the left activity panel framework with mocked but functional tool surfaces. Files remains real; Search, Source Control, Outline, and Examples are UI-framework mocks that prove switching, selection, filtering, and scrolling behavior.

## Deliverables

- [ ] Keep Files backed by the existing `<file-explorer>`.
- [ ] Add a Search panel custom element with static results.
- [ ] Add a Source Control panel custom element with static changed-file data.
- [ ] Add an Outline panel custom element with static symbol data.
- [ ] Add an Examples panel custom element with static examples.
- [ ] Add a small mock data module for these panels.
- [ ] Ensure each panel can scroll when content overflows.
- [ ] Update the Mock Inventory in the parent plan for every mocked surface added or changed.

## Visible Functionality

- [ ] Left rail switches Files, Search, Source Control, Outline, and Examples.
- [ ] Clicking the active rail item hides and reopens the left panel.
- [ ] Search input filters visible mock results.
- [ ] Search clear button empties the query and restores results.
- [ ] Source Control stage/unstage controls move mock files between sections and update counts.
- [ ] Outline entries visibly navigate, scroll the editor, or dispatch a visible mocked navigation signal.
- [ ] Examples selection updates selected state and detail/preview content.
- [ ] No mock panel contains dead buttons.

## Mock Inventory Impact

- Expected mock entries:
  - Search panel
  - Source Control panel
  - Outline panel
  - Examples panel
- Update the parent plan if any additional mock controls, badges, commands, or datasets are introduced.

## Verification

- [ ] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [ ] Run `git diff --check`.
- [ ] Run `git status --short` and confirm only intended files changed.
- [ ] Browser-check every left rail item.
- [ ] Browser-check each panel's visible controls against the functionality standard.
- [ ] Browser-check panel scroll behavior with long mock content.
- [ ] Browser-check Files, editor open, Compile, Execute, and diagnostics still work.

## Completion Notes

- Commit:
- Browser notes:
- Test output:
