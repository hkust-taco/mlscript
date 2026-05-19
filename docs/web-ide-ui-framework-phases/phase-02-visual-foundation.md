# Phase 2: Visual Foundation Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [ ] In progress
- [ ] Browser verified
- [ ] Tests passed
- [ ] Committed

## Goal

Establish the visual system for the new IDE shell before adding more panel surfaces. This phase defines the reusable layout and theme tokens that make the UI dense, readable, and prototype-aligned.

## Deliverables

- [ ] Add CSS tokens for warm light theme colors.
- [ ] Add dark theme scaffold only if the theme toggle is functional in this phase.
- [ ] Add layout tokens for rail width, side panel width, right inspector width, bottom panel height, and status bar height.
- [ ] Add shared tokens for borders, radius, shadows, typography, and diagnostic severity colors.
- [ ] Restyle existing shell, file explorer, editor chrome, diagnostics region, bottom region, and status bar to use the new tokens.
- [ ] Ensure editor, left panel, right inspector, and bottom panel occupy real layout space and scroll independently.

## Visible Functionality

- [ ] Theme toggle is shown only if it actually switches themes.
- [ ] Active rail, tab, segmented-control, and selected states are visually distinct.
- [ ] Text remains readable in all visible regions.
- [ ] No control text overlaps or clips at desktop width.
- [ ] No control text overlaps or clips at narrow viewport width.

## Mock Inventory Impact

- Expected new mock entries: none.
- If a theme button is rendered but dark theme is only partial, either complete it in this phase or document it in the Mock Inventory as a mocked/future UI surface.

## Verification

- [ ] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [ ] Run `git diff --check`.
- [ ] Run `git status --short` and confirm only intended files changed.
- [ ] Browser-check light theme contrast and layout.
- [ ] Browser-check dark theme if the theme button is visible.
- [ ] Browser-check independent scrolling for editor, left panel, right inspector, and bottom panel.
- [ ] Browser-check desktop and narrow viewport layout stability.

## Completion Notes

- Commit:
- Browser notes:
- Test output:
