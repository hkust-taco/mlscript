# Phase 2: Visual Foundation Progress Tracker

Parent plan: [MLscript Web IDE UI Framework Plan](../web-ide-ui-framework-plan.md)

## Status

- [ ] Not started
- [x] In progress
- [x] Browser verified
- [x] Tests passed
- [x] Committed

## Goal

Establish the visual system for the new IDE shell before adding more panel surfaces. This phase defines the reusable layout and theme tokens that make the UI dense, readable, and prototype-aligned.

## Deliverables

- [x] Add CSS tokens for warm light theme colors.
- [x] Add dark theme scaffold only if the theme toggle is functional in this phase.
- [x] Add layout tokens for rail width, side panel width, right inspector width, bottom panel height, and status bar height.
- [x] Add shared tokens for borders, radius, shadows, typography, and diagnostic severity colors.
- [x] Restyle existing shell, file explorer, editor chrome, diagnostics region, bottom region, and status bar to use the new tokens.
- [x] Ensure editor, left panel, right inspector, and bottom panel occupy real layout space and scroll independently.

## Visible Functionality

- [x] Theme toggle is shown only if it actually switches themes.
- [x] Active rail, tab, segmented-control, and selected states are visually distinct.
- [x] Text remains readable in all visible regions.
- [x] No control text overlaps or clips at desktop width.
- [x] No control text overlaps or clips at narrow viewport width.

## Mock Inventory Impact

- Expected new mock entries: none.
- If a theme button is rendered but dark theme is only partial, either complete it in this phase or document it in the Mock Inventory as a mocked/future UI surface.

## Verification

- [x] Run `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`.
- [x] Run `git diff --check`.
- [x] Run `git status --short` and confirm only intended files changed.
- [x] Browser-check light theme contrast and layout.
- [x] Browser-check dark theme if the theme button is visible.
- [x] Browser-check independent scrolling for editor, left panel, right inspector, and bottom panel.
- [x] Browser-check desktop and narrow viewport layout stability.
- [x] Capture a 1920x1080 Playwright screenshot.

## Completion Notes

- Commit: this phase commit.
- Browser notes: Playwright CLI verified clean console output, no theme toggle, independent overflow containers, Files collapse/reopen, `.mls` compile, Execute reopening the collapsed console, and no horizontal overflow at 390x844. Screenshot: `docs/web-ide-ui-framework-screenshots/phase-02/visual-foundation-1920x1080.png`.
- Test output: `hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide` passed 21 tests.
