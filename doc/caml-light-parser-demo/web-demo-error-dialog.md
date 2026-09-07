# Web Demo Task 01: Error Dialog

Status: Done

## Goal

The parser web demo must not hide parse, lexer, or rendering failures in the
console. A failed parse action should show an eye-catching modal dialog with the
error message and a readable stack trace.

## Changes

- Added an HTML `dialog#error-dialog` to the web demo.
- Added visible error styling for the dialog, backdrop, message, and stack
  trace.
- Moved tokenization inside the `Runtime.try_catch` parse action so lexer
  failures are displayed through the same dialog path as parser failures.
- Added `showError`, `hideError`, and stack formatting helpers in `main.mls`.
- Replaced selector-change throws with the same dialog path.

## Verification

- Ran focused compile check:
  `hkmc2AppsTests/testOnly hkmc2.AppsCompileTestRunner -- -z parsing-web-demo`
- Result: passed.
- Served `hkmc2/shared/src/test/mlscript-compile` locally and opened
  `http://127.0.0.1:4173/apps/parsing-web-demo` with Playwright.
- Verified the page loads without parser-console errors and that invalid input
  (`let =`) opens the modal dialog with `Parser Error`, the message, and stack
  trace text.
