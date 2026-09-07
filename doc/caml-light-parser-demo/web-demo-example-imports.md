# Web Demo Example Imports

## Goal

Import every parser example added in this phase into the browser demo and verify
that the demo can parse them successfully.

## Imported Examples

The web demo now includes these Caml Light ports:

- `caml-fibonacci`: Fibonacci
- `caml-sieve`: Sieve
- `caml-integer-sets`: Integer sets
- `caml-pascal-values`: Pascal values
- `caml-picomach-constants`: Picomach constants
- `caml-bit-buffer`: Bit buffer
- `caml-priority-queue`: Priority queue
- `caml-word-count`: Word count
- `caml-bubble-sort`: Bubble sort
- `caml-insertion-sort`: Insertion sort

The web demo also includes these extensible parser examples:

- `extensible-routes`: small HTTP route declarations
- `extensible-workflow`: workflow steps with recursive extension syntax

## Implementation Notes

- Added the imported sources to `apps/parsing-web-demo/Examples.mls`.
- Fixed selector lookup to use the `MutMap` API instead of calling `get`
  directly on the examples map.
- Replaced recursive demo-side error-tree traversal with a summary-based check.
  The previous traversal could throw a match error while inspecting otherwise
  valid parse trees; the parser's own summary already marks error trees with the
  warning marker used elsewhere by the parsing app.

## Verification

- Ran `hkmc2AppsTests/testOnly hkmc2.AppsCompileTestRunner -- -z parsing-web-demo`.
  The web-demo compile tests passed.
- Served `hkmc2/shared/src/test/mlscript-compile` at
  `http://127.0.0.1:4173/apps/parsing-web-demo/`.
- Used Playwright to select and parse every available demo example.

Browser verification covered:

- `hanoi`
- `extensible`
- all 10 imported Caml Light examples
- both imported extensible parser examples

Every example produced non-empty output, and none opened the error dialog.
