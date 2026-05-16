# Web IDE MLscript Rewrite Progress

This tracker follows `docs/web-ide-mlscript-rewrite-workflow.md`.

## Remaining Hand-Written JavaScript

- [x] `components/PanelPersistence.js` -> `components/PanelPersistence.mls`
- [x] `components/ResizeHandle.js` -> `components/ResizeHandle.mls`
- [x] `components/ConsolePanel.js` -> `components/ConsolePanel.mls`
- [x] `components/ToolbarPanel.js` -> `components/ToolbarPanel.mls`
- [x] `components/TreeNode.js` -> `components/TreeNode.mls`
- [x] `components/FileExplorer.js` -> `components/FileExplorer.mls`
- [x] `components/ReservedPanel.js` -> `components/ReservedPanel.mls`
- [x] `editor/editor.js` -> `editor/editor.mls`
- [x] `components/EditorPanel.js` -> `components/EditorPanel.mls`
- [ ] `execution/worker.js`
- [ ] `main.js`

## Current Step

Next: `execution/worker.js`.

## Verification

- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `PanelPersistence.mls`.
- Browser smoke from `http://127.0.0.1:8125/index.html?panel-persistence=20260517` loaded `PanelPersistence.mjs`, restored/saved file explorer, diagnostics, and console panel sizes, compiled `main.mls`, and executed the default program.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `ResizeHandle.mls`.
- Browser smoke from `http://127.0.0.1:8126/index.html?resize-handle=20260517b` loaded `ResizeHandle.mjs`, did not load `ResizeHandle.js`, resized file explorer and console panels, persisted their sizes, compiled `main.mls`, and executed the default program.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `ConsolePanel.mls`.
- Headless browser smoke from `http://127.0.0.1:8127/index.html?console-panel=20260517d` loaded `ConsolePanel.mjs`, did not load `ConsolePanel.js`, rendered logs, collapsed/restored the panel, preserved logs, compiled `main.mls`, and executed the default program.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `ToolbarPanel.mls`.
- Headless browser smoke from `http://127.0.0.1:8128/index.html?toolbar=20260517b` loaded `ToolbarPanel.mjs`, did not load `ToolbarPanel.js`, dispatched compile for `/main.mls`, updated status/button states, showed and hid the status tooltip, and executed the default program.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `TreeNode.mls`.
- Headless browser smoke from `http://127.0.0.1:8129/index.html?treenode=20260517b` loaded `TreeNode.mjs`, did not load `TreeNode.js`, opened source and compiled-output files from the tree, hid paired `.mjs` entries, updated folder children, removed stale `.mjs` buttons, and executed the default program.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `FileExplorer.mls`.
- Headless browser smoke from `http://127.0.0.1:8130/index.html?fileexplorer=20260517a` loaded `FileExplorer.mjs`, did not load `FileExplorer.js`, toggled sidebar collapse, created and opened a new file through the UI, showed and hid the tree tooltip, compiled `main.mls`, and executed the default program.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `ReservedPanel.mls`.
- Headless browser smoke from `http://127.0.0.1:8131/index.html?reserved-panel=1778962322` loaded `ReservedPanel.mjs`, did not load `ReservedPanel.js`, compiled and executed `main.mls`, rendered diagnostics, and exercised goto, diagnostic toggle, file toggle, collapse-all, and panel collapse behavior.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `editor/editor.mls`.
- Headless browser smoke from `http://127.0.0.1:8131/index.html?editor=1778962677` loaded `editor.mjs`, did not load `editor.js`, created mutable CodeMirror editor views, autosaved edits, compiled and executed edited `main.mls`, and kept readonly std-file edits from persisting.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `EditorPanel.mls`.
- Headless browser smoke from `http://127.0.0.1:8131/index.html?editor-panel=1778963227` loaded `EditorPanel.mjs`, did not load `EditorPanel.js`, kept public tab state, opened files, synchronized write/rename/delete filesystem events, navigated to a line, handled keyboard compile/execute, disabled std tabs, and closed a tab with Ctrl-W.
