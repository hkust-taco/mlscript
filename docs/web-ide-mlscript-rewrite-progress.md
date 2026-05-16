# Web IDE MLscript Rewrite Progress

This tracker follows `docs/web-ide-mlscript-rewrite-workflow.md`.

## Remaining Hand-Written JavaScript

- [x] `components/PanelPersistence.js` -> `components/PanelPersistence.mls`
- [x] `components/ResizeHandle.js` -> `components/ResizeHandle.mls`
- [x] `components/ConsolePanel.js` -> `components/ConsolePanel.mls`
- [x] `components/ToolbarPanel.js` -> `components/ToolbarPanel.mls`
- [ ] `components/TreeNode.js`
- [ ] `components/FileExplorer.js`
- [ ] `components/ReservedPanel.js`
- [ ] `editor/editor.js`
- [ ] `components/EditorPanel.js`
- [ ] `execution/worker.js`
- [ ] `main.js`

## Current Step

Next: `components/TreeNode.js`.

## Verification

- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `PanelPersistence.mls`.
- Browser smoke from `http://127.0.0.1:8125/index.html?panel-persistence=20260517` loaded `PanelPersistence.mjs`, restored/saved file explorer, diagnostics, and console panel sizes, compiled `main.mls`, and executed the default program.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `ResizeHandle.mls`.
- Browser smoke from `http://127.0.0.1:8126/index.html?resize-handle=20260517b` loaded `ResizeHandle.mjs`, did not load `ResizeHandle.js`, resized file explorer and console panels, persisted their sizes, compiled `main.mls`, and executed the default program.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `ConsolePanel.mls`.
- Headless browser smoke from `http://127.0.0.1:8127/index.html?console-panel=20260517d` loaded `ConsolePanel.mjs`, did not load `ConsolePanel.js`, rendered logs, collapsed/restored the panel, preserved logs, compiled `main.mls`, and executed the default program.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `ToolbarPanel.mls`.
- Headless browser smoke from `http://127.0.0.1:8128/index.html?toolbar=20260517b` loaded `ToolbarPanel.mjs`, did not load `ToolbarPanel.js`, dispatched compile for `/main.mls`, updated status/button states, showed and hid the status tooltip, and executed the default program.
