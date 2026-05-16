# Web IDE MLscript Rewrite Progress

This tracker follows `docs/web-ide-mlscript-rewrite-workflow.md`.

## Remaining Hand-Written JavaScript

- [x] `components/PanelPersistence.js` -> `components/PanelPersistence.mls`
- [x] `components/ResizeHandle.js` -> `components/ResizeHandle.mls`
- [ ] `components/ConsolePanel.js`
- [ ] `components/ToolbarPanel.js`
- [ ] `components/TreeNode.js`
- [ ] `components/FileExplorer.js`
- [ ] `components/ReservedPanel.js`
- [ ] `editor/editor.js`
- [ ] `components/EditorPanel.js`
- [ ] `execution/worker.js`
- [ ] `main.js`

## Current Step

Next: `components/ConsolePanel.js`.

## Verification

- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `PanelPersistence.mls`.
- Browser smoke from `http://127.0.0.1:8125/index.html?panel-persistence=20260517` loaded `PanelPersistence.mjs`, restored/saved file explorer, diagnostics, and console panel sizes, compiled `main.mls`, and executed the default program.
- `timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"` passed after `ResizeHandle.mls`.
- Browser smoke from `http://127.0.0.1:8126/index.html?resize-handle=20260517b` loaded `ResizeHandle.mjs`, did not load `ResizeHandle.js`, resized file explorer and console panels, persisted their sizes, compiled `main.mls`, and executed the default program.
