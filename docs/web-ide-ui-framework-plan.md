# MLscript Web IDE UI Framework Plan

## Summary

Build the prototype-inspired UI framework in phases, using MLscript custom elements and native HTML primitives. Phase 1 prioritizes shell/layout architecture with mocked secondary panels, not real Search/Git/Outline/Terminal functionality. Existing editor, file explorer, compile, execute, diagnostics, and console behavior should remain working where practical.

## Key Changes

- Replace the current page-level layout with an MLscript-owned workbench shell custom element.
- Adopt the prototype structure: titlebar, left activity rail, left panel host, editor workbench, right diagnostics inspector, bottom panel, status bar.
- Use native HTML patterns:
  - `<dialog>` for command palette and share dialog.
  - `<details>/<summary>` for static trees/groups.
  - `<input type="search">`, checkboxes, radio groups, and buttons for controls.
  - `hidden`, `inert`, `aria-selected`, `aria-pressed`, and `role="tablist"`/`role="tab"` where appropriate.
- Do not introduce React, JSX, or another frontend framework.
- Treat the Claude Design prototype as a visual and interaction reference only.

## Functionality Standard

Every visible control must be functional in the phase where it appears.

- Real controls must dispatch the current Web IDE event or call the current component method.
- Framework-only controls must still change UI state, open/close a native surface, switch a tab, select a mode, copy mock text, clear mock content, or show a disabled state with a clear title.
- Nonfunctional placeholder buttons are not acceptable. If an action cannot be made useful in the current phase, render it disabled with `aria-disabled="true"` and a title explaining that the feature is mocked.
- Mocked surfaces must be internally consistent. Counts, badges, selected states, and visible content should agree with the mock data shown on screen.
- Keyboard and focus behavior counts as functionality for dialogs and tabbed surfaces: Escape closes dialogs, the first useful field receives focus, and tab selections update ARIA state.
- Maintain the mock inventory in this document. Every time a non-real UI element, mocked dataset, disabled future action, or framework-only behavior is added, document it in the Mock Inventory before committing that phase.

## Mock Inventory

This list tracks visible UI that is intentionally not backed by real functionality yet. Each phase must update this list when it adds, changes, or removes mocked UI.

| UI surface | Phase added | Mocked behavior | Required real replacement |
| --- | --- | --- | --- |
| Source Control panel | Phase 3 | Static changed-file list with stage/unstage movement between mock sections. | Real version-control state, staging, commit, pull, and push integration if supported by the Web IDE environment. |
| Outline panel | Phase 3 | Static symbol list with mocked editor navigation. | Real symbol extraction from the active MLscript file. |
| Examples panel | Phase 3 | Static examples list with mocked selection/detail behavior. | Real bundled examples/snippets that can open or load files. |
| Diagnostics sample dataset | Phase 4 | Static sample diagnostics shown in the inspector before compiler diagnostics arrive. | Real compiler diagnostics or the empty success state after compilation. |
| Diagnostics quick actions | Phase 4 | Quick fix, explain, and ignore are mocked state changes or disabled actions. | Real compiler/code-action integration or removal of unsupported actions. |
| Problems tab | Phase 5 | Mocked problem list separate from current diagnostics. | Real diagnostic/problem aggregation from compiler results. |
| Terminal tab | Phase 5 | Static terminal transcript or locally mutable mock lines. | Real terminal/REPL integration, or remove if unsupported. |
| Compiled output split view | Phase 6 | Static `.mjs`/`wasm`/`c` mock output selected by target controls. | Real generated-output preview based on current compiled file and selected backend. |
| Command palette future commands | Phase 7 | Commands without current runtime support switch mock UI state or render disabled. | Real command implementations or removal from the palette. |
| Share dialog | Phase 7 | Mock share URL and copy behavior. | Real share/export/persisted URL behavior, or removal if sharing is out of scope. |

## Progress Trackers

- [Phase 1: Workbench Shell](web-ide-ui-framework-phases/phase-01-workbench-shell.md)
- [Phase 2: Visual Foundation](web-ide-ui-framework-phases/phase-02-visual-foundation.md)
- [Phase 3: Left Activity Panels](web-ide-ui-framework-phases/phase-03-left-activity-panels.md)
- [Phase 4: Diagnostics Inspector](web-ide-ui-framework-phases/phase-04-diagnostics-inspector.md)
- [Phase 5: Bottom Panel](web-ide-ui-framework-phases/phase-05-bottom-panel.md)
- [Phase 6: Editor Workbench Chrome](web-ide-ui-framework-phases/phase-06-editor-workbench-chrome.md)
- [Phase 7: Native Dialogs](web-ide-ui-framework-phases/phase-07-native-dialogs.md)
- [Phase 8: Integration And Cleanup](web-ide-ui-framework-phases/phase-08-integration-cleanup.md)

## Phase Plan

### Phase 1: Workbench Shell

Create the structural framework.

- Add a top-level custom element, such as `<ide-workbench>`, that owns:
  - titlebar
  - left activity rail
  - left panel host
  - editor region
  - right diagnostics inspector region
  - bottom panel region
  - status bar
- Move sidebar tab switching out of `main.mls` into the shell component.
- Keep `<file-explorer>` and `<editor-panel>` embedded as real existing components.
- Replace the current right activity rail with a permanent diagnostics inspector region.
- Preserve current compile/execute events from the toolbar path, but route them through the new titlebar controls.
- Make each visible shell control functional:
  - Compile dispatches `compile-requested`.
  - Execute dispatches `execute-requested` and opens the output area if present.
  - left rail buttons switch/hide panels.
  - diagnostics hide/show control toggles the inspector.
  - status bar segments are buttons only if they open or switch a visible surface; otherwise render as plain text.

Commit: `Add IDE workbench shell`

### Phase 2: Visual Tokens And Layout Polish

Establish the design system before adding more panels.

- Add CSS tokens for:
  - warm light theme
  - dark theme scaffold
  - rail width
  - panel width
  - bottom panel height
  - status bar height
  - border, shadow, radius, diagnostic colors
- Restyle existing panels to match the prototype density:
  - compact headers
  - subtle borders
  - muted panel backgrounds
  - active tab and rail states
- Ensure editor, side panels, right inspector, and bottom panel all occupy real grid/flex space and scroll independently.
- Verify the theme toggle works if shown. If dark mode is not implemented in this phase, do not render a clickable theme button yet.

Commit: `Add IDE visual foundation`

### Phase 3: Left Activity Panels With Mock Data

Build the left-side framework using static data.

- Keep Files backed by the existing `<file-explorer>`.
- Add mock custom elements for:
  - Search
  - Source Control
  - Outline
  - Examples
- Use a small `mockWorkbenchData.mls` module for static sample entries.
- Each panel should be interactive enough to prove the shell:
  - rail button switches panels
  - active state updates
  - current panel can be hidden by clicking active rail item
  - panel content scrolls
- Required mocked interactions:
  - Search query filters the visible mock results and clear button empties the query.
  - Source Control stage/unstage buttons move mock files between sections.
  - Outline entries move the editor scroll position or dispatch a mocked navigation event.
  - Examples selection marks the selected example and can open a mock preview or replace mock panel detail.
- Do not implement real search, git, symbol extraction, or examples loading yet.

Commit: `Add mock left activity panels`

### Phase 4: Right Diagnostics Inspector Framework

Rework diagnostics into the prototype-style inspector.

- Replace `<reserved-panel>` with a diagnostics-focused custom element, such as `<diagnostics-inspector>`.
- Provide three native radio/segmented modes:
  - List
  - Tree
  - Source
- Initially support mock diagnostics for framework verification.
- Preserve a `setDiagnostics(diagnosticsPerFile)` method so current compiler diagnostics can still be routed later.
- Show severity counts in the inspector header.
- Source mode should use rich static cards with excerpt, location, and action controls that are either mocked state changes or disabled with clear titles.
- Required interactions:
  - List, Tree, and Source mode buttons switch visible content and update selected state.
  - Diagnostic rows/cards dispatch `open-file-at-location` when clicked if they point at an existing file.
  - Quick fix, explain, and ignore are either mocked state-changing controls or disabled with clear titles.
  - Hide diagnostics collapses the inspector and exposes a clear way to reopen it.

Commit: `Add diagnostics inspector framework`

### Phase 5: Bottom Panel Framework

Replace the single console surface with a tabbed bottom panel.

- Add `<bottom-panel>` with tabs:
  - Output
  - Problems
  - Terminal
- Output can wrap or reuse the existing console stream initially.
- Problems and Terminal use mock content.
- Keep Preserve logs, Clear, Download, and Hide controls as native controls/buttons.
- Maintain the existing requirement: Execute opens the Output tab if the bottom panel is hidden.
- Required interactions:
  - Output, Problems, and Terminal tabs switch content and ARIA selected state.
  - Preserve logs checkbox changes the clear behavior for the output panel.
  - Clear removes visible output or mock terminal lines when preserve logs is off.
  - Download creates a downloadable text blob from the visible panel content.
  - Hide collapses the bottom panel without overlaying the editor.

Commit: `Add bottom panel framework`

### Phase 6: Editor Workbench Chrome

Add prototype-like editor chrome without changing editor semantics.

- Keep CodeMirror/editor behavior intact.
- Add:
  - tab strip polish
  - breadcrumbs row
  - editor action buttons
  - optional compiled-output split view shell
- The compiled split view is framework-only:
  - static/mock `.mjs` content
  - target radio buttons for `mjs / wasm / c`
  - copy/download/close buttons wired only for UI state
- Required interactions:
  - split view opens and closes without destroying the current editor tab.
  - target buttons switch mock output content and selected state.
  - copy writes mock output text to the clipboard when browser permissions allow it, otherwise shows a visible failure message.
  - download creates a downloadable mock artifact.
- Do not implement real generated-output preview in this phase.

Commit: `Add editor workbench chrome`

### Phase 7: Native Dialogs And Command Surfaces

Add modal command surfaces with native HTML.

- Add `<command-palette-dialog>` backed by `<dialog>`.
- Open via titlebar button and keyboard shortcut.
- Include static commands:
  - Compile current file
  - Run compiled output
  - Change compile target
  - Go to symbol
  - Go to file
  - Search across files
  - Toggle theme
  - Toggle diagnostics panel
  - Toggle console panel
- Add a small `<share-dialog>` using `<dialog>`.
- Escape and dialog close behavior should be native.
- Required interactions:
  - Command palette opens from button and keyboard shortcut.
  - Search input filters command rows.
  - Commands that map to existing behavior dispatch the real events.
  - Mock commands switch the relevant mocked UI state.
  - Share dialog opens, closes, and has copy-link behavior using mock URL text.

Commit: `Add native command dialogs`

### Phase 8: Integration And Cleanup

Make the framework coherent with current runtime behavior.

- Update `main.mls` to query the new components:
  - diagnostics inspector for diagnostics
  - bottom panel for output visibility
  - titlebar/workbench for status updates
- Keep current compile/execute/run behavior working.
- Remove obsolete placeholder panels and old right-rail assumptions.
- Keep mock-only panels clearly isolated so real functionality can replace their data later.
- Remove or disable any visible action that still does nothing after integration.

Commit: `Integrate IDE workbench shell`

## Public Interfaces

- `<ide-workbench>` owns panel selection and layout state.
- `<diagnostics-inspector>.setDiagnostics(diagnosticsPerFile)` remains the diagnostics entrypoint.
- `<bottom-panel>.showPanel(panelName)` supports at least `"output"`, `"problems"`, and `"terminal"`.
- Existing events remain valid:
  - `compile-requested`
  - `execute-requested`
  - `terminate-requested`
  - `active-tab-changed`
  - `open-file-at-location`
- Add one new event only if needed:
  - `bottom-panel-open-requested` with `{ panel: "output" | "problems" | "terminal" }`.

## Test Workflow

Reuse the package-focused loop from `docs/web-ide-mlscript-second-pass-workflow.md`, but make browser verification stricter because this work changes visible behavior.

### Per-Phase Loop

1. Implement only one phase at a time.
2. Compile the package:

   ```sh
   timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"
   ```

3. Check diff hygiene:

   ```sh
   git diff --check
   git status --short
   ```

   No unrelated golden snapshots or unrelated test files should change.
   If the phase adds or changes any mocked UI, verify the Mock Inventory was updated in the same commit.

4. Start a local server from the Web IDE package directory:

   ```sh
   cd hkmc2/shared/src/test/mlscript-packages/web-ide
   python3 -m http.server 8123 --bind 127.0.0.1
   ```

5. Open `http://127.0.0.1:8123/index.html?<cache-buster>` with the Playwright CLI.
6. Verify no browser console errors were introduced.
7. Run the phase-specific browser checklist below.
8. Capture a 1920x1080 screenshot for any new or substantially changed UI surface and save it under `docs/web-ide-ui-framework-screenshots/<phase>/`.
9. Commit the phase only after compile, diff hygiene, and browser checks pass.

### Baseline Browser Checks

Run these after every phase:

- Page loads to the workbench without blank regions or horizontal document overflow.
- Files are visible in the explorer.
- A source file opens in the editor.
- Editor content scrolls independently from the panels.
- Compile works on an `.mls` file.
- Compile is skipped or disabled for a non-`.mls` file.
- Execute works and opens the Output tab/panel if hidden.
- Existing diagnostics still appear after compilation.
- Bottom panel occupies layout space and does not overlay editor or side panels.
- Resizing side and bottom panels does not expose handles over unrelated regions.

### Visible-Control Checks

For each phase, build a small manual checklist from every visible button, checkbox, tab, input, segmented control, dialog close button, and status-bar action added in that phase.

Each item must satisfy one of these outcomes:

- It performs a real Web IDE action.
- It performs a mocked UI action with visible state change.
- It is disabled and communicates why via title/label.
- It has been removed until the phase that can make it functional.

The phase is not complete until every visible control has one of those outcomes.

### Phase-Specific Browser Checks

Phase 1:

- Titlebar Compile and Execute dispatch the same behavior as the old toolbar.
- Left rail switches Files and any shell panels added in this phase.
- Clicking the active left rail button hides and reopens the left panel.
- Right diagnostics inspector hides and reopens.
- Status bar does not contain clickable dead controls.

Phase 2:

- Light theme renders with readable contrast.
- Dark theme renders if the theme button is visible.
- Layout remains stable at desktop width and a narrow viewport.
- Text does not overlap controls in titlebar, side panels, diagnostics, bottom panel, or status bar.

Phase 3:

- Search input filters mock results.
- Search clear button clears the query.
- Source Control mock stage/unstage changes visible sections and counts.
- Outline entry activation changes visible editor position or dispatches a visible navigation signal.
- Example selection changes selected state and detail/preview.

Phase 4:

- Diagnostics List, Tree, and Source modes switch content and selected state.
- Severity counts match visible mock or real diagnostics.
- Diagnostic click opens the relevant file/line when backed by a real file.
- Quick fix/explain/ignore controls are either stateful mocks or disabled.

Phase 5:

- Output, Problems, and Terminal tabs switch content.
- Preserve logs changes Clear behavior.
- Clear removes visible output when allowed.
- Download creates a text download from visible content.
- Hide collapses the panel; Execute reopens Output.

Phase 6:

- Compiled split view opens and closes.
- Target selector switches mock content.
- Copy and Download act on the currently selected mock output.
- Closing compiled view preserves editor tab, scrollability, and diagnostics.

Phase 7:

- Command palette opens from button and shortcut.
- Command search filters rows.
- Escape and close button close the dialog.
- Real commands dispatch real events; mock commands change visible UI state.
- Share dialog opens, closes, and copies mock link text or shows a visible failure.

Phase 8:

- No visible dead controls remain.
- Real compile, execute, diagnostics, file open, panel switching, and bottom output flow still work together.
- Mock-only panels are visually clear as framework surfaces without blocking real editor workflows.

### Automated/Scripted Checks

When practical, add lightweight browser scripts or test harness snippets that assert:

- required custom elements are defined;
- expected regions exist exactly once;
- selected/hidden ARIA states match visible panels;
- panel scroll containers have `scrollHeight > clientHeight` for long mock data;
- clicking each rail/tab/mode control changes the expected state;
- Execute opens the Output panel when hidden.

Keep these scripts as verification helpers unless the package test infrastructure already has a natural place for browser UI tests.

### Test Commands

- Run focused package test after each phase:
  - `sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"`
- Run diff checks before every commit:
  - `git diff --check`
  - `git status --short`
- Before final completion:
  - `sbt hkmc2AllTests/test`

## Assumptions

- Phase 1 target is the native shell framework, not full visual parity.
- Right side becomes a diagnostics inspector, not a right activity rail.
- Search, Source Control, Outline, Examples, Problems, Terminal, and compiled preview use mock data until later phases.
- Existing editor, file explorer, compile, execute, and diagnostics should remain usable unless a phase explicitly replaces their wrapper UI.
- No React, JSX, or frontend framework dependencies are introduced.
