# Web IDE Polish Implementation Plan

This document consolidates the remaining Web IDE polish work into a formal implementation plan. It is intended to be executed as a sequence of small, reviewable commits. The plan is split into two workstreams:

- Part A covers general polish, editor quality-of-life improvements, persistence, accessibility, documentation, and small correctness checks.
- Part B introduces a Settings dialog and then wires existing or new preferences through a shared settings store.

The plan intentionally favors narrow changes over broad refactors. Each task should be checked against the current implementation before any edits are made, because some items may already have been completed by earlier sessions.

## Execution Rules

1. Use one commit per task unless a task is explicitly described as a grouped check.
2. Touch as few files as possible for each commit.
3. Edit `.mls` source files, not generated `.mjs` files.
4. Preserve existing indentation, blank lines, and `end` markers.
5. Do not perform unrelated refactors, renames, formatting passes, or cleanup.
6. When exact text, keys, code snippets, or URLs are specified here, use them verbatim.
7. Do not introduce new mock data except where this plan explicitly requests it.
8. Keep Source Control, Terminal, and generated-output panels hidden unless a later task explicitly enables them.
9. After `SettingsStore` exists, all new user preferences must go through it. Do not add new ad hoc `localStorage` calls after that point.
10. Work on a branch or worktree and do not push unless explicitly asked.
11. Update `PLAN.md` only to describe work that actually shipped.

## Validation Rules

After each implementation task, run:

```sh
sbt --client "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"
```

If the task is documentation-only, a package test is optional, but `git diff --check` should still be run before committing.

Before the final closing commit for this plan, run:

```sh
sbt --client "hkmc2PackagesTest/test"
```

## Skip Policy

Before implementing a task, inspect the relevant files and behavior. If the code already satisfies the task, skip the task and mention the skip in the commit summary or progress note. Do not rework working code for style preference alone.

Some tasks are explicitly investigative. For those tasks, only make a code change if there is a clear and local defect. If no defect is found, record that the check was completed and move on.

---

# Part A: General Polish and Quality-of-Life

Part A can be executed independently of most Settings work. The only planned dependency is that the editor font-size implementation in A2 should land before the Settings row that controls it in Part B.

## A1. Known Issues Review

### A1.1 Review CodeMirror folding logic

Inspect `foldRange` and `mlscriptFolding` in `editor/editor.mls`. The goal is not to redesign folding. Only fix an obvious local bug, such as:

- a fold range that starts or ends one line too early or too late,
- a missing null or absent-value check,
- a range that includes invalid line numbers,
- a clearly inverted condition.

If the implementation is coherent and no local defect is visible, skip this task.

### A1.2 Review fold gutter styling

Inspect `.cm-foldGutter` and related fold-marker CSS in `style.css`. If the app relies on CodeMirror's default fold gutter markers with no partial custom styling, skip this task. Only make a change if there is a half-finished override that visually conflicts with the rest of the editor or breaks interaction.

## A2. Editor Projection Legibility

This work creates the editor font-size control that the Settings dialog will later expose. Implement the editor behavior first, then wire the Settings row in Part B.

### A2.1 Add an editor font-size CSS variable

Add `--editor-font-size` to `:root` in `style.css`. Use this variable only for CodeMirror editor text, specifically `.cm-editor` and `.cm-content` font sizing. Do not apply it to sidebars, tabs, dialogs, buttons, or status text.

Expected result: editor text size can be changed by setting a single CSS custom property.

### A2.2 Add editor font-size adjustment logic

Add `bumpEditorFontSize(delta)` in `editor/editor.mls`. It should:

- read the current editor font size,
- add `delta`,
- clamp the result to the range 10-24 pixels,
- write the result back through `--editor-font-size`.

Use the app's existing style and helper conventions. Avoid duplicating persistence logic here if that logic already lives elsewhere.

### A2.3 Add keyboard shortcuts for font-size changes

Wire Cmd/Ctrl+= and Cmd/Ctrl+- into the existing `handleShortcut` chain in `EditorPanel.mls`.

Do not bind:

- Cmd/Ctrl+0, because browsers reserve it for page zoom reset,
- Cmd/Ctrl+B, because it is already used for the left-sidebar toggle.

Expected result: the active editor font size increases or decreases without affecting browser zoom.

### A2.4 Persist editor font size

Persist the editor font size using `PanelPersistence.mls` and its existing localStorage convention. Do not introduce a separate storage pattern for this task.

Expected result: after reload, the editor uses the last selected font size.

## A3. Examples Panel

The Examples panel should be made functional with two small built-in examples. The content is intentionally minimal; better examples can be supplied later.

### A3.1 Add initial example data

Add exactly the following two examples and no additional entries:

```text
{id: "pattern-matching", title: "Pattern Matching", code: "data class Cons(head, tail)\ndata object Nil\n\nfun sum(list) = if list is\n  Cons(h, t) then h + sum(t)\n  Nil then 0\n\nsum(Cons(1, Cons(2, Cons(3, Nil))))"}
```

```text
{id: "recursion", title: "Recursion", code: "fun factorial(n) =\n  if n <= 1 then 1\n  else n * factorial(n - 1)\n\nfactorial(5)"}
```

If either example causes the package test to fail, replace the failing example body with `1 + 1` rather than spending time debugging example syntax.

### A3.2 Replace mock example source

Update `ExamplesPanel` in `components/MockActivityPanels.mls` to use the new example data instead of `mockWorkbenchData.examples`.

Remove the "Mock library" label. Keep the rail button hidden for now.

### A3.3 Implement load-example behavior

Wire "load example" so it reuses the same create-and-open file flow already used by `FileExplorer.mls` or `main.mls`.

Expected result: selecting an example creates or opens a file containing the example code, then focuses it in the editor.

### A3.4 Unhide the Examples rail button

Only perform this task if A3.1-A3.3 passed. Unhide the Examples rail button in `IdeWorkbench.mls`.

If any earlier Examples task was skipped or failed, leave the rail button hidden and explain why in the commit note.

### A3.5 Update visible-plan documentation

Update `PLAN.md` to reflect only the Examples work that actually shipped.

## A4. Status Bar and Editor Info

The status bar should expose basic editor state without requiring new layout surfaces.

### A4.1 Dispatch cursor-position updates

In `editor/editor.mls`, dispatch a `cursor-position-changed` DOM event whenever the CodeMirror selection changes. The event detail should include:

- line number,
- column number.

Use 1-based line and column values for user-facing display.

### A4.2 Render cursor position in the existing status bar

Search for an existing status-bar component or element first, using `status-bar` across `components/*.mls`. If a status bar already exists, reuse it. Do not create a second status bar.

Render the current cursor position as:

```text
Ln X, Col Y
```

### A4.3 Render selected-character count

Using the same listener, render:

```text
(N selected)
```

only when the current selection length is greater than zero. Hide this label when there is no selection.

### A4.4 Add encoding and line-ending labels

Add a static status-bar label:

```text
UTF-8 LF
```

This is a hardcoded product assumption, not computed from file contents.

### A4.5 Add indentation label

Add a static status-bar label:

```text
Spaces: 2
```

This is also hardcoded. Do not infer it from the active file.

## A5. Layout and Filter Persistence

These persistence keys will also be used by the Settings "Reset Layout to Default" action. Keep key names stable once chosen.

### A5.1 Persist left sidebar width

Persist the user-adjusted width of the left sidebar. Restore it during workbench initialization.

Expected result: resizing the left sidebar survives page reload.

### A5.2 Persist right sidebar width

Persist the user-adjusted width of the right sidebar. Restore it during workbench initialization.

Expected result: resizing the Problems sidebar survives page reload.

### A5.3 Persist bottom panel height

Persist the user-adjusted bottom panel height. Restore it during workbench initialization.

Expected result: resizing the Output/Logging panel survives page reload.

### A5.4 Persist last active bottom tab

Persist whether the bottom panel last showed Output or Logging. Restore that tab on reload.

This should not force the bottom panel open if the panel is intentionally collapsed, unless current behavior already does so.

### A5.5 Persist Problems panel scope

Persist the Problems panel scope, either Workspace or Current file. Restore it when the diagnostics inspector initializes.

### A5.6 Persist Logs filters

Persist the Logs level filter and source filter. Restore both values when the bottom panel initializes.

If source options are generated dynamically from log entries, restore the saved source only when it exists in the current option set.

## A6. Discoverability

These tasks make existing actions easier to find through command palette entries, shortcuts, or consistent dialog behavior.

### A6.1 Add New File to the command palette

Add a command palette item labeled "New File". Do not add a keyboard shortcut, because Cmd/Ctrl+N is browser-reserved.

The command should reuse the existing new-file flow rather than duplicating file-creation logic.

### A6.2 Add Problems panel toggle shortcut

Add a right-rail Problems toggle bound to Cmd/Ctrl+Shift+B. This shortcut is confirmed not to collide with the existing Cmd/Ctrl+B left-sidebar toggle.

Expected result: the shortcut opens or closes the Problems panel.

### A6.3 Add Clear Output action if missing

Check whether a Clear Output button and command already exist. If either is missing, add the missing surface and reuse the existing output-clear behavior.

Do not create a second output-clearing implementation.

### A6.4 Add Clear Logs action if missing

Check whether a Clear Logs button and command already exist. If either is missing, add the missing surface and reuse the existing logs-clear behavior.

Do not create a second logs-clearing implementation.

### A6.5 Add Export Project to the command palette

Add an "Export Project" command palette item that invokes the existing project export behavior.

Expected result: users can export the current project without opening the Project Switcher first.

### A6.6 Audit Escape handling for dialogs

Check exactly these dialogs:

- Command Palette,
- Share dialog,
- Project Switcher.

Each should close on Escape. Fix only a missing or broken Escape case. Do not refactor dialog infrastructure.

## A7. Small Polish

### A7.1 Add middle-click tab close

In `EditorPanel.mls`, add support for closing editor tabs with a middle-click, where `event.button === 1`.

Prevent browser autoscroll behavior if necessary.

### A7.2 Verify dirty-dot clearing after undo

In `EditorPanel.mls`, check whether undoing back to the saved state clears the dirty indicator on the tab.

Only fix this exact case if it is broken. Do not redesign dirty-state tracking.

### A7.3 Add rail button aria labels

Add missing `aria-label` attributes to rail icon buttons in `IdeWorkbench.mls` only.

Use concise labels that match the visible panel purpose, such as "Files", "Search", "Outline", or "Problems".

### A7.4 Add temporary Copy Markdown feedback

For the Problems "Copy Markdown" action, briefly relabel the button itself to:

```text
Copied!
```

Then revert after approximately one second. Do not add a new toast, snackbar, or notification element.

### A7.5 Review dialog and tooltip z-index usage

Check z-index usage in exactly:

- `NativeDialogs.mls`,
- `ProjectSwitcher.mls`.

Compare dialog layering against `--z-tooltip`. Fix only a clear inconsistency where a tooltip or dialog can incorrectly cover the other.

### A7.6 Check Output auto-scroll during execution

Check whether Output auto-scrolls on every new execution chunk, not only once when execution starts.

If auto-scroll only happens at the beginning, update the append path so each new chunk keeps the latest output visible when the user has not intentionally scrolled away.

## A8. Accessibility

### A8.1 Audit icon-only toolbar and rail buttons

Inspect exactly:

- `IdeWorkbench.mls`,
- `ToolbarPanel.mls`.

Add missing `aria-label` attributes to icon-only buttons. Do not broaden this task into a full accessibility rewrite.

### A8.2 Audit removed focus outlines

Search `style.css` for `outline: none` on focusable elements. If a focus outline was removed without a replacement focus style, add a visible replacement.

Expected result: keyboard users can see focus location on buttons, tabs, inputs, and dialog controls.

### A8.3 Verify semantic color contrast

Compute relative-luminance contrast ratios for these text colors against `--ide-bg`:

- `--ide-danger`,
- `--ide-warning`,
- `--ide-info`.

Use the WCAG AA threshold of 4.5:1 for normal text. Only change a color if the computed ratio is clearly below threshold.

## A9. Documentation Pass

Run this after Part A and Part B implementation work so the docs describe reality rather than planned behavior.

### A9.1 Update `PLAN.md`

Confirm `PLAN.md` matches the behavior currently visible in the Web IDE. Remove claims about features that did not ship.

### A9.2 Update `AGENTS.md`

Confirm `AGENTS.md` reflects the current component layout, important event names, and development workflow for the Web IDE package.

### A9.3 Update package `README.md`

Confirm the package README matches the current setup, build, and run steps.

## A10. Stretch Filler

These are low-priority tasks for when the main polish work is complete. Keep them small.

### A10.1 Route stray console logging through Logger

Search for `console.log` calls that are not routed through `common/Logger.mls`.

Fix up to five instances, then stop. Do not attempt a full logging migration in this task.

### A10.2 Proofread visible copy

Proofread toolbar labels, dialog copy, and empty-state text for clear misspellings only.

Do not rewrite tone, terminology, or product language unless there is an obvious typo.

### A10.3 Add a favicon only if absent

Check `index.html` for a custom favicon `<link>`. If one is entirely absent, add a minimal favicon.

Do not replace an existing favicon.

### A10.4 Cross-check shortcut tooltips

Compare shortcut tooltips against actual bindings in `handleShortcut`.

Fix label text only when it is mismatched. Do not add new shortcuts in this task.

### A10.5 Read ZIP export path for obvious bugs

Read the ZIP export code path once and look for an obvious local defect, such as a missing file, wrong path prefix, or unhandled empty project.

Do not perform a live export test as part of this task unless explicitly requested.

### A10.6 Run final package test and closing summary

Run:

```sh
sbt --client "hkmc2PackagesTest/test"
```

Then make a closing summary commit that updates the relevant plan documentation to match the actual completed work.

---

# Part B: Settings Panel

Part B creates a Settings dialog and then wires preferences through a shared settings store. Phase 0 is mandatory foundation work. Do not start Phase 1, 2, or 3 until Phase 0 is complete.

## Phase 0: Settings Foundation

### B0.1 Add `SettingsStore`

Create `common/SettingsStore.mls`.

Expose:

```text
getSetting(key, default)
setSetting(key, value)
```

Back the store with `localStorage`. Prefix every key with:

```text
settings.
```

Follow the style of `PanelPersistence.mls`: plain functions, no JSON blob that stores all preferences together.

### B0.2 Create the base Settings dialog component

Create `components/SettingsDialog.mls`.

Use `ShareDialog` in `components/NativeDialogs.mls` as the structural model. The new component should use:

- `connectedCallback`,
- `render()`,
- `attachEventListeners()`,
- `dialog()`,
- `openDialog()`.

The rendered HTML should contain a native dialog:

```html
<dialog class="settings-dialog-native" data-dismissible="true">
  <form method="dialog">
    ...
  </form>
</dialog>
```

The header should contain the title "Settings" and a close button. The body can be empty until the tab task lands.

### B0.3 Wire Settings dialog dismissal and open event

Inside `SettingsDialog.attachEventListeners()`:

- use the existing `closeDismissibleDialogFromBackdrop(dialog())`,
- register a listener for `settings-dialog-open-requested`,
- call `openDialog()` when that event is received.

Register the custom element:

```text
customElements.define("settings-dialog", SettingsDialog)
```

Do not duplicate the backdrop-dismiss helper.

### B0.4 Mount Settings dialog in the workbench

Add:

```html
<settings-dialog></settings-dialog>
```

in `components/IdeWorkbench.mls` next to the existing `<share-dialog></share-dialog>`.

### B0.5 Add Settings toolbar button

Add a `#settings` icon button to `ToolbarPanel.mls` inside the `.actions` area.

Copy the existing `#share` button pattern:

- add a `handleSettings()` method,
- dispatch `settings-dialog-open-requested`,
- wire the handler in `attachButtonListeners`.

### B0.6 Add Settings tabs

Add tab switching inside the Settings dialog body. Create seven tab buttons with `data-settings-tab`:

- Appearance,
- Editor,
- Workbench,
- Compile & Run,
- Keyboard Shortcuts,
- Data,
- About.

Create seven matching content panels with `data-settings-tab-panel`.

Add `switchTab(id)` to toggle `.active` on both the selected tab and panel. Mirror the existing rail-panel active-class convention documented in `AGENTS.md`. Default to Appearance.

### B0.7 Add base Settings styles

Add CSS for:

- `.settings-dialog-native`,
- `.settings-tabs`,
- `.settings-tab-content`.

Use existing `--ide-*` tokens and the sizing approach used by `.share-dialog-native` and `.project-switcher-native`. Do not introduce a new visual language.

### B0.8 Add canonical Settings row templates

Add one canonical row shape for each row kind.

Toggle row:

```html
<label class="settings-row">
  <span class="settings-row-label">{label}</span>
  <input type="checkbox" class="settings-toggle" data-setting-key="{key}"/>
</label>
```

Select row:

```html
<label class="settings-row">
  <span class="settings-row-label">{label}</span>
  <select class="settings-select" data-setting-key="{key}"></select>
</label>
```

Button row:

```html
<div class="settings-row">
  <span class="settings-row-label">{label}</span>
  <button class="settings-action-button" data-setting-action="{action}">{text}</button>
</div>
```

Static row:

```html
<div class="settings-row settings-row-static">
  <span class="settings-row-label">{label}</span>
  <span class="settings-row-value">{value}</span>
</div>
```

Add one delegated change listener. Changes from `.settings-toggle` and `.settings-select` should call `SettingsStore.setSetting(el.dataset.settingKey, value)`.

### B0.9 Load persisted Settings values into the dialog

Add `loadSettingsIntoDialog()`.

Call it from `openDialog()`. It should:

- find all elements with `data-setting-key`,
- read their stored values with `SettingsStore.getSetting(...)`,
- apply checked state for toggles,
- apply selected value for selects.

This must be generic and reused by all later settings rows.

## Phase 1: Editor and Workbench Settings

Each Phase 1 task should be small because Phase 0 supplies the store, dialog, tabs, and row templates.

### B1.1 Add Editor font-size setting

Add an Editor tab select row using key:

```text
editor.fontSize
```

Reuse the `--editor-font-size` variable from A2. Update `editor.mls` so editor creation applies the stored value.

Expected result: the setting changes editor font size and persists across reload.

### B1.2 Add Editor word-wrap setting

Add an Editor tab toggle using key:

```text
editor.wordWrap
```

When enabled, include CodeMirror's `EditorView.lineWrapping` extension during editor creation.

Expected result: long lines wrap only when the setting is enabled.

### B1.3 Add Editor indentation-guides setting

Add an Editor tab toggle using key:

```text
editor.indentGuides
```

When enabled, include the existing indentation-guide extension. When disabled, omit it.

Do not reimplement indentation guides in this task.

### B1.4 Add Editor show-whitespace setting

Add an Editor tab toggle using key:

```text
editor.showWhitespace
```

When enabled, include `highlightWhitespace()` from `@codemirror/view`.

Expected result: whitespace markers appear only when the setting is enabled.

### B1.5 Add Reset Layout to Default action

Add a Workbench tab button labeled:

```text
Reset Layout to Default
```

The action should clear exactly the layout and filter keys introduced in A5:

- left sidebar width,
- right sidebar width,
- bottom panel height,
- last active bottom tab,
- Problems panel scope,
- Logs level filter,
- Logs source filter.

Reload the app after clearing those keys. Do not clear project or file contents.

### B1.6 Add startup Problems panel setting

Add a Workbench tab toggle using key:

```text
workbench.showProblemsOnStartup
```

Wire it where the right rail's initial open/closed state is set in `IdeWorkbench.mls`.

Expected result: users can choose whether the Problems panel opens on startup.

### B1.7 Add reopen-last-project setting

Add a Workbench tab toggle using key:

```text
workbench.reopenLastProject
```

Inspect `filesystem/projects.mls` to find where the initial project is selected. Make that behavior conditional on the setting.

Expected result: users can disable automatic reopening of the previous project.

## Phase 2: Compile and Run, Keyboard Shortcuts, and About

### B2.1 Add default Problems scope setting

Add a Compile & Run tab select row using key:

```text
problems.defaultScope
```

Options:

- Workspace,
- Current file.

Update `DiagnosticsInspector.mls` so the selected value is used as the initial scope.

### B2.2 Add default Logs level setting

Add a Compile & Run tab select row using key:

```text
logs.defaultLevel
```

Update `BottomPanel.mls` so it uses this setting as the initial `logLevelFilter` instead of hardcoding `"all"`.

Do not add a default source row. Log sources are built dynamically from log entries, so there is no stable option set at startup.

### B2.3 Add Keyboard Shortcuts static list

Add a static list in the Keyboard Shortcuts tab.

Build the list from the shortcuts actually bound in `EditorPanel.mls`'s `handleShortcut` at the time this task is implemented. Do not copy a stale shortcut list from this document.

Expected result: the Settings dialog documents the shortcuts that actually work.

### B2.4 Add About version label

Add a static version label to the About tab.

Use a simple hardcoded string. `manifest.json` has no version field, so do not invent a new version source.

### B2.5 Add About project link

Add a static link to:

```text
https://github.com/hkust-taco/mlscript
```

This URL is confirmed from the repository remote. Do not substitute another project URL.

## Phase 3: Larger Settings Work

These tasks touch broader behavior or visual design. Do them last and review each one more carefully than the earlier Settings tasks.

### B3.1 Add editor-only dark theme setting

Add an Appearance tab toggle for the editor theme only.

When enabled, swap `vscodeLight` to `vscodeDark` from the same `@uiw/codemirror-theme-vscode` package.

This is explicitly not full workbench dark mode. Do not change workbench colors in this task.

### B3.2 Add auto-compile-on-save setting

Add a Compile & Run tab toggle for auto-compile-on-save.

Wire it into `editor.mls`'s `saveOnChange` flow so saving conditionally dispatches `compile-requested`.

This changes program flow, so verify that manual compile still works and that disabled auto-compile does not dispatch compile requests.

### B3.3 Add auto-run-after-compile setting

Add a Compile & Run tab toggle for auto-run-after-compile.

Wire it wherever `compilation-status-change` emits `"done"` in `compiler/index.mls`. When enabled, successful compile completion should dispatch `execute-requested`.

This changes program flow, so verify that manual execute still works and that failed compilation does not auto-run.

### B3.4 Add Reset app to defaults action

Add a Data tab button labeled:

```text
Reset app to defaults
```

Do not implement this as "clear all localStorage." Hardcode the exact list of keys to clear:

- all `settings.*` keys,
- the panel-size and filter keys from A5.

Explicitly exclude any key that stores project contents, file contents, workspace contents, or user-created data.

Require a native `confirm()` before clearing. If the exact key list cannot be confirmed with confidence, skip this task rather than guess.

### B3.5 Reserve full workbench dark mode

Leave the Appearance tab section for full workbench dark mode reserved but empty.

Do not attempt this in an unattended batch. Full workbench dark mode needs actual design input for colors, contrast, and component states.

---

# Recommended Sequencing

1. Complete Part A tasks that are independent and low risk.
2. Complete A2 before B1.1, because B1.1 depends on the editor font-size variable and adjustment behavior.
3. Complete A5 before B1.5, because Reset Layout needs the exact persistence keys.
4. Complete all of Part B Phase 0 before any later Settings task.
5. Complete Phase 1 and Phase 2 Settings rows before Phase 3 behavior changes.
6. Run Part A9 documentation tasks after implementation work, not before.
7. Use A10 only as stretch work after the main plan is stable.

This plan currently contains 72 tasks. If an implementation task is skipped because the code already satisfies it, keep the task number reserved and note the skip in the relevant progress summary.
