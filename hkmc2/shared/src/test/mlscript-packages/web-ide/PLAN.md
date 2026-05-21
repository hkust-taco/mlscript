# Web IDE Plan

This document tracks the current Web IDE UI modernization work. Keep it updated
when adding, completing, hiding, or intentionally deferring UI behavior.

## Completed

- Reworked the application shell around native custom elements:
  `<ide-workbench>`, `<toolbar-panel>`, `<editor-workbench>`,
  `<file-explorer>`, `<search-panel>`, `<outline-panel>`,
  `<diagnostics-inspector>`, `<bottom-panel>`,
  `<command-palette-dialog>`, and `<share-dialog>`.
- Moved sidebars to persistent activity rails with collapsible, resizable
  panels.
- Fixed sidebar collapse after resize for left and right panels.
- Kept resize handles scoped above the bottom panel so they no longer overlay
  console content.
- Fixed editor and file list scrollability with the bottom panel visible.
- Disabled Compile and Execute when no active file is open.
- Prevented Compile from compiling non-`.mls` files.
- Made Execute unfold the Output panel before output appears.
- Changed the document title and OpenGraph title to `MLscript Web IDE`.
- Removed the standard-library edit lock so std files can be edited in the Web
  IDE.
- Replaced the old Diagnostics status-bar toggle with a right-rail Problems
  panel.
- Removed the bottom Problems tab and moved real compiler diagnostics to the
  Problems sidebar.
- Added a Problems empty state and real diagnostics rendering.
- Changed Problems to display diagnostics for all workspace `.mls` files from
  each compile request instead of only the active file.
- Improved the Problems panel narrow-width layout.
- Hid Source Control on the left rail, keeping source code for later.
- Hid Examples on the left rail, keeping source code for later.
- Hid Terminal and Generated bottom panels, keeping source code where useful for
  future work.
- Implemented grouped global search in the left sidebar:
  summary counts, file groups, occurrence counts, folding, per-occurrence rows,
  exact occurrence navigation, responsive snippets, and search-term highlights.
- Removed browser search input clear styling.
- Implemented centered native dialogs with dimmed backdrops and dismissible
  backdrop clicks.
- Implemented the Share dialog download actions:
  all files ZIP, MLscript-only ZIP, and JavaScript-only ZIP.
- Improved the command palette:
  centered position, fixed input, max height, smaller entries, inline
  descriptions, keyboard navigation, and Enter confirmation.
- Added centralized Logs in the bottom panel:
  bounded log buffer, compact one-line rows, folded body previews, formatted
  time, level/source filters, time sort, and auto-scroll.
- Routed Web IDE logging through `common/Logger.mls` and worker internal-log
  messages.
- Added real outline analysis through the analysis worker and compiler analysis
  API.
- Removed outline mock fallback. The outline now shows real symbols or a clear
  unavailable/error state.
- Added command-palette symbol navigation using the analysis symbol index.
- Refined outline presentation:
  symbol kind colors, badges, type/pattern icons, shorter `L5` locations,
  reduced indentation, child guide rule, monospace symbol names, and exact
  outline navigation.
- Merged `web-ide-features/outline-view` into `web-ide`.
- Verified recent focused changes with:

  ```sh
  sbt --client "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"
  ```

- Verified the outline integration against the browser preview and ran the full
  suite after the outline merge:

  ```sh
  sbt --client hkmc2AllTests/test
  ```

## In Progress

- Converging the Outline panel visual density and symbol taxonomy.
- Keeping package-local agent documentation current as the Web IDE diverges from
  the rest of the repository.
- Reducing remaining prototype/mock surfaces before the UI is considered
  shippable.

## Mock And Deferred UI List

Every new non-functional UI element must be added here when introduced and
removed when implemented or deleted.

- Source Control panel:
  currently hidden/commented from the left rail. Source files remain because the
  feature is expected to return later.
- Terminal panel:
  currently hidden from the bottom panel. Source may remain for later, but it is
  not part of the current shipped UI.
- Generated panel:
  currently hidden because the supported flow is compile to JavaScript and view
  or edit generated `.mjs` files directly.
- Examples panel:
  currently hidden/commented from the left rail. Source files remain because the
  feature may return with real curated examples later.
- `mockWorkbenchData.mls`:
  legacy prototype data. Do not wire it into production-facing panels.

## Left For Future

- Restore Examples only with real curated examples.
- Restore Source Control with real repository or workspace integration.
- Restore Terminal only when there is a real execution model and command set.
- Add a first-class generated-output experience only if it improves on direct
  generated `.mjs` tabs.
- Add automated browser regression coverage for the most important UI flows
  instead of relying only on manual Playwright smoke checks.
- Strengthen outline symbol coverage as the compiler analysis API evolves.
- Improve command palette command coverage beyond file and symbol navigation.
- Add persistent user preferences for panel sizes, active tabs, and log filters
  where not already persisted.
- Audit all remaining uses of mock/prototype naming and remove any that are
  visible to users.
- Keep `README.md`, `AGENTS.md`, and this `PLAN.md` synchronized with the actual
  package workflow.

## Standard Verification Checklist

Run this before committing Web IDE behavior changes:

```sh
sbt --client "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"
git diff --check
git status --short
```

For UI changes, also verify in a browser using the active preview server when
one is available. Current common preview URL:

```text
http://127.0.0.1:3003/index.html
```

For broad compiler, runtime, analysis, vendoring, or generated-output changes,
run:

```sh
sbt --client hkmc2AllTests/test
```

