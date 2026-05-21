# Web IDE Agent Guide

This package is the MLscript Web IDE. It is unusual in this repository because
the application source is written in MLscript, compiled to browser JavaScript,
and then served as a static web app. Most agents have not seen MLscript before:
read this file before editing anything in this package.

## First Rules

- Edit `.mls` files as source of truth. The adjacent `.mjs` files are generated
  package outputs.
- Do not hand-edit generated `.mjs` files unless the user explicitly asks for a
  generated-output investigation. If tests regenerate them, review and commit
  the expected generated changes.
- Preserve indentation whitespace and blank lines. Empty lines in this
  repository are often intentional.
- Keep changes scoped. This package is UI-heavy and event-driven; broad
  refactors can easily break browser behavior.
- Do not display fake or mock data in production UI. If a real subsystem is not
  available, show a clear empty or unavailable state.
- Do not add React, Vue, Svelte, or another frontend framework. The Web IDE uses
  native custom elements, browser events, workers, dialogs, CSS, and MLscript.
- Prefer one commit per fix or small coherent UI pass.

## Package Location

The package root is:

```sh
hkmc2/shared/src/test/mlscript-packages/web-ide
```

Run repository-level commands from the repository root unless a command
explicitly says to `cd` into this package.

## Source Layout

- `index.html`: static entry point. It imports generated component `.mjs` files,
  `style.css`, the Lucide icon font, and `main.mjs`.
- `style.css`: all current UI styling. It owns the workbench grid, rails,
  sidebars, bottom panel, dialogs, editor chrome, search, problems, logs, and
  outline presentation.
- `main.mls`: browser bootstrap. It loads the compiled MLscript compiler bundle,
  loads standard library files into the in-browser filesystem, creates the
  default `/main.mls`, starts outline analysis, and wires compile/execute/open
  events.
- `filesystem/`: in-memory and persisted browser filesystem.
  - `fs.mls`: file tree operations and filesystem events.
  - `persistent.mls`: local persistence for user files.
- `compiler/`: compile worker front end.
  - `index.mls`: browser-side compiler worker API.
  - `worker.mls`: worker-side compilation entry.
- `execution/`: sandboxed JavaScript execution.
  - `runner.mls`: browser-side execution API.
  - `worker.mls`: worker-side execution runtime.
- `analysis/`: outline and command-palette symbol analysis.
  - `index.mls`: analysis worker lifecycle, filesystem change batching, active
    file tracking, symbol index events, and test hooks.
  - `worker.mls`: worker-side calls into the compiler analysis API.
  - `SymbolTree.mls`: normalizes symbol documents, ranges, expansion keys, and
    navigation details.
- `common/`: shared browser utilities.
  - `JS.mls`: helpers for JavaScript interop and missing values.
  - `Logger.mls`: centralized logging event emitter.
- `components/`: custom elements. Each file usually registers one custom element
  with `customElements.define`.
- `mockWorkbenchData.mls`: legacy prototype data. Do not use it for production
  behavior. When a mock-only panel is hidden or retained for future work,
  document that in `PLAN.md`.
- `vendors/std/` and `mlscript-std/` outputs: standard library assets used by
  the package tests and browser runtime.
- `build/`: ignored local compiler bundle output. It normally contains
  `MLscript.mjs` copied from the Scala.js build.

## Current UI Architecture

The app is a static document containing `<ide-workbench>`.

`IdeWorkbench.mls` renders the main shell:

- top toolbar: `<toolbar-panel>`;
- left activity rail and panels: Files, Search, Outline, Examples, with Source
  Control currently hidden/commented;
- center editor: `<editor-workbench>`;
- right rail and panel: Problems via `<diagnostics-inspector>`;
- bottom panel: `<bottom-panel>` for Output and Logs;
- status bar;
- native custom elements for command palette and share dialogs.

Panels are switched by rail buttons using `data-sidebar-side` and
`data-sidebar-panel`. The active panel receives the `active` class and is not
hidden. Resize handles target the active sidebar panel.

The bottom panel follows the same mental model as the side rails: clicking the
active tab folds it, clicking a different tab switches it. The old separate
collapse button was removed.

## Browser Event Contracts

The package is intentionally decoupled through DOM events. Before changing a
component, search for both dispatchers and listeners.

Important events:

- `compile-requested`: toolbar/editor shortcut asks `main.mls` to compile the
  active `.mls` file.
- `execute-requested`: toolbar/editor shortcut asks `main.mls` to execute. The
  output panel should unfold before execution output appears.
- `terminate-requested`: asks the execution runner to stop.
- `open-file-at-location`: opens a file in the editor and selects the requested
  line/column/range.
- `active-tab-changed`: editor announces the active file path; workbench status
  and analysis listen to it.
- `compilation-status-change`: compiler status updates the toolbar/workbench.
- `execution-status-change`: runner status updates the toolbar/workbench.
- `analysis-document-updated`: outline receives the active file symbol tree.
- `analysis-status-changed`: outline receives loading/error/ready status.
- `analysis-symbol-index-updated`: command palette receives workspace symbols.
- `web-ide-log`: centralized log entries consumed by the Logs tab.
- `sidebar-toggle-requested`: components can ask the workbench to fold/unfold a
  side panel.

## Error Surfacing Contracts

User-visible errors must not disappear into logs only. When touching compile,
execute, workers, diagnostics, toolbar status, or logs, preserve these contracts.

Compile diagnostics:

- ordinary compiler diagnostics are stored in the Problems sidebar through
  `diagnostics-inspector.setDiagnostics(...)`;
- the Problems sidebar shows workspace-wide diagnostics by default and can scope
  to the current file;
- non-`.mls` files must not be compiled by the Compile button.

Fatal compiler failures:

- compiler worker internal failures are reported by `compiler/index.mls` as
  `compilation-status-change` with status `fatal`;
- `main.mls` converts those failures into an `internal` Problems entry with
  source `compiler`;
- the center toolbar/workbench indicator must show `Fatal error`;
- the bottom panel must switch to Logging and record the fatal payload.

Execution failures:

- `main.mls` executes the compiled `.mjs` path but also passes the source path to
  `execution/runner.mls`;
- `execution/worker.mls` should report runtime failures as structured
  `runtime-error` messages with `name`, `message`, and `stack`;
- `execution/runner.mls` converts runtime failures into an `error` Problems
  entry with source `execution`;
- that Problems entry should name both the culprit source file, for example
  `/std/CSP.mls`, and the executed module, for example `/std/CSP.mjs`;
- Execute should unfold Output, and execution failures should be visible there
  immediately as well as in centralized Logging.

## MLscript Notes For New Agents

MLscript here compiles to JavaScript modules, so most code uses browser globals
directly. A few syntax patterns appear everywhere:

```mlscript
import "./common/JS.mls"

open JS { Absent }

module Logger with...

fun message(text) =
  "Hello " + text

class MyElement extends HTMLElement with
  let
    value = null

  fun connectedCallback() =
    this.render()

  fun render() =
    set this.innerHTML = "<div>Ready</div>"
```

Common idioms:

- `fun name(args) = ...` defines a function.
- `let` introduces local bindings. A multi-line `let` block is common before an
  expression.
- `mut { key: value }` creates a mutable JavaScript-like object.
- `set target = value` mutates an existing binding or property.
- `if value is "x" then ... else ...` is pattern matching, not JavaScript
  equality syntax.
- `Absent` is used for missing JavaScript fields. Many checks look like
  `field is Absent then ...`.
- `~Absent as value` means "present, bind it as value".
- JavaScript property names that are reserved words are quoted, for example
  `event.'type`.
- Rest parameters are written as `...body`.
- DOM APIs such as `document.querySelector`, `new CustomEvent`, `new Worker`,
  `window.setTimeout`, and `customElements.define` are used directly.

Style constraints from the repository still apply here:

- Do not use `asInstanceOf` unless there is no reasonable alternative.
- Do not introduce default arguments in core business logic.
- Do not remove existing `end` markers in files that use them.

## Generated Files And Build Outputs

The package test runner compiles `.mls` files to adjacent `.mjs` files. This is
why most source files have a generated sibling:

```text
components/OutlinePanel.mls
components/OutlinePanel.mjs
```

The source file is the `.mls` file. The generated `.mjs` file may change after
running the package tests. If the test runner updates generated output, inspect
the diff and commit it when it is expected.

The browser compiler bundle is separate:

```text
build/MLscript.mjs
build/MLscript.mjs.map
```

This directory is ignored local runtime output. To refresh it for a browser
preview, run the Scala.js build and copy the output:

```sh
sbt --client hkmc2JS/fullOptJS
cp hkmc2/js/target/scala-3.8.3/hkmc2-opt/MLscript.mjs \
  hkmc2/shared/src/test/mlscript-packages/web-ide/build/MLscript.mjs
cp hkmc2/js/target/scala-3.8.3/hkmc2-opt/MLscript.mjs.map \
  hkmc2/shared/src/test/mlscript-packages/web-ide/build/MLscript.mjs.map
```

Use the exact Scala version path present in the local build if it changes.

## CLI Test Workflow

Prefer `sbt --client` after the sbt server is running. SBT startup is slow.

For most Web IDE-only changes, run:

```sh
sbt --client "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"
```

This compiles the `web-ide` MLscript package and runs the focused package test
suite. It is the default check for component, style, package, analysis, compiler
front-end, and UI event changes.

For broader compiler/runtime changes, first make sure runtime test assets are
generated:

```sh
sbt --client hkmc2JVM/test
```

Before finishing a substantial or risky change, run the full test suite:

```sh
sbt --client hkmc2AllTests/test
```

If golden or generated test output changes, inspect it and commit the expected
updates. CI can fail when generated test output is stale.

Always run diff hygiene before committing:

```sh
git diff --check
git status --short
```

Unrelated dirty files are common in this repository. Do not revert them.

## Browser Verification Workflow

CLI tests are not enough for UI work. Use a browser check for any change that
affects layout, custom elements, dialogs, sidebars, panels, editor interaction,
search, outline, diagnostics, logs, compile, execute, or worker behavior.

If the user has an existing preview server, use it. In recent UI work the shared
preview has often been:

```text
http://127.0.0.1:3003/index.html
```

Do not start another server when the user says a preview server is already
running.

The Web IDE preview workflow deploys to Cloudflare only when both
`CLOUDFLARE_API_TOKEN` and `CLOUDFLARE_ACCOUNT_ID` are configured in the
repository where the workflow runs. Forks need their own Actions secrets; the
upstream repository's secrets are not inherited by fork push workflows.

If no server exists and the user has not prohibited starting one, serve the
package root:

```sh
cd hkmc2/shared/src/test/mlscript-packages/web-ide
python3 -m http.server 8123 --bind 127.0.0.1
```

Then open:

```text
http://127.0.0.1:8123/index.html?<cache-buster>
```

Browser smoke checks for most UI changes:

- page title is `MLscript Web IDE`;
- page loads with no browser console errors;
- Files panel opens and can open `/main.mls`;
- editor content is scrollable;
- left and right rails can show, hide, and switch panels;
- resize handles only affect the visible side panel area;
- Compile is disabled when there is no active file and skips non-`.mls` files;
- Compile on `/main.mls` updates Problems with real diagnostics or an empty
  state;
- fatal compiler failures show `Fatal error` in the toolbar, populate Problems
  as `Internal`, and switch the bottom panel to Logging;
- Execute unfolds Output and shows output in order;
- execution runtime errors, including std-file execution failures such as
  `/std/CSP.mls`, populate Problems with the culprit source path and executed
  module path;
- Logs tab receives centralized log entries and auto-scrolls when appropriate;
- Search results are grouped by file, highlight the selected occurrence, fold by
  file, and open the exact occurrence;
- Outline shows real symbols or a clear unavailable state, never mock symbols;
- command palette is centered, keyboard navigable, and keeps the input fixed;
- share dialog remains centered and provides the configured download buttons;
- desktop and narrow viewports do not horizontally overflow.

Use browser-side test hooks where available:

- `window.__mlscriptAnalysis.analyzeNow()`;
- `window.__mlscriptAnalysis.injectResponse(response)`;
- `window.__mlscriptAnalysis.symbolIndex()`;
- `analysis-test-inject-response` events for analysis worker scenarios.

When using Playwright tools, remove `.playwright-mcp/` artifacts before
committing unless the user explicitly asks to keep screenshots or snapshots.

## Implementation Guidelines

### Custom Elements

Each component should own its DOM subtree and event listeners. Keep the public
surface small: methods such as `setDiagnostics`, `showOutput`, or `openFileAtLine`
are acceptable when another component needs a direct imperative entrypoint.

Use native HTML where practical:

- `<dialog>` for modal dialogs;
- `<button>` for commands;
- `<details>/<summary>` for foldable tree groups when it fits;
- form controls for inputs, filters, toggles, and selectors.

### Styling

Use the design tokens in `:root` before introducing new colors or dimensions.
Important tokens include:

- `--monospace`;
- `--sans-serif`;
- `--ide-bg`;
- `--ide-surface`;
- `--ide-border`;
- `--ide-text`;
- `--ide-text-muted`;
- `--ide-accent`;
- z-index tokens such as `--z-tooltip`.

Avoid one-off decorative effects. Keep tool surfaces dense, readable, and close
to the established IDE style.

### Logging

Do not use `console.log` as product logging. Route user-visible and diagnostic
logs through `common/Logger.mls`:

```mlscript
Logger.info("Compiler", "Compilation finished", path)
Logger.warn("Execution", "Compiled file not found, compiling first", mjsPath)
Logger.error("Analysis", "Analysis worker error", error)
```

The Logs tab consumes `web-ide-log` events and renders level, time, source,
message, and body.

### Mocks

New non-functional UI must be recorded in `PLAN.md` under the mock list. Prefer
not adding mocks at all. If a feature cannot be implemented now, render an empty
state or an unavailable explanation instead of fake content.

Known intentionally deferred surfaces should stay hidden/commented when they are
not ready to ship.

## Common Pitfalls

- Editing `.mjs` instead of `.mls`.
- Forgetting that `build/MLscript.mjs` is ignored local runtime state.
- Trusting package tests alone for CSS or interaction changes.
- Adding mock data because a worker or compiler API is unavailable.
- Starting a second preview server when the user already has one.
- Reverting unrelated dirty files.
- Removing blank lines while touching nearby code.
- Letting browser-generated `.playwright-mcp/` files enter the commit.

