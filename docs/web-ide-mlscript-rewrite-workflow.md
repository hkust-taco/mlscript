# Web IDE MLscript Rewrite Workflow

This workflow is for LLM agents rewriting the remaining Web IDE JavaScript
modules under `hkmc2/shared/src/test/mlscript-packages/web-ide` into MLscript.

## Principles

- Rewrite one module boundary at a time.
- Preserve the JavaScript module contract first: exported names, default export
  shape, callbacks, events, error behavior, and import paths.
- Treat the existing JavaScript file as the behavior spec.
- Keep commits scoped to one conceptual change.
- Do not reformat unrelated whitespace or blank lines.

## Steps

1. Pick a small boundary.
   Prefer leaf modules or modules with already-ported callers. Read the target
   JavaScript file and every direct caller before writing MLscript.

2. Port the implementation.
   Add a `.mls` file next to the old `.js` file. Follow existing Web IDE
   MLscript style: UCS conditionals, conjunctive `and` guards, direct declared
   globals when possible, and shared helpers such as `common/JS.mls`.

3. Keep browser APIs explicit.
   If the port needs a browser or JavaScript global, add the smallest useful
   declaration to `hkmc2/shared/src/test/mlscript/decls/Prelude.mls`. Use
   `globalThis` only when MLscript/codegen cannot express the access, and leave
   a short comment explaining why.

4. Switch imports deliberately.
   After package compilation generates the `.mjs`, update callers from the old
   `.js` module to the generated `.mjs`. Delete the old `.js` file only after
   the generated module is actually used.

5. Run package verification.
   Run:

   ```sh
   timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"
   ```

   Check `git status` afterward. Generated `.mjs` files and generated
   `vendors/` output should stay untracked.

6. Run a browser smoke test.
   Start a static server from the Web IDE package directory:

   ```sh
   cd hkmc2/shared/src/test/mlscript-packages/web-ide
   python3 -m http.server 8123 --bind 127.0.0.1
   ```

   Open `http://127.0.0.1:8123/index.html?<cache-buster>`, then verify:

   - initial page load has no browser console errors;
   - default `main.mls` is visible;
   - Compile works and produces the normal compiler output;
   - Execute works and the worker runs;
   - the browser console still has no errors afterward.

   Also test one behavior owned by the rewritten module, for example:

   - filesystem: create, rename, delete, read, and list files;
   - persistence: create a file, reload, and confirm it survives;
   - runner: compile first, then execute through the rewritten runner;
   - compiler: compile through the rewritten compiler client or worker;
   - UI component: perform the hover, click, input, or focus action it owns.

7. Run broader verification when needed.
   Run `timeout 1500s sbt hkmc2AllTests/test` before committing if the change
   touches shared compiler behavior, `Prelude.mls`, module resolution, codegen,
   package vendoring, or golden-test-visible behavior.

8. Commit only reviewed output.
   Review `git diff`, run `git diff --check`, and keep any golden snapshot
   rewrites only when they are intentional. Use a one-line commit message.

## Style Notes

- Do not write `else if`; use Ultimate Conditional Syntax.
- Prefer `if value is ~Absent and ...` over nested null checks.
- Do not recreate local `isAbsent` helpers; import the shared `Absent` pattern.
- Prefer direct declarations from `Prelude.mls` over `globalThis`.
- Do not remove existing `end` markers.
- Do not use `asInstanceOf` unless there is no reasonable typed alternative.
