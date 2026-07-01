# Web IDE MLscript Second-Pass Workflow

This workflow is for improving the already-rewritten Web IDE MLscript files
after the first JavaScript-to-MLscript port. The goal is idiomatic MLscript,
not another behavior rewrite.

## Inputs

- Use `docs/idomatic-mlscript-rules.md` as the rule list.
- Treat the current Web IDE behavior as fixed unless a bug is explicitly in
  scope.
- Preserve existing whitespace style, including blank-line indentation.

## Rewrite Loop

1. Pick one idiom rule.
   Prefer one checklist item from `docs/idomatic-mlscript-rules.md`.

2. Apply it to one small file first.
   This keeps syntax, type, and style problems easy to inspect.

3. Compile the package.
   Run:

   ```sh
   timeout 300s sbt "hkmc2PackagesTest/testOnly hkmc2.PackageTestRunner -- -z web-ide"
   ```

4. Expand the same rule to other relevant files.
   Keep the pass scoped to that rule unless a nearby small cleanup is required
   for the same rewrite.

5. Check the diff.
   Run:

   ```sh
   git diff --check
   git status --short
   ```

   No golden snapshots or unrelated test files should change.

6. Run browser verification.
   Prefer a headless browser so the user's desktop is not disturbed. Start a
   local server from the Web IDE package directory:

   ```sh
   cd hkmc2/shared/src/test/mlscript-packages/web-ide
   python3 -m http.server 8123 --bind 127.0.0.1
   ```

   Open `http://127.0.0.1:8123/index.html?<cache-buster>` and verify:

   - the page loads without browser console errors;
   - files are visible in the explorer;
   - a source file opens in the editor;
   - Compile still works;
   - Execute still works;
   - the specific UI or runtime behavior touched by the rewrite still works.

7. Run broader tests when needed.
   If the pass touches shared compiler behavior, `Prelude.mls`, package
   vendoring, module resolution, generated JavaScript shape, or golden-test
   output, run:

   ```sh
   timeout 1800s sbt hkmc2AllTests/test
   ```

8. Update the checklist.
   Mark completed rules in `docs/idomatic-mlscript-rules.md`.

9. Commit the pass.
   Use a short one-line commit message with no body. Prefer one commit per
   idiom rule; use one commit per file only when the change is risky.

## Commit Shape

- Cross-file mechanical cleanup: one rule, one commit.
- Single-file polish: one coherent group, one commit.
- Risky behavior change: isolate it in its own commit.

