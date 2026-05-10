import * as MLscript from "./build/MLscript.mjs";
import fs from "./filesystem/fs.mjs";
import persistent from "./filesystem/persistent.mjs";
import runner from "./execution/runner.mjs";
import { compile } from "./compiler/index.js";

try {
  console.groupCollapsed(`Loading standard library files`);
  // This `collapsed` attribute make sure that the standard library folder is
  // initially collapsed in the file explorer.
  fs.createFolder("/std", { force: true, attrs: { collapsed: true } });
  
  // Mark standard library files as they will not be persisted.
  fs.createFile("/std/Prelude.mls", MLscript.std.prelude, {
    force: true,
    readonly: true,
    attrs: { std: true, compiled: true },
  });
  
  MLscript.std.files.forEach(([filePath, content]) => {
    console.log(`Loading file: "${filePath}"`);
    fs.createFile(filePath, content, {
      force: true,
      readonly: true,
      attrs: { std: true, compiled: true },
    });
  });
} finally {
  console.groupEnd();
}

// Load persisted user files from localStorage.
if (persistent.loadPersistedFiles() === 0) {
  fs.createFile("/main.mls", `import "./std/Predef.mls"

open Predef

print of "Welcome to MLscript Web IDE!"
print of "============================"

print of "Press Ctrl-S to compile."
print of "Press Ctrl-E to execute."
`, { force: true })
}

/**
 * Collect all MLscript files for compilation and determine target files.
 * @param {string} targetPath the file path that triggered the compile request
 */
function collectFilesForCompilation(targetPath) {
  const files = fs.getAllFiles((path) => path.endsWith(".mls") || path.endsWith(".mjs"));
  const targetPaths = new Set(
    Object.keys(files).filter((p) => {
      const node = fs.stat(p);
      if (!p.endsWith(".mls")) return false;
      if (node?.attrs?.std) return false;
      return node?.attrs?.compiled !== true;
    })
  );
  if (targetPath) targetPaths.add(targetPath);
  return [files, Array.from(targetPaths)];
}

/**
 * Mark specified files as compiled.
 * @param {string[]} filePaths paths to the files
 */
function markAsCompiled(filePaths) {
  filePaths.forEach((p) => {
    const node = fs.stat(p);
    if (!node?.attrs?.std) {
      fs.setAttr(p, "compiled", true);
    }
  })
}

// Global compile event listener
document.addEventListener("compile-requested", (e) => {
  const targetPath = e.detail.filePath;
  const [allFiles, targetPaths] = collectFilesForCompilation(targetPath);

  compile(targetPaths, allFiles).then(({ result: diagnosticsPerFile }) => {
    markAsCompiled(targetPaths);
    const reservedPanel = document.querySelector('reserved-panel');
    if (reservedPanel) {
      reservedPanel.setDiagnostics(diagnosticsPerFile);
    }
  });
});

document.addEventListener("execute-requested", async function (event) {
  let { filePath } = event.detail;
  if (typeof filePath !== "string") {
    // This should not happen, but just in case.
    console.error("Invalid file path for execution:", filePath);
    return;
  }
  const mjsFilePath = filePath.replace(/\.mls$/, ".mjs");
  if (fs.pathExists(mjsFilePath)) {
    runner.execute(mjsFilePath);
  } else {
    // If the compiled file does not exist, we first compile it.
    // TODO: Show this message using a toast notification.
    console.warn("Compiled file not found, compiling first:", mjsFilePath);
    const [allFiles, targetPaths] = collectFilesForCompilation(filePath);

    compile(targetPaths, allFiles).then(() => {
      markAsCompiled(targetPaths);
      if (fs.pathExists(mjsFilePath)) {
        runner.execute(mjsFilePath);
      } else {
        // TODO: Show this error message using a toast notification.
        console.error(
          "Compiled file not found after compilation:",
          mjsFilePath
        );
      }
    });
  }
});

document.addEventListener("terminate-requested", () => runner.terminate());

// Handle navigation to file location from diagnostics
document.addEventListener("open-file-at-location", (e) => {
  const { filePath, line } = e.detail;
  const editorPanel = document.querySelector('editor-panel');
  if (editorPanel) {
    editorPanel.openFileAtLine(filePath, line);
  }
});
