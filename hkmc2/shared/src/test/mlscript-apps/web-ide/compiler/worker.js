// Compiler Web Worker
import * as MLscript from "../build/MLscript.mjs";

let compiler = null;
let filesStore = {};

/** Maintain a set of modified paths. @type {Set<string>} */
let modifiedFiles = new Set();

function createVirtualFileSystem() {
  return {
    read(path) {
      if (path in filesStore) {
        return filesStore[path];
      }
      throw new Error(`File not found: ${path}`);
    },

    write(path, content) {
      filesStore[path] = content;
      modifiedFiles.add(path);
      return true;
    },

    exists(path) {
      return path in filesStore;
    },
  };
}

function initializeCompiler() {
  if (!compiler) {
    const virtualFS = createVirtualFileSystem();
    const dummyFileSystem = new MLscript.DummyFileSystem(virtualFS);
    
    // We assume that three standard library files are always present.
    const paths = new MLscript.Paths(
      "/std/Prelude.mls",
      "/std/Runtime.mjs",
      "/std/Term.mjs"
    );
    
    compiler = new MLscript.Compiler(dummyFileSystem, paths);
  }
}

self.addEventListener("message", function (e) {
  const {
    type,
    payload: { id, allFiles, filePaths },
  } = e.data;

  if (type === "compile") {
    try {
      initializeCompiler();
      
      filesStore = allFiles;

      modifiedFiles.clear();

      const diagnosticsPerFile = [];
      for (const filePath of filePaths) {
        diagnosticsPerFile.push(...compiler.compile(filePath));
      }
      
      const changes = {};
      for (const path of modifiedFiles) {
        changes[path] = filesStore[path];
      }

      self.postMessage({
        type: "compile-success",
        id,
        result: { diagnostics: diagnosticsPerFile, compiledFiles: filePaths },
        changes,
      });
    } catch (error) {
      self.postMessage({
        type: "compile-error",
        id,
        name: error.name,
        message: error.message,
        stack: error.stack,
      });
    }
  } else {
    self.postMessage({
      type: "error",
      error: `Unknown message type: ${type}`,
    });
  }
});
