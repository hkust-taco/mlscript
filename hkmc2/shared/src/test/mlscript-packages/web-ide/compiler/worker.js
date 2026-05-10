// Compiler Web Worker
import * as MLscript from "../build/MLscript.mjs";

let compiler = null;
let filesStore = {};

/** Maintain a set of modified paths. @type {Set<string>} */
let modifiedFiles = new Set();
let fileTimestamps = {};
let timestamp = 0;

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
      fileTimestamps[path] = ++timestamp;
      modifiedFiles.add(path);
    },

    exists(path) {
      return path in filesStore;
    },

    getLastChangedTimestamp(path) {
      return fileTimestamps[path] ?? 0;
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
      "/std/Term.mjs",
      "/std"
    );
    
    compiler = new MLscript.BrowserCompiler(dummyFileSystem, paths);
  }
}

self.addEventListener("message", function (e) {
  const {
    type,
    payload: { id, allFiles, filePaths },
  } = e.data;

  if (type === "compile") {
    try {
      filesStore = allFiles;
      fileTimestamps = Object.fromEntries(Object.keys(filesStore).map((path) => [path, 0]));
      modifiedFiles.clear();
      compiler = null;
      initializeCompiler();

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
