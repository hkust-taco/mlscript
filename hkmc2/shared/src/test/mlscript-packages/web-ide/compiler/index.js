import * as fs from "../filesystem/fs.js";

// We put the compiler on the worker as well because the MLscript compiler takes
// more time when handling multiple files. If it runs directly here, it would
// block the user interface from updating.
const compilerWorker = new Worker("/compiler/worker.js", { type: "module" });

/** @type {Map<string, { resolve: Function, reject: Function }>} */
const callbackMap = new Map();

compilerWorker.addEventListener("message", function (e) {
  console.log("[Compiler Worker] Message received:", e.data);
  
  if (e.data.type === "compile-success") {
    const { result, changes } = e.data;
    const diagnostics = result?.diagnostics ?? result;
    const compiledFiles = result?.compiledFiles ?? [];
    console.log("[Compiler] Result:", diagnostics);

    // Apply file changes to main file system
    for (const [path, content] of Object.entries(changes)) {
      fs.write(path, content);
    }
    // Mark compiled sources as up-to-date
    compiledFiles
      .filter((path) => typeof path === "string" && path.endsWith(".mls"))
      .forEach((path) => fs.setAttr(path, "compiled", true));

    // Dispatch compilation completed event
    const doneEvent = new CustomEvent("compilation-status-change", {
      detail: { status: "done" },
    });
    document.dispatchEvent(doneEvent);

    // Resolve the promise
    const callbacks = callbackMap.get(e.data.id);
    if (callbacks === undefined) {
      console.error("[Compiler] No callback found for id:", e.data.id);
    } else {
      callbacks.resolve({ result: diagnostics, changes });
    }
  } else if (e.data.type === "compile-error") {
    const { name, message, stack } = e.data;
    console.error(`[Compiler] ${name}: ${message}`);
    console.error(stack);

    // Dispatch compilation error event
    const errorEvent = new CustomEvent("compilation-status-change", {
      detail: { status: "error" },
    });
    document.dispatchEvent(errorEvent);

    // Reject the promise
    const callbacks = callbackMap.get(e.data.id);
    if (callbacks === undefined) {
      console.error("[Compiler] No callback found for id:", e.data.id);
    } else {
      callbacks.reject(Object.assign(new Error(message), { name, stack }));
    }
  } else {
    console.warn("[Compiler Worker] Unknown message type:", e.data.type);
  }
});

compilerWorker.addEventListener("error", function (error) {
  console.error("[Compiler Worker] Worker error:", error);
});

/**
 * Compile the given MLscript files using the compiler worker.
 *
 * Currently, we also need to pass all compiler-visible `.mls` and `.mjs` files
 * to the worker because there is no simple way to share the file system between
 * the main thread and the worker. The current approach works even when the
 * number of files is not too large.
 *
 * Calling this function will also dispatch compilation status change events:
 * - `"running"` when compilation starts,
 * - `"done"` when compilation succeeds, and
 * - `"error"` when compilation fails.
 * Therefore, the caller does not need to dispatch these events manually.
 *
 * The updated files upon successful compilation will also be written back to
 * the file system automatically. Therefore, the caller does not need to handle
 * file updates manually.
 *
 * @param {string[]} filePaths the list of file paths to compile
 * @param {Record<string, string>} allFiles
 *    all compiler-visible source and JavaScript module files in the file system
 * @returns {Promise<{ result: string, changes: Record<string, string> }>}
 *    compilation result and changed files
 */
export async function compile(filePaths, allFiles) {
  return new Promise((resolve, reject) => {
    // Dispatch compilation started event.
    const startEvent = new CustomEvent("compilation-status-change", {
      detail: { status: "running" },
    });
    document.dispatchEvent(startEvent);
    const id = makeUniqueID();
    // Send compile request to the worker.
    compilerWorker.postMessage({
      type: "compile",
      payload: { id, filePaths, allFiles },
    });
    // Push the callbacks to the queue.
    callbackMap.set(id, { resolve, reject });
  });
}

function makeUniqueID() {
  const nonce = (~~(Math.random() * 0xFFFF)).toString(16).padStart(4, '0');
  return `${new Date().toISOString()}_${nonce}`;
}
