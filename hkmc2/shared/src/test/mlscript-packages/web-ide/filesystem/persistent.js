import { createFile, findNode, subscribe } from "./fs.js";

// LocalStorage key prefix for file system
export const FS_PREFIX = "mlscript-fs:";
export const FS_PATHS_KEY = "mlscript-fs-paths";

/**
 * Get the list of persisted file paths from localStorage
 * @returns {Set<string>} Set of file paths
 */
function getPersistedPaths() {
  try {
    const data = localStorage.getItem(FS_PATHS_KEY);
    return data ? new Set(JSON.parse(data)) : new Set();
  } catch (e) {
    console.error("Failed to load persisted paths from localStorage:", e);
    return new Set();
  }
}
/**
 * Save the list of persisted file paths to localStorage
 * @param {Set<string>} paths - Set of file paths
 */
function savePersistedPaths(paths) {
  try {
    localStorage.setItem(FS_PATHS_KEY, JSON.stringify([...paths]));
  } catch (e) {
    console.error("Failed to save persisted paths to localStorage:", e);
  }
}
/**
 * Load a persisted file from localStorage
 * @param {string} path - File path
 * @returns {Object|null} File data or null if not found
 */
function loadPersistedFile(path) {
  try {
    const key = FS_PREFIX + path;
    const data = localStorage.getItem(key);
    return data ? JSON.parse(data) : null;
  } catch (e) {
    console.error("Failed to load file from localStorage:", path, e);
    return null;
  }
}
/**
 * Load all persisted files from localStorage and restore them to the file tree.
 * @returns {number} The number of files restored.
 */
export function loadPersistedFiles() {
  let counter = 0;
  try {
    const paths = getPersistedPaths();
    console.groupCollapsed("Loading persisted files from localStorage");
    for (const path of paths) {
      const fileData = loadPersistedFile(path);
      if (fileData) {
        console.log(`Restoring file: "${path}"`);
        createFile(path, fileData.content, {
          force: true,
          readonly: fileData.readonly,
          attrs: fileData.attrs,
        });

        // Restore timestamps
        const node = findNode(path);
        if (node) {
          node.atime = fileData.atime;
          node.mtime = fileData.mtime;
          node.ctime = fileData.ctime;
          node.birthtime = fileData.birthtime;
        }
        
        counter++;
      }
    }
  } finally {
    console.groupEnd();
  }
  return counter;
}

// Subscribe to file system changes to persist to localStorage
subscribe((event) => {
  const { type, path, node, newPath } = event;

  // Skip standard library files
  if (node?.attrs?.std === true) return;

  try {
    const paths = getPersistedPaths();

    switch (type) {
      case "create":
      case "write":
        if (node?.type === "file") {
          const key = FS_PREFIX + path;
          localStorage.setItem(
            key,
            JSON.stringify({
              content: node.content,
              readonly: node.readonly,
              atime: node.atime,
              mtime: node.mtime,
              ctime: node.ctime,
              birthtime: node.birthtime,
              attrs: node.attrs,
            })
          );
          paths.add(path);
          savePersistedPaths(paths);
        }
        break;

      case "delete":
        if (node?.type === "file") {
          const key = FS_PREFIX + path;
          localStorage.removeItem(key);
          paths.delete(path);
          savePersistedPaths(paths);
        }
        break;

      case "rename":
        if (node?.type === "file") {
          const oldKey = FS_PREFIX + path;
          const newKey = FS_PREFIX + newPath;
          localStorage.removeItem(oldKey);
          localStorage.setItem(
            newKey,
            JSON.stringify({
              content: node.content,
              readonly: node.readonly,
              atime: node.atime,
              mtime: node.mtime,
              ctime: node.ctime,
              birthtime: node.birthtime,
              attrs: node.attrs,
            })
          );
          paths.delete(path);
          paths.add(newPath);
          savePersistedPaths(paths);
        }
        break;

      case "attr":
      case "readonly":
        if (node?.type === "file") {
          const key = FS_PREFIX + path;
          localStorage.setItem(
            key,
            JSON.stringify({
              content: node.content,
              readonly: node.readonly,
              atime: node.atime,
              mtime: node.mtime,
              ctime: node.ctime,
              birthtime: node.birthtime,
              attrs: node.attrs,
            })
          );
          // No need to update paths list for metadata changes
        }
        break;
    }
  } catch (e) {
    console.error("Failed to persist file system change to localStorage:", e);
  }
});
