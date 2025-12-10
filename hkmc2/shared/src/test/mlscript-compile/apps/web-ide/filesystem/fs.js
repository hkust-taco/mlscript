// Virtual File System for MLscript Web Demo

// File tree structure - moved from main.js
// const now = Date.now();

export const fileTree = [
  // Example file data type:
  // {
  //   name: "main.mls",
  //   type: "file",
  //   content: "",
  //   readonly: false,
  //   atime: now,
  //   mtime: now,
  //   ctime: now,
  //   birthtime: now,
  //   attrs: {},
  // },
];

// Event listeners for file system changes
const listeners = new Set();

// Helper to create timestamp object
function createTimestamps() {
  const now = Date.now();
  return {
    atime: now, // access time
    mtime: now, // modify time
    ctime: now, // change time (metadata)
    birthtime: now, // creation time
  };
}

// Helper to update timestamps
function updateAccessTime(node) {
  node.atime = Date.now();
}

function updateModifyTime(node) {
  const now = Date.now();
  node.mtime = now;
  node.ctime = now; // metadata changed too
}

function updateChangeTime(node) {
  node.ctime = Date.now();
}

// Notify all listeners of changes
function notifyChange(event) {
  listeners.forEach((listener) => listener(event));
}

/**
 * Subscribe to file system changes
 * @param {string|Function} pathOrCallback - Path to watch or callback function
 * @param {Function} [callback] - Called with event object {type, path, node}
 * @returns {Function} Unsubscribe function
 */
export function subscribe(pathOrCallback, callback) {
  // Overload 1: subscribe(callback)
  if (typeof pathOrCallback === "function") {
    const listener = pathOrCallback;
    listeners.add(listener);
    return () => listeners.delete(listener);
  }

  // Overload 2: subscribe(path, callback)
  if (typeof pathOrCallback === "string" && typeof callback === "function") {
    const path = pathOrCallback;
    const filteredListener = (event) => {
      if (event.path === path || event.newPath === path) {
        callback(event);
      }
    };
    listeners.add(filteredListener);
    return () => listeners.delete(filteredListener);
  }

  throw new Error(
    "Invalid arguments: expected subscribe(callback) or subscribe(path, callback)"
  );
}

/**
 * Find a node by path
 * @param {string} path - Path like '/std/Char.mls' or '/main.mls'
 * @returns {Object|null} The node or null if not found
 */
export function findNode(path) {
  // Remove leading slash and split
  const parts = path
    .replace(/^\//, "")
    .split("/")
    .filter((p) => p);
  let current = fileTree;

  for (const part of parts) {
    if (Array.isArray(current)) {
      current = current.find((node) => node.name === part);
    } else if (current?.type === "folder") {
      current = current.children?.find((node) => node.name === part);
    } else {
      return null;
    }

    if (!current) return null;
  }

  return current;
}

/**
 * Find parent node and child index
 * @param {string} path - Path to the node
 * @returns {{parent: Object|Array, index: number}|null}
 */
function findParent(path) {
  // Remove leading slash and split
  const parts = path
    .replace(/^\//, "")
    .split("/")
    .filter((p) => p);
  if (parts.length === 0) return null;

  const parentPath = parts.slice(0, -1).join("/");
  const childName = parts[parts.length - 1];

  let parent;
  if (parentPath === "") {
    parent = fileTree;
  } else {
    const parentNode = findNode("/" + parentPath);
    if (!parentNode || parentNode.type !== "folder") return null;
    parent = parentNode.children;
  }

  const index = parent.findIndex((node) => node.name === childName);
  return index >= 0 ? { parent, index } : null;
}

/**
 * Check if a path exists
 * @param {string} path - Path to check
 * @returns {boolean}
 */
export function exists(path) {
  return findNode(path) !== null;
}

/**
 * Read file content
 * @param {string} path - Path to the file
 * @returns {string} File content or null if not found/not a file
 */
export function read(path) {
  const node = findNode(path);
  if (!node || node.type !== "file") throw new Error(`File not found: ${path}`);
  updateAccessTime(node);
  return node.content || "";
}

/**
 * Write content to a file
 * @param {string} path - Path to the file
 * @param {string} content - Content to write
 * @returns {boolean} Success status
 */
export function write(path, content) {
  const node = findNode(path);

  // If file doesn't exist, create it with all missing parent directories
  if (!node) {
    return createFile(path, content, { force: true });
  }

  if (node.type !== "file") return false;
  if (node.readonly) throw new Error(`File is readonly: ${path}`);

  node.content = content;
  updateModifyTime(node);

  // Mark MLscript files as needing compilation (skip std files)
  if (node.name.endsWith(".mls") && !node.attrs?.std) {
    if (!node.attrs) node.attrs = {};
    if (node.attrs.compiled !== false) {
      node.attrs.compiled = false;
      notifyChange({
        type: "attr",
        path,
        node,
        key: "compiled",
        value: false,
      });
    }
  }

  notifyChange({ type: "write", path, node });
  return true;
}

/**
 * Create a new file
 * @param {string} path - Path where to create the file (e.g., '/main.mls' or '/std/test.mls')
 * @param {string} content - Initial content (default: empty)
 * @param {Object} options - Creation options
 * @param {boolean} options.force - If true, create missing parent directories
 * @param {boolean} options.readonly - If true, file is readonly
 * @param {Object} options.attrs - Custom attributes to attach to the file
 * @returns {boolean} Success status
 */
export function createFile(path, content = "", options = {}) {
  if (exists(path)) return false;

  // Remove leading slash and split
  const parts = path
    .replace(/^\//, "")
    .split("/")
    .filter((p) => p);
  const fileName = parts[parts.length - 1];
  const parentPath = parts.slice(0, -1).join("/");

  let parent;
  if (parentPath === "") {
    parent = fileTree;
  } else {
    let parentNode = findNode("/" + parentPath);

    // If parent doesn't exist and force is enabled, create all missing directories
    if (!parentNode && options.force) {
      const pathSegments = parentPath.split("/");
      let currentPath = "";

      for (const segment of pathSegments) {
        currentPath += "/" + segment;
        if (!exists(currentPath)) {
          createFolder(currentPath);
        }
      }

      parentNode = findNode("/" + parentPath);
    }

    if (!parentNode || parentNode.type !== "folder") return false;
    if (!parentNode.children) parentNode.children = [];
    parent = parentNode.children;
  }

  const timestamps = createTimestamps();
  const attrs = { ...(options.attrs || {}) };
  if (fileName.endsWith(".mls") && attrs.compiled === undefined) {
    attrs.compiled = attrs.std ? true : false;
  }
  const newFile = {
    name: fileName,
    type: "file",
    content: content,
    readonly: options.readonly || false,
    ...timestamps,
    attrs,
  };

  parent.push(newFile);
  parent.sort((a, b) => {
    // Folders first, then files, alphabetically
    if (a.type !== b.type) return a.type === "folder" ? -1 : 1;
    return a.name.localeCompare(b.name);
  });

  notifyChange({ type: "create", path, node: newFile });
  return true;
}

/**
 * Create a new folder
 * @param {string} path - Path where to create the folder (e.g., '/examples')
 * @param {Object} options - Creation options
 * @param {boolean} options.readonly - If true, folder is readonly
 * @param {Object} options.attrs - Custom attributes to attach to the folder
 * @returns {boolean} Success status
 */
export function createFolder(path, options = {}) {
  if (exists(path)) return false;

  // Remove leading slash and split
  const parts = path
    .replace(/^\//, "")
    .split("/")
    .filter((p) => p);
  const folderName = parts[parts.length - 1];
  const parentPath = parts.slice(0, -1).join("/");

  let parent;
  if (parentPath === "") {
    parent = fileTree;
  } else {
    const parentNode = findNode("/" + parentPath);
    if (!parentNode || parentNode.type !== "folder") return false;
    if (!parentNode.children) parentNode.children = [];
    parent = parentNode.children;
  }

  const timestamps = createTimestamps();
  const newFolder = {
    name: folderName,
    type: "folder",
    children: [],
    readonly: options.readonly || false,
    ...timestamps,
    attrs: options.attrs || {},
  };

  parent.push(newFolder);
  parent.sort((a, b) => {
    // Folders first, then files, alphabetically
    if (a.type !== b.type) return a.type === "folder" ? -1 : 1;
    return a.name.localeCompare(b.name);
  });

  notifyChange({ type: "create", path, node: newFolder });
  return true;
}

/**
 * Delete a file or folder
 * @param {string} path - Path to delete
 * @returns {boolean} Success status
 */
export function remove(path) {
  const result = findParent(path);
  if (!result) return false;

  const { parent, index } = result;
  const node = parent[index];

  parent.splice(index, 1);

  notifyChange({ type: "delete", path, node });
  return true;
}

/**
 * Rename a file or folder
 * @param {string} path - Current path
 * @param {string} newName - New name (not full path, just the name)
 * @returns {boolean} Success status
 */
export function rename(path, newName) {
  const node = findNode(path);
  if (!node) return false;

  // Check if new name would create a duplicate
  const parts = path.split("/").filter((p) => p);
  parts[parts.length - 1] = newName;
  const newPath = parts.join("/");

  if (exists(newPath)) return false;

  const oldName = node.name;
  node.name = newName;
  updateChangeTime(node);

  notifyChange({ type: "rename", path, newPath, node, oldName });
  return true;
}

/**
 * List contents of a folder
 * @param {string} path - Path to the folder
 * @returns {Array|null} Array of child nodes or null if not found/not a folder
 */
export function list(path) {
  const node = findNode(path);
  if (!node || node.type !== "folder") return null;
  return node.children || [];
}

/**
 * Get node info
 * @param {string} path - Path to the node
 * @returns {Object|null} Node object or null if not found
 */
export function stat(path) {
  return findNode(path);
}

/**
 * Get all files as an object with normalized paths as keys and content as values
 * @param {(path: string, node: unknown) => boolean} [predicate] - Optional filter function (path, node) => boolean
 * @returns {Record<string, string>} Object mapping normalized file paths to their content
 */
export function getAllFiles(predicate) {
  const result = {};

  function traverse(nodes, currentPath) {
    for (const node of nodes) {
      const nodePath = currentPath + "/" + node.name;

      if (node.type === "file") {
        if (
          predicate === undefined ||
          (typeof predicate === "function" && predicate(nodePath, node))
        ) {
          result[nodePath] = node.content || "";
        }
      } else if (node.type === "folder" && node.children) {
        traverse(node.children, nodePath);
      }
    }
  }

  traverse(fileTree, "");
  return result;
}

/**
 * Set a custom attribute on a file or folder
 * @param {string} path - Path to the node
 * @param {string} key - Attribute key
 * @param {any} value - Attribute value
 * @returns {boolean} Success status
 */
export function setAttr(path, key, value) {
  const node = findNode(path);
  if (!node) return false;

  if (!node.attrs) node.attrs = {};
  node.attrs[key] = value;
  updateChangeTime(node);

  notifyChange({ type: "attr", path, node, key, value });
  return true;
}

/**
 * Get a custom attribute from a file or folder
 * @param {string} path - Path to the node
 * @param {string} key - Attribute key
 * @returns {any} Attribute value or undefined if not found
 */
export function getAttr(path, key) {
  const node = findNode(path);
  if (!node || !node.attrs) return undefined;
  return node.attrs[key];
}

/**
 * Remove a custom attribute from a file or folder
 * @param {string} path - Path to the node
 * @param {string} key - Attribute key
 * @returns {boolean} Success status
 */
export function removeAttr(path, key) {
  const node = findNode(path);
  if (!node || !node.attrs) return false;

  const existed = key in node.attrs;
  delete node.attrs[key];

  if (existed) {
    updateChangeTime(node);
    notifyChange({ type: "attr", path, node, key, value: undefined });
  }

  return existed;
}

/**
 * Set readonly flag on a file or folder
 * @param {string} path - Path to the node
 * @param {boolean} readonly - Readonly status
 * @returns {boolean} Success status
 */
export function setReadonly(path, readonly) {
  const node = findNode(path);
  if (!node) return false;

  node.readonly = readonly;
  updateChangeTime(node);

  notifyChange({ type: "readonly", path, node, readonly });
  return true;
}
