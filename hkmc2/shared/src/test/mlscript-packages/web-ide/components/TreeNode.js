import fs from '../filesystem/fs.mjs';

// Tree Node Custom Element (Reactive)
class TreeNode extends HTMLElement {
  constructor() {
    super();
    this.node = null;
    this.path = '';
    // Keep references to DOM elements
    this.elements = {
      fileItem: null,
      fileNameText: null,
      compiledDot: null,
      details: null,
      summary: null,
      childrenContainer: null
    };
    // Map of child path to TreeNode element
    this.childTreeNodes = new Map();
  }

  setupNameScroll(container, textEl) {
    if (!container || !textEl || container.dataset.scrollInit) return;
    container.dataset.scrollInit = "true";
    const start = () => {
      const distance = textEl.scrollWidth - container.clientWidth + 16;
      if (distance <= 0) return;
      const duration = Math.min(12, Math.max(4, distance / 40));
      textEl.style.setProperty("--scroll-distance", `${distance}px`);
      textEl.style.setProperty("--scroll-duration", `${duration}s`);
      textEl.classList.add("scrolling");
    };
    const stop = () => {
      textEl.classList.remove("scrolling");
      textEl.style.removeProperty("--scroll-distance");
      textEl.style.removeProperty("--scroll-duration");
    };
    container.addEventListener("mouseenter", start);
    container.addEventListener("mouseleave", stop);
    container.addEventListener("focus", start);
    container.addEventListener("blur", stop);
  }

  connectedCallback() {
    // Subscribe to file system changes
    this.unsubscribe = fs.subscribe((event) => {
      // Handle different event types
      if (event.type === 'create' || event.type === 'delete') {
        // Structural change - need to update children
        if (this.node?.type === 'folder') {
          // Check if the event is for a direct child of this folder
          const eventPath = event.path;
          const parentPath = eventPath.substring(0, eventPath.lastIndexOf('/'));
          if (parentPath === this.path) {
            this.updateChildren();
          }
        }
        // If this is a file node, check if we need to update the .mjs button
        if (this.node?.type === 'file' && this.node.name.endsWith('.mls')) {
          const eventPath = event.path;
          const parentPath = eventPath.substring(0, eventPath.lastIndexOf('/'));
          const myParentPath = this.path.substring(0, this.path.lastIndexOf('/'));

          // Check if a .mjs file was created/deleted in the same folder
          if (parentPath === myParentPath && eventPath.endsWith('.mjs')) {
            const eventFileName = eventPath.substring(eventPath.lastIndexOf('/') + 1);
            const myBasename = this.node.name.slice(0, -4);
            const eventBasename = eventFileName.slice(0, -4);

            // If the .mjs file matches our .mls file, update the button
            if (myBasename === eventBasename) {
              this.render();
            }
          }
        }
      } else if (event.type === 'rename') {
        // Update name if this is the renamed node
        if (event.path === this.path) {
          this.updateName();
        }
        // Update children if a child was renamed
        if (this.node?.type === 'folder') {
          const eventPath = event.path;
          const parentPath = eventPath.substring(0, eventPath.lastIndexOf('/'));
          if (parentPath === this.path) {
            this.updateChildren();
          }
        }
      } else if (event.type === 'readonly' || event.type === 'attr') {
        // Update readonly icon if this node's readonly status changed
        if (event.path === this.path) {
          this.render();
        }
      }
      // No need to handle 'write' events - they don't affect the tree structure
    });

    this.render();
  }

  disconnectedCallback() {
    if (this.unsubscribe) {
      this.unsubscribe();
    }
    // Clean up child nodes
    this.childTreeNodes.clear();
  }

  setData(node, path, parentFolderNode = null) {
    this.node = node;
    this.path = path;
    this.parentFolderNode = parentFolderNode;
    if (this.isConnected) {
      this.render();
    }
  }

  updateName() {
    if (!this.node) return;

    if (this.node.type === 'file' && this.elements.fileItem) {
      this.elements.fileItem.textContent = this.node.name;
    } else if (this.node.type === 'folder' && this.elements.summary) {
      this.elements.summary.textContent = this.node.name + '/';
    }
  }

  updateChildren() {
    if (!this.node || this.node.type !== 'folder' || !this.elements.childrenContainer) {
      return;
    }

    const children = this.node.children || [];

    // Filter out .mjs files that have a corresponding .mls file
    const filteredChildren = this.filterMjsFiles(children);
    const newChildPaths = new Set();

    // Build set of expected child paths
    filteredChildren.forEach(child => {
      const childPath = this.path ? `${this.path}/${child.name}` : child.name;
      newChildPaths.add(childPath);
    });

    // Remove child nodes that no longer exist
    for (const [childPath, childElement] of this.childTreeNodes.entries()) {
      if (!newChildPaths.has(childPath)) {
        childElement.remove();
        this.childTreeNodes.delete(childPath);
      }
    }

    // Add or update children in order
    filteredChildren.forEach((child, index) => {
      const childPath = this.path ? `${this.path}/${child.name}` : child.name;

      let childElement = this.childTreeNodes.get(childPath);

      if (!childElement) {
        // Create new child node
        childElement = document.createElement('tree-node');
        childElement.setData(child, childPath, this.node);
        this.childTreeNodes.set(childPath, childElement);

        // Insert at correct position
        const nextChild = this.elements.childrenContainer.children[index];
        if (nextChild) {
          this.elements.childrenContainer.insertBefore(childElement, nextChild);
        } else {
          this.elements.childrenContainer.appendChild(childElement);
        }
      } else {
        // Update existing child's data
        childElement.setData(child, childPath, this.node);

        // Ensure correct order
        const currentPosition = Array.from(this.elements.childrenContainer.children).indexOf(childElement);
        if (currentPosition !== index) {
          const nextChild = this.elements.childrenContainer.children[index];
          if (nextChild !== childElement) {
            this.elements.childrenContainer.insertBefore(childElement, nextChild);
          }
        }
      }
    });
  }

  /**
   * Filter out .mjs files that have a corresponding .mls file
   * @param {Array} children - Array of child nodes
   * @returns {Array} Filtered array of children
   */
  filterMjsFiles(children) {
    // Create a set of .mls file basenames (without extension)
    const mlsFiles = new Set();
    children.forEach(child => {
      if (child.type === 'file' && child.name.endsWith('.mls')) {
        const basename = child.name.slice(0, -4); // Remove .mls extension
        mlsFiles.add(basename);
      }
    });

    // Filter out .mjs files that have a corresponding .mls file
    return children.filter(child => {
      if (child.type === 'file' && child.name.endsWith('.mjs')) {
        const basename = child.name.slice(0, -4); // Remove .mjs extension
        return !mlsFiles.has(basename);
      }
      return true; // Keep all other files and folders
    });
  }

  /**
   * Check if a .mjs file exists for this .mls file
   * @returns {boolean}
   */
  hasMjsFile() {
    if (!this.node || this.node.type !== 'file' || !this.node.name.endsWith('.mls')) {
      return false;
    }

    const basename = this.node.name.slice(0, -4); // Remove .mls extension
    const mjsFileName = basename + '.mjs';

    // First try using the cached parent folder node
    if (this.parentFolderNode) {
      let children;
      // Handle root level (which is an array) vs regular folders
      if (Array.isArray(this.parentFolderNode)) {
        children = this.parentFolderNode;
      } else if (this.parentFolderNode.type === 'folder') {
        children = this.parentFolderNode.children || [];
      } else {
        children = [];
      }

      return children.some(child => child.type === 'file' && child.name === mjsFileName);
    }

    // Fallback: Look up the parent folder dynamically from the file system
    const parentPath = this.path.substring(0, this.path.lastIndexOf('/'));
    const isRoot = parentPath === '';

    let children;
    if (isRoot) {
      // Root level - stat('/') returns the fileTree array directly
      const rootArray = fs.stat('/');
      children = Array.isArray(rootArray) ? rootArray : [];
    } else {
      const parentNode = fs.stat(parentPath);
      if (!parentNode || parentNode.type !== 'folder') {
        return false;
      }
      children = parentNode.children || [];
    }

    return children.some(child => child.type === 'file' && child.name === mjsFileName);
  }

  updateOpenState(openFiles) {
    if (!openFiles) return;
    if (this.node?.type === 'file' && this.elements.fileItem) {
      this.elements.fileItem.classList.toggle('open-in-editor', openFiles.has(this.path));
    }
    for (const child of this.childTreeNodes.values()) {
      child.updateOpenState(openFiles);
    }
  }

  /**
   * Get the path to the corresponding .mjs file
   * @returns {string|null}
   */
  getMjsPath() {
    if (!this.hasMjsFile()) return null;

    const basename = this.node.name.slice(0, -4); // Remove .mls extension
    const mjsFileName = basename + '.mjs';
    const pathParts = this.path.split('/');
    pathParts[pathParts.length - 1] = mjsFileName;
    return pathParts.join('/');
  }

  /**
   * Get the appropriate icon class for a file based on its extension
   * @param {string} fileName - The file name
   * @returns {string} Lucide icon name
   */
  getFileIcon(fileName) {
    const ext = fileName.substring(fileName.lastIndexOf('.'));
    switch (ext) {
      case '.mls':
      case '.mjs':
      case '.js':
        return 'file-code';
      case '.json':
        return 'braces';
      case '.md':
        return 'file-text';
      default:
        return 'file';
    }
  }

  render() {
    if (!this.node) return;

    // Only create elements if they don't exist yet
    if (this.node.type === 'file') {
      if (!this.elements.fileItem) {
        this.elements.fileItem = document.createElement('div');
        this.elements.fileItem.className = 'file-item';
        this.elements.fileItem.dataset.path = this.path;
        this.elements.fileItem.dataset.name = this.node.name;

        // Create icon element
        this.elements.fileIcon = document.createElement('i');

        // Create a container for the file name
        this.elements.fileName = document.createElement('span');
        this.elements.fileName.className = 'file-name';
        this.elements.fileNameText = document.createElement('span');
        this.elements.fileNameText.className = 'file-name-text';
        this.elements.fileName.appendChild(this.elements.fileNameText);
        this.setupNameScroll(this.elements.fileName, this.elements.fileNameText);

        this.elements.compiledDot = document.createElement('span');
        this.elements.compiledDot.className = 'compiled-dot';

        // Attach click listener to the file name
        this.elements.fileName.addEventListener('click', () => {
          const event = new CustomEvent('file-open', {
            detail: { path: this.path, fileName: this.node.name },
            bubbles: true
          });
          this.dispatchEvent(event);
        });

        this.elements.fileItem.appendChild(this.elements.fileIcon);
        this.elements.fileItem.appendChild(this.elements.fileName);
        this.elements.fileItem.appendChild(this.elements.compiledDot);
        this.appendChild(this.elements.fileItem);
      }

      // Update icon based on readonly status and file type
      if (this.node.readonly) {
        this.elements.fileIcon.className = 'file-icon icon-file-lock';
      } else {
        const icon = this.getFileIcon(this.node.name);
        this.elements.fileIcon.className = `file-icon icon-${icon}`;
      }

      this.elements.fileNameText.textContent = this.node.name;
      this.elements.fileItem.dataset.path = this.path;
      this.elements.fileItem.dataset.name = this.node.name;
      const isStd = this.node.attrs?.std === true;
      const compiledStatus = this.node.attrs?.compiled;
      const isCompiled = compiledStatus === true;
      this.elements.compiledDot.classList.toggle('hidden', isStd);
      this.elements.compiledDot.classList.toggle('needs-compile', !isCompiled && !isStd);
      this.elements.compiledDot.title = isStd
        ? ''
        : isCompiled
          ? 'Compiled'
          : 'Needs compile';

      // Add or remove .mjs button based on whether a compiled file exists
      if (this.node.name.endsWith('.mls')) {
        const hasMjs = this.hasMjsFile();

        if (hasMjs) {
          if (!this.elements.mjsButton) {
            this.elements.mjsButton = document.createElement('button');
            this.elements.mjsButton.className = 'mjs-button';
            this.elements.mjsButton.textContent = '.mjs';
            this.elements.mjsButton.title = 'Open compiled .mjs file';

            // Attach click listener to open the .mjs file
            this.elements.mjsButton.addEventListener('click', (e) => {
              e.stopPropagation(); // Prevent triggering the file-item click
              const mjsPath = this.getMjsPath();
              if (mjsPath) {
                const basename = this.node.name.slice(0, -4);
                const event = new CustomEvent('file-open', {
                  detail: { path: mjsPath, fileName: basename + '.mjs' },
                  bubbles: true
                });
                this.dispatchEvent(event);
              }
            });

            this.elements.fileItem.appendChild(this.elements.mjsButton);
          }
        } else {
          // Remove .mjs button if it exists but shouldn't
          if (this.elements.mjsButton) {
            this.elements.mjsButton.remove();
            this.elements.mjsButton = null;
          }
        }
      }

    } else if (this.node.type === 'folder') {
      if (!this.elements.details) {
        // Create folder structure
        this.elements.details = document.createElement('details');
        
        console.log(`The attributes of ${this.path}:`, this.node.attrs);

        // Check collapsed attribute, default to open if not specified
        const isCollapsed = this.node.attrs?.collapsed === true;
        this.elements.details.open = !isCollapsed;

        this.elements.summary = document.createElement('summary');
        this.elements.summary.dataset.path = this.path;
        this.elements.summary.dataset.name = this.node.name + '/';

        // Create folder icon
        this.elements.folderIcon = document.createElement('i');
        // Set initial icon based on collapsed state
        this.elements.folderIcon.className = isCollapsed ? 'folder-icon icon-folder' : 'folder-icon icon-folder-open';

        // Create folder name span
        this.elements.folderName = document.createElement('span');
        this.elements.folderName.textContent = this.node.name;

        this.elements.summary.appendChild(this.elements.folderIcon);
        this.elements.summary.appendChild(this.elements.folderName);
        this.elements.details.appendChild(this.elements.summary);

        this.elements.childrenContainer = document.createElement('div');
        this.elements.childrenContainer.className = 'folder-children';
        this.elements.childrenContainer.style.paddingLeft = '12px';
        this.elements.details.appendChild(this.elements.childrenContainer);

        // Update folder icon on toggle
        this.elements.details.addEventListener('toggle', () => {
          if (this.elements.details.open) {
            this.elements.folderIcon.className = 'folder-icon icon-folder-open';
          } else {
            this.elements.folderIcon.className = 'folder-icon icon-folder';
          }
        });

        this.appendChild(this.elements.details);
      }

      this.elements.folderName.textContent = this.node.name;
      this.elements.summary.dataset.path = this.path;
      this.elements.summary.dataset.name = this.node.name;
      this.updateChildren();
    }
  }
}

customElements.define('tree-node', TreeNode);

export { TreeNode };
