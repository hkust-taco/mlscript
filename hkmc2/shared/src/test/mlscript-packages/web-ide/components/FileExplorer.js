import fs from '../filesystem/fs.mjs';
import PanelPersistence from './PanelPersistence.mjs';
import './FileTooltip.mjs';
import './ResizeHandle.mjs';

// File Explorer Custom Element
class FileExplorer extends HTMLElement {
  constructor() {
    super();
    this.isCollapsed = false;
    this.rootNodes = new Map();
    this.isCreatingFile = false;
    this.newFileInput = null;
    this.tooltipTimeout = null;
    this.activeTooltipTarget = null;
    this.openFiles = new Set();
  }

  connectedCallback() {
    this.render();
    this.attachEventListeners();
    this.attachTooltipHandlers();
    this.restoreSizeFromStorage();
    this.handleOpenFilesChanged = (e) => {
      this.openFiles = new Set(e.detail?.paths || []);
      this.updateOpenFlags();
    };
    document.addEventListener("open-files-changed", this.handleOpenFilesChanged);

    // Subscribe to file system changes
    this.unsubscribe = fs.subscribe((event) => {
      // Only update tree on structural changes at root level
      if (event.type === 'create' || event.type === 'delete' || event.type === 'rename') {
        // Check if this is a root-level change
        const pathParts = event.path.replace(/^\//, '').split('/');
        if (pathParts.length === 1) {
          // Root level change - update tree
          this.updateTree();
        }
      }
    });
  }

  restoreSizeFromStorage() {
    PanelPersistence.restorePanelWidth(this, 'file-explorer-width', 150, 600);
  }

  saveSizeToStorage(width) {
    PanelPersistence.savePanelWidth('file-explorer-width', width);
  }

  disconnectedCallback() {
    if (this.unsubscribe) {
      this.unsubscribe();
    }
    if (this.tooltipTimeout !== null) {
      clearTimeout(this.tooltipTimeout);
      this.tooltipTimeout = null;
    }
    if (this.handleOpenFilesChanged) {
      document.removeEventListener(
        "open-files-changed",
        this.handleOpenFilesChanged
      );
    }
  }

  render() {
    this.innerHTML = `
      <div class="header">
        <h2>Files</h2>
        <button class="button create-file-button" title="Create new file">
          <i class="icon-file-plus"></i>
        </button>
        <button class="button collapse-button" title="Toggle sidebar">
          <i class="icon-arrow-left-to-line"></i>
        </button>
      </div>
      <div class="tree-view"></div>
      <file-tooltip class="tree-tooltip"></file-tooltip>
      <resize-handle direction="horizontal" side="left" min-size="150" max-size="600"></resize-handle>
    `;

    this.updateTree();
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

  updateTree() {
    const treeView = this.querySelector('.tree-view');
    if (!treeView) return;

    // Filter root-level files to hide .mjs files that have a corresponding .mls file
    const filteredRootNodes = this.filterMjsFiles(fs.fileTree);
    const newRootPaths = new Set();

    // Build set of expected root paths
    filteredRootNodes.forEach(node => {
      const path = `/${node.name}`;
      newRootPaths.add(path);
    });

    // Remove root nodes that no longer exist
    for (const [path, element] of this.rootNodes.entries()) {
      if (!newRootPaths.has(path)) {
        element.remove();
        this.rootNodes.delete(path);
      }
    }

    // Add or update root nodes
    filteredRootNodes.forEach((node, index) => {
      const path = `/${node.name}`;
      let treeNode = this.rootNodes.get(path);

      if (!treeNode) {
        // Create new root node, passing fileTree as the parent
        treeNode = document.createElement('tree-node');
        treeNode.setData(node, path, fs.fileTree);
        this.rootNodes.set(path, treeNode);

        // Insert at correct position
        const nextChild = treeView.children[index];
        if (nextChild) {
          treeView.insertBefore(treeNode, nextChild);
        } else {
          treeView.appendChild(treeNode);
        }
      } else {
        // Update existing node's data, passing fileTree as the parent
        treeNode.setData(node, path, fs.fileTree);

        // Ensure correct order
        const currentPosition = Array.from(treeView.children).indexOf(treeNode);
        if (currentPosition !== index) {
          const nextChild = treeView.children[index];
          if (nextChild !== treeNode) {
            treeView.insertBefore(treeNode, nextChild);
          }
        }
      }
    });

    this.updateOpenFlags();
  }

  toggleCollapse() {
    this.isCollapsed = !this.isCollapsed;
    this.classList.toggle('collapsed', this.isCollapsed);

    const container = document.querySelector('.app-container');

    if (!this.isCollapsed) {
      // Restore previous width or use default
      const width = this.getAttribute('width');
      if (width) {
        container.style.setProperty('--file-explorer-width', `${width}px`);
      } else {
        container.style.removeProperty('--file-explorer-width');
      }
    }
    // Collapsed state (40px) is handled by CSS :has() selector
  }

  startCreatingFile() {
    if (this.isCreatingFile) return;

    this.isCreatingFile = true;
    const treeView = this.querySelector('.tree-view');

    // Create a temporary file entry with an input field
    const fileEntry = document.createElement('div');
    fileEntry.className = 'file-item new-file-entry';

    const fileIcon = document.createElement('i');
    fileIcon.className = 'file-icon icon-file-code';

    const input = document.createElement('input');
    input.type = 'text';
    input.className = 'new-file-input';
    input.placeholder = 'path/to/file.mls';

    fileEntry.appendChild(fileIcon);
    fileEntry.appendChild(input);

    // Insert at the top of the tree
    treeView.insertBefore(fileEntry, treeView.firstChild);
    this.newFileInput = input;

    // Focus the input
    input.focus();

    // Handle input submission
    const submitFile = () => {
      const fileName = input.value.trim();

      if (fileName) {
        // Normalize path to support nested folders (convert backslashes and trim extra slashes)
        const normalizedInput = fileName.replace(/\\/g, '/').replace(/^\/+/, '').replace(/\/+$/, '');
        const parts = normalizedInput.split('/').filter(Boolean);

        if (parts.length === 0) {
          alert('Please enter a valid file name (e.g. path/to/file.mls)');
          input.focus();
          return;
        }

        if (parts.some(part => part === '.' || part === '..')) {
          alert('File name cannot contain "." or ".." path segments');
          input.focus();
          return;
        }

        const path = `/${parts.join('/')}`;
        const success = fs.createFile(path, '', { force: true });

        if (success) {
          // File created successfully, clean up
          this.cancelCreatingFile();

          // Dispatch event to open the newly created file
          const event = new CustomEvent('file-open', {
            detail: { path, fileName },
            bubbles: true
          });
          this.dispatchEvent(event);
        } else {
          alert('Failed to create file. File may already exist.');
          input.focus();
        }
      } else {
        // Empty name, cancel creation
        this.cancelCreatingFile();
      }
    };

    const cancelFile = () => {
      this.cancelCreatingFile();
    };

    // Submit on Enter, cancel on Escape
    input.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') {
        e.preventDefault();
        submitFile();
      } else if (e.key === 'Escape') {
        e.preventDefault();
        cancelFile();
      }
    });

    // Cancel on blur (click outside)
    input.addEventListener('blur', () => {
      // Use setTimeout to allow click events to process first
      setTimeout(() => {
        if (this.isCreatingFile) {
          cancelFile();
        }
      }, 200);
    });
  }

  cancelCreatingFile() {
    if (!this.isCreatingFile) return;

    this.isCreatingFile = false;
    const entry = this.querySelector('.new-file-entry');
    if (entry) {
      entry.remove();
    }
    this.newFileInput = null;
  }

  attachEventListeners() {
    const collapseBtn = this.querySelector('.collapse-button');
    if (collapseBtn) {
      collapseBtn.addEventListener('click', () => this.toggleCollapse());
    }

    const createFileBtn = this.querySelector('.create-file-button');
    if (createFileBtn) {
      createFileBtn.addEventListener('click', () => this.startCreatingFile());
    }
  }

  attachTooltipHandlers() {
    const treeView = this.querySelector('.tree-view');
    const tooltip = this.querySelector('file-tooltip.tree-tooltip');
    if (!treeView || !tooltip) return;

    const hideTooltip = () => {
      if (this.tooltipTimeout !== null) {
        clearTimeout(this.tooltipTimeout);
        this.tooltipTimeout = null;
      }
      tooltip.hide();
      this.activeTooltipTarget = null;
    };

    treeView.addEventListener('mouseover', (e) => {
      const target = e.target.closest('.file-item, summary');
      if (!target || !treeView.contains(target)) return;

      if (this.activeTooltipTarget !== target) {
        hideTooltip();
        this.activeTooltipTarget = target;
      }

      const currentTarget = target;
      this.tooltipTimeout = setTimeout(() => {
        if (this.activeTooltipTarget !== currentTarget) return;
        const path = currentTarget.dataset.path;
        if (!path) return;
        tooltip.show(currentTarget, {
          path,
          name: currentTarget.dataset.name || currentTarget.textContent.trim(),
        });
      }, 5000);
    });

    treeView.addEventListener('mouseout', (e) => {
      if (!this.activeTooltipTarget) return;
      const related = e.relatedTarget;
      if (related && this.activeTooltipTarget.contains(related)) return;
      if (related && related.closest('.file-item, summary') === this.activeTooltipTarget) return;
      hideTooltip();
    });

    treeView.addEventListener('scroll', hideTooltip);
    this.addEventListener('mouseleave', hideTooltip);
  }

  updateOpenFlags() {
    for (const treeNode of this.rootNodes.values()) {
      if (treeNode.updateOpenState) {
        treeNode.updateOpenState(this.openFiles);
      }
    }
  }
}

customElements.define('file-explorer', FileExplorer);

export { FileExplorer };
