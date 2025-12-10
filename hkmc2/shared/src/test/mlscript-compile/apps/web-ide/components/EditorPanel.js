import { subscribe, read, stat } from "../filesystem/fs.js";
import { createEditor } from "../editor/editor.js";
import "./FileTooltip.js";

// Editor Panel Custom Element
class EditorPanel extends HTMLElement {
  constructor() {
    super();
    this.openTabs = new Map();
    this.activeTabId = null;
    this.tabCounter = 0;
    this.tabTooltipTimeout = null;
    this.tabTooltipPendingTarget = null;
    this.tabTooltipHoverTarget = null;
    this.emitOpenFilesChange();
  }

  emitOpenFilesChange() {
    const paths = Array.from(this.openTabs.values()).map((t) => t.path);
    document.dispatchEvent(
      new CustomEvent("open-files-changed", {
        detail: { paths },
      })
    );
  }

  connectedCallback() {
    this.render();
    this.setupEventListeners();
    this.setupTabBarScrolling();

    // Subscribe to file system changes
    this.unsubscribe = subscribe((event) => {
      // Update content of open tabs if files are modified
      if (
        event.type === "write" ||
        event.type === "delete" ||
        event.type === "rename" ||
        event.type === "readonly" ||
        event.type === "attr"
      ) {
        for (const [tabId, tab] of this.openTabs) {
          if (tab.path === event.path) {
            if (event.type === "delete") {
              // Close tab if file is deleted
              this.closeTab(tabId);
            } else if (event.type === "rename") {
              // Update tab name and path
              tab.name = event.node.name;
              tab.path = event.newPath;
              this.updateDisplay();
            } else if (event.type === "readonly") {
              tab.readonly = event.readonly;
              this.updateDisplay();
            } else if (event.type === "attr") {
              tab.attrs = event.node?.attrs || {};
              this.updateDisplay();
            } else if (event.type === "write") {
              // Reload content if file was modified externally
              const currentContent = tab.editorView.state.doc.toString();
              const fileContent = read(event.path);

              if (fileContent !== null && fileContent !== currentContent) {
                // Update content while preserving cursor position
                const transaction = tab.editorView.state.update({
                  changes: {
                    from: 0,
                    to: tab.editorView.state.doc.length,
                    insert: fileContent,
                  },
                });
                tab.editorView.dispatch(transaction);
              }
            }
          }
        }
      }
    });
  }

  disconnectedCallback() {
    if (this.unsubscribe) {
      this.unsubscribe();
    }
    if (this.resizeObserver) {
      this.resizeObserver.disconnect();
    }
    // Destroy all CodeMirror instances
    for (const tab of this.openTabs.values()) {
      if (tab.editorView) {
        tab.editorView.destroy();
      }
    }
  }

  render() {
    this.innerHTML = `
      <div class="tab-bar-wrapper">
        <button class="tab-scroll-arrow tab-scroll-left" aria-label="Scroll tabs left">‹</button>
        <div class="tab-bar"></div>
        <button class="tab-scroll-arrow tab-scroll-right" aria-label="Scroll tabs right">›</button>
        <file-tooltip class="tab-tooltip"></file-tooltip>
      </div>
      <div class="editor-container">
        <div class="empty-state">Open a file to start editing</div>
      </div>
    `;
  }

  setupEventListeners() {
    window.addEventListener("file-open", (e) => {
      this.openFile(e.detail.path, e.detail.fileName);
    });

    // Keyboard shortcuts
    document.addEventListener("keydown", (e) => {
      // Check if Cmd (Mac) or Ctrl (Windows/Linux) is pressed
      const isMac = window.navigator.platform.toUpperCase().indexOf("MAC") >= 0;
      const isCmdOrCtrl = isMac ? e.metaKey : e.ctrlKey;

      if (isCmdOrCtrl) {
        // Cmd/Ctrl+S - Trigger compile
        if (e.key === "s" || e.key === "S") {
          e.preventDefault();
          // Get the active tab's file path
          const activeTab = this.activeTabId
            ? this.openTabs.get(this.activeTabId)
            : null;
          // Dispatch compile event
          const compileEvent = new CustomEvent("compile-requested", {
            bubbles: true,
            detail: {
              filePath: activeTab ? activeTab.path : null,
            },
          });
          document.dispatchEvent(compileEvent);
        }

        // Cmd/Ctrl+E - Execute the current file
        if (e.key === "e" || e.key === "E") {
          e.preventDefault();
          const activeTab = this.activeTabId
            ? this.openTabs.get(this.activeTabId)
            : null;
          if (activeTab) {
            const executeEvent = new CustomEvent("execute-requested", {
              bubbles: true,
              detail: {
                filePath: activeTab ? activeTab.path : null,
              },
            });
            document.dispatchEvent(executeEvent);
          }
        }

        if (e.key === "b" || e.key === "B") {
          e.preventDefault();
          const fileExplorer = document.querySelector("file-explorer");
          if (fileExplorer) {
            fileExplorer.toggleCollapse();
          }
        }
      }
      
      if (e.ctrlKey) {
        // Ctrl+W - Close active tab
        if ((e.key === "w" || e.key === "W")) {
          e.preventDefault();
          if (this.activeTabId) {
            this.closeTab(this.activeTabId);
          }
        }
      }
    });
  }

  setupTabBarScrolling() {
    const tabBar = this.querySelector(".tab-bar");
    const leftArrow = this.querySelector(".tab-scroll-left");
    const rightArrow = this.querySelector(".tab-scroll-right");

    let scrollInterval = null;
    const scrollSpeed = 3;

    // Mouse wheel scrolling (convert vertical scroll to horizontal)
    tabBar.addEventListener("wheel", (e) => {
      e.preventDefault();
      tabBar.scrollLeft += e.deltaY;
    });

    // Left arrow hover scrolling
    const startScrollLeft = () => {
      if (scrollInterval) return;
      scrollInterval = setInterval(() => {
        tabBar.scrollLeft -= scrollSpeed;
      }, 10);
    };

    const startScrollRight = () => {
      if (scrollInterval) return;
      scrollInterval = setInterval(() => {
        tabBar.scrollLeft += scrollSpeed;
      }, 10);
    };

    const stopScroll = () => {
      if (scrollInterval) {
        clearInterval(scrollInterval);
        scrollInterval = null;
      }
    };

    leftArrow.addEventListener("mouseenter", startScrollLeft);
    leftArrow.addEventListener("mouseleave", stopScroll);
    rightArrow.addEventListener("mouseenter", startScrollRight);
    rightArrow.addEventListener("mouseleave", stopScroll);

    // Update arrow visibility based on scroll position
    this.updateArrowVisibility = () => {
      const hasOverflow = tabBar.scrollWidth > tabBar.clientWidth;
      const isAtStart = tabBar.scrollLeft === 0;
      const isAtEnd =
        tabBar.scrollLeft >= tabBar.scrollWidth - tabBar.clientWidth - 1;

      const hideArrow = (arrow) => {
        if (arrow.classList.contains("visible")) {
          arrow.classList.remove("visible");
          // Set display: none after fade-out transition
          setTimeout(() => {
            if (!arrow.classList.contains("visible")) {
              arrow.style.display = "none";
            }
          }, 200); // Match the CSS transition duration
        }
      };

      const showArrow = (arrow) => {
        if (!arrow.classList.contains("visible")) {
          arrow.style.display = "flex";
          // Force reflow to ensure display change is applied before transition
          arrow.offsetHeight;
          arrow.classList.add("visible");
        }
      };

      if (hasOverflow) {
        if (isAtStart) {
          hideArrow(leftArrow);
        } else {
          showArrow(leftArrow);
        }
        if (isAtEnd) {
          hideArrow(rightArrow);
        } else {
          showArrow(rightArrow);
        }
      } else {
        hideArrow(leftArrow);
        hideArrow(rightArrow);
      }
    };

    tabBar.addEventListener("scroll", this.updateArrowVisibility);

    // Store observer for cleanup
    this.resizeObserver = new ResizeObserver(this.updateArrowVisibility);
    this.resizeObserver.observe(tabBar);

    // Initial check
    setTimeout(this.updateArrowVisibility, 0);
  }

  openFile(filePath, fileName) {
    // Check if file is already open
    let existingTabId = null;
    for (const [tabId, tab] of this.openTabs) {
      if (tab.path === filePath) {
        existingTabId = tabId;
        break;
      }
    }

    if (existingTabId) {
      // File already open, just switch to it
      this.switchTab(existingTabId);
      return existingTabId;
    } else {
      // Create new tab
      const tabId = `tab-${this.tabCounter++}`;

      // Create container for CodeMirror
      const editorDiv = document.createElement("div");
      editorDiv.className = "editor-codemirror";

      // Load file content from fs
      const content = read(filePath);
      const initialContent = content !== null ? content : "";
      const extension = filePath.match(/\.(\w+)$/)?.[1] ?? "";
      const nodeInfo = stat(filePath);
      const isReadonly = !!nodeInfo?.readonly;
      const attrs = nodeInfo?.attrs || {};
      const editorView = createEditor(
        editorDiv,
        initialContent,
        filePath,
        extension,
        isReadonly
      );
      this.openTabs.set(tabId, {
        name: fileName,
        path: filePath,
        editorDiv,
        editorView,
        readonly: isReadonly,
        attrs,
      });
      const editorContainer = this.querySelector(".editor-container");
      editorContainer.appendChild(editorDiv);
      this.switchTab(tabId);
      this.updateDisplay();
      this.emitOpenFilesChange();
      return tabId;
    }
  }

  openFileAtLine(filePath, line) {
    // Extract file name from path
    const fileName = filePath.split('/').pop();

    // Open the file (or switch to it if already open)
    const tabId = this.openFile(filePath, fileName);

    // Get the editor view for this tab
    const tab = this.openTabs.get(tabId);
    if (tab && tab.editorView) {
      // Navigate to the line
      // CodeMirror lines are 1-indexed, so we use the line number as-is
      const linePos = tab.editorView.state.doc.line(line);

      // Move cursor to the beginning of the line and scroll into view
      tab.editorView.dispatch({
        selection: { anchor: linePos.from, head: linePos.from },
        scrollIntoView: true
      });

      // Focus the editor
      tab.editorView.focus();
    }
  }

  switchTab(tabId) {
    // Hide all editors
    for (const tab of this.openTabs.values()) {
      tab.editorDiv.classList.remove("active");
    }

    // Show the selected editor
    const selectedTab = this.openTabs.get(tabId);
    if (selectedTab) {
      selectedTab.editorDiv.classList.add("active");
      this.activeTabId = tabId;
      selectedTab.editorView.focus();
    }

    this.updateDisplay();

    // Scroll the active tab into view
    this.scrollTabIntoView(tabId);
  }

  closeTab(tabId) {
    const tab = this.openTabs.get(tabId);
    if (tab) {
      // Destroy CodeMirror instance
      if (tab.editorView) {
        tab.editorView.destroy();
      }

      // Remove editor div from DOM
      tab.editorDiv.remove();

      // Remove from map
      this.openTabs.delete(tabId);

      // If we closed the active tab, switch to another
      if (this.activeTabId === tabId) {
        const remainingTabs = Array.from(this.openTabs.keys());
        if (remainingTabs.length > 0) {
          this.switchTab(remainingTabs[remainingTabs.length - 1]);
        } else {
          this.activeTabId = null;
          this.notifyActiveTabChange(null);
        }
      }
    }

    this.updateDisplay();
    this.emitOpenFilesChange();
  }

  clearTabTooltip(reason = "unknown") {
    const tooltip = this.querySelector("file-tooltip.tab-tooltip");
    console.log("[tab-tooltip] hide", {
      reason,
      pendingTargetPath: this.tabTooltipPendingTarget?.dataset?.path || null,
      hoverTargetPath: this.tabTooltipHoverTarget?.dataset?.path || null,
    });
    if (this.tabTooltipTimeout !== null) {
      clearTimeout(this.tabTooltipTimeout);
      this.tabTooltipTimeout = null;
    }
    this.tabTooltipPendingTarget = null;
    this.tabTooltipHoverTarget = null;
    if (tooltip) {
      tooltip.hide();
    }
  }

  updateDisplay() {
    const tabBar = this.querySelector(".tab-bar");
    const emptyState = this.querySelector(".empty-state");
    const tooltip = this.querySelector("file-tooltip.tab-tooltip");
    // Reset any visible tooltip and pending timers when rebuilding the tab bar
    this.clearTabTooltip("rebuild-tab-bar");

    // Update tab bar
    const tabs = Array.from(this.openTabs.entries())
      .map(([tabId, tab]) => {
        const isActive = tabId === this.activeTabId;

        // Split filename and extension
        const lastDot = tab.name.lastIndexOf(".");
        let nameHtml;
        if (lastDot > 0) {
          const baseName = tab.name.substring(0, lastDot);
          const extension = tab.name.substring(lastDot);
          nameHtml = `<span class="tab-basename">${baseName}</span><span class="tab-extension">${extension}</span>`;
        } else {
          nameHtml = `<span class="tab-basename">${tab.name}</span>`;
        }

        return `
          <div class="tab ${
            isActive ? "active" : ""
          }" data-tab-id="${tabId}" data-path="${tab.path}">
            <span class="tab-name">
              ${tab.readonly ? '<i class="tab-lock icon-lock"></i>' : ""}
              <span class="tab-name-text">${nameHtml}</span>
            </span>
            <button class="tab-close" data-tab-id="${tabId}"><i class="icon-x"></i></button>
          </div>
        `;
      })
      .join("");

    tabBar.innerHTML = tabs;

    // Show/hide empty state
    if (this.openTabs.size === 0) {
      emptyState.classList.remove("hidden");
    } else {
      emptyState.classList.add("hidden");
    }
    this.notifyActiveTabChange(
      this.activeTabId ? this.openTabs.get(this.activeTabId) : null
    );
    this.emitOpenFilesChange();
    
    // Set up tab tooltips for display metadata of files.

    const showTooltip = (tabEl, reason = "unknown") => {
      if (!tooltip) return;
      const tabId = tabEl.getAttribute("data-tab-id");
      const tab = this.openTabs.get(tabId);
      if (!tab) return;
      console.log("[tab-tooltip] show", {
        reason,
        tabId,
        path: tab.path,
        visible: tooltip.classList.contains("visible"),
        pendingTargetPath: this.tabTooltipPendingTarget?.dataset?.path || null,
        hoverTargetPath: this.tabTooltipHoverTarget?.dataset?.path || null,
      });
      tooltip.show(tabEl, {
        path: tab.path,
        name: tab.name,
        size: tab.editorView?.state.doc.length,
        placement: "bottom",
      });
    };

    // Attach event listeners to tabs
    const tabElements = tabBar.querySelectorAll(".tab");
    const setupNameScroll = (container) => {
      if (!container || container.dataset.scrollInit) return;
      const textEl = container.querySelector(".tab-name-text");
      if (!textEl) return;
      container.dataset.scrollInit = "true";
      const start = () => {
        const distance =
          textEl.scrollWidth - container.clientWidth + 16; // extra padding to reveal end
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
    };

    tabElements.forEach((tabEl) => {
      setupNameScroll(tabEl.querySelector(".tab-name"));
      tabEl.addEventListener("click", (e) => {
        if (!e.target.closest(".tab-close")) {
          const tabId = tabEl.getAttribute("data-tab-id");
          this.switchTab(tabId);
        }
      });

      // Tooltip on tab hover with movement guard to avoid false triggers on rerenders
      tabEl.addEventListener("mouseenter", () => {
        this.tabTooltipHoverTarget = tabEl;
        console.log("[tab-tooltip] mouseenter", {
          tabId: tabEl.getAttribute("data-tab-id"),
          path: tabEl.dataset.path,
        });
      });
      tabEl.addEventListener("mousemove", () => {
        if (this.tabTooltipHoverTarget !== tabEl) return;
        if (tooltip && tooltip.classList.contains("visible")) {
          showTooltip(tabEl, "already-visible");
          return;
        }
        if (this.tabTooltipPendingTarget === tabEl) return;
        if (this.tabTooltipTimeout !== null) {
          clearTimeout(this.tabTooltipTimeout);
        }
        this.tabTooltipPendingTarget = tabEl;
        console.log("[tab-tooltip] schedule show", {
          tabId: tabEl.getAttribute("data-tab-id"),
          path: tabEl.dataset.path,
          delayMs: 5000,
        });
        this.tabTooltipTimeout = setTimeout(() => {
          if (this.tabTooltipHoverTarget !== tabEl) return;
          showTooltip(tabEl, "delay-elapsed");
          this.tabTooltipPendingTarget = null;
          this.tabTooltipTimeout = null;
        }, 5000);
      });
      tabEl.addEventListener("mouseleave", () =>
        this.clearTabTooltip("mouseleave")
      );
    });

    const closeButtons = tabBar.querySelectorAll(".tab-close");
    closeButtons.forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const tabId = btn.getAttribute("data-tab-id");
        this.closeTab(tabId);
      });
    });

    // Hide tooltip when tab bar scrolls
    tabBar.addEventListener("scroll", () =>
      this.clearTabTooltip("tab-bar-scroll")
    );

    // Update arrow visibility after tabs change
    if (this.updateArrowVisibility) {
      setTimeout(this.updateArrowVisibility, 0);
    }
  }

  scrollTabIntoView(tabId) {
    setTimeout(() => {
      const tabBar = this.querySelector(".tab-bar");
      const tabElement = this.querySelector(`.tab[data-tab-id="${tabId}"]`);

      if (tabBar && tabElement) {
        const tabBarRect = tabBar.getBoundingClientRect();
        const tabRect = tabElement.getBoundingClientRect();

        // Check if tab is fully visible
        const isVisible =
          tabRect.left >= tabBarRect.left && tabRect.right <= tabBarRect.right;

        if (!isVisible) {
          // Scroll to make the tab visible with some padding
          const scrollOffset = tabElement.offsetLeft - tabBar.offsetLeft - 20;
          tabBar.scrollTo({
            left: scrollOffset,
            behavior: "smooth",
          });
        }
      }
    }, 0);
  }

  notifyActiveTabChange(tab) {
    const detail = tab
      ? { path: tab.path, isStd: !!tab.attrs?.std }
      : { path: null, isStd: false };
    document.dispatchEvent(
      new CustomEvent("active-tab-changed", {
        detail,
      })
    );
  }
}

customElements.define("editor-panel", EditorPanel);
