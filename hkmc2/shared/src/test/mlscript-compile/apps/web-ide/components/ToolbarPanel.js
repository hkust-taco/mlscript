import {
  computePosition,
  shift,
  offset,
} from "https://esm.sh/@floating-ui/dom";

// Toolbar Panel Custom Element
class ToolbarPanel extends HTMLElement {
  constructor() {
    super();
    this.status = "idle"; // idle, running, done, error, aborted, fatal
    this.runningTime = null;
    this.startTime = null;
    this.isCompiling = false;
    this.isStdActive = false;
  }

  connectedCallback() {
    this.render();
    this.attachEventListeners();

    // Listen for status change events
    window.addEventListener("execution-status-change", (e) => {
      this.setStatus(e.detail.status, e.detail.runningTime);
    });

    // Listen for compilation status change events
    document.addEventListener("compilation-status-change", (e) => {
      this.setCompilationStatus(e.detail.status);
    });

    document.addEventListener("active-tab-changed", (e) => {
      this.setActiveFileMeta(e.detail);
    });
  }

  setStatus(status, runningTime = null) {
    this.status = status;
    this.runningTime = runningTime;
    this.updateStatusIndicator();
  }

  updateStatusIndicator() {
    const statusLight = this.querySelector(".status-light");
    const statusText = this.querySelector(".status-text");
    const terminateBtn = this.querySelector("#terminate");
    const tooltip = this.querySelector(".status-tooltip");

    if (!statusLight || !statusText) return;

    // Remove all status classes
    statusLight.className = "status-light";

    // Add appropriate class and update text
    switch (this.status) {
      case "idle":
        statusLight.classList.add("status-idle");
        statusText.textContent = "Not running";
        if (terminateBtn) terminateBtn.style.display = "none";
        tooltip.textContent = `No execution is currently running.`;
        break;
      case "running":
        statusLight.classList.add("status-running");
        statusText.textContent = "Running...";
        if (terminateBtn) terminateBtn.style.display = "inline-block";
        tooltip.textContent = `Execution started at ${new Date(
          this.startTime
        ).toLocaleTimeString()}.`;
        break;
      case "done":
        statusLight.classList.add("status-done");
        statusText.textContent = this.runningTime
          ? `Done (${this.runningTime}ms)`
          : "Done";
        if (terminateBtn) terminateBtn.style.display = "none";
        tooltip.textContent = `Execution completed successfully in ${this.runningTime}ms.`;
        break;
      case "error":
        statusLight.classList.add("status-error");
        statusText.textContent = "Error";
        if (terminateBtn) terminateBtn.style.display = "none";
        tooltip.textContent = `Execution encountered an error.`;
        break;
      case "aborted":
        statusLight.classList.add("status-aborted");
        statusText.textContent = "Aborted";
        if (terminateBtn) terminateBtn.style.display = "none";
        tooltip.textContent = `Execution was aborted by the user.`;
        break;
      case "fatal":
        statusLight.classList.add("status-fatal");
        statusText.textContent = "Fatal error";
        if (terminateBtn) terminateBtn.style.display = "none";
        tooltip.textContent = `A fatal error occurred during execution.`;
        break;
    }
  }

  render() {
    this.innerHTML = `
      <div class="title">MLscript Web IDE</div>
      <div class="status-container">
        <div class="status-light status-idle"></div>
        <span class="status-text">Not running</span>
      </div>
      <div class="status-tooltip" role="tooltip">
        No execution is currently running.
      </div>
      <div class="actions">
        <button id="compile" class="compile-btn">
          <i class="icon-binary"></i>
          Compile
        </button>
        <button id="execute" class="compile-btn">
          <i class="icon-play"></i>
          Execute
        </button>
        <button id="terminate" class="terminate-btn" style="display: none;">Terminate</button>
      </div>
    `;
  }

  #getActiveFilePath() {
    const editorPanel = document.querySelector("editor-panel");
    const activeTab = editorPanel?.activeTabId
      ? editorPanel.openTabs.get(editorPanel.activeTabId)
      : null;
    return activeTab ? activeTab.path : null;
  }

  handleCompile() {
    this.dispatchEvent(
      new CustomEvent("compile-requested", {
        bubbles: true,
        detail: { filePath: this.#getActiveFilePath() },
      })
    );
  }

  handleExecute() {
    this.dispatchEvent(
      new CustomEvent("execute-requested", {
        bubbles: true,
        detail: { filePath: this.#getActiveFilePath() },
      })
    );
  }

  handleTerminate() {
    const event = new CustomEvent("terminate-requested", { bubbles: true });
    this.dispatchEvent(event);
  }

  setCompilationStatus(status) {
    this.isCompiling = status === "running";
    this.updateCompileButton();
    this.updateExecuteButton();
  }

  setActiveFileMeta(meta) {
    this.isStdActive = !!meta?.isStd;
    this.updateCompileButton();
    this.updateExecuteButton();
  }

  updateCompileButton() {
    const compileBtn = this.querySelector("#compile");
    if (!compileBtn) return;

    if (this.isCompiling) {
      compileBtn.disabled = true;
      compileBtn.classList.add("loading");
      compileBtn.innerHTML = `
        <i class="icon-loader"></i>
        Compiling...
      `;
    } else {
      compileBtn.disabled = this.isStdActive;
      compileBtn.classList.remove("loading");
      compileBtn.classList.toggle("disabled", this.isStdActive);
      compileBtn.innerHTML = `
        <i class="icon-binary"></i>
        Compile
      `;
    }
  }

  updateExecuteButton() {
    const executeBtn = this.querySelector("#execute");
    if (!executeBtn) return;
    executeBtn.disabled = this.isStdActive;
    executeBtn.classList.toggle("disabled", this.isStdActive);
  }

  attachEventListeners() {
    const compileBtn = this.querySelector("#compile");
    if (compileBtn) {
      compileBtn.addEventListener("click", () => this.handleCompile());
    }
    const executeBtn = this.querySelector("#execute");
    if (executeBtn) {
      executeBtn.addEventListener("click", () => this.handleExecute());
    }
    const terminateBtn = this.querySelector("#terminate");
    if (terminateBtn) {
      terminateBtn.addEventListener("click", () => this.handleTerminate());
    }
    const statusContainer = this.querySelector(".status-container");
    const statusTooltip = this.querySelector(".status-tooltip");
    function showTooltip() {
      statusTooltip.style.display = "block";
      computePosition(statusContainer, statusTooltip, {
        placement: "bottom",
        middleware: [shift({ padding: 5 }), offset(4)],
      }).then(({ x, y }) => {
        statusTooltip.style.top = `${y}px`;
        statusTooltip.style.left = `${x}px`;
      });
    }
    function hideTooltip() {
      statusTooltip.style.display = "none";
    }
    [
      ["mouseenter", showTooltip],
      ["mouseleave", hideTooltip],
      ["focus", showTooltip],
      ["blur", hideTooltip],
    ].forEach(([event, listener]) => {
      statusContainer.addEventListener(event, listener);
    });
  }
}

customElements.define("toolbar-panel", ToolbarPanel);

export { ToolbarPanel };
