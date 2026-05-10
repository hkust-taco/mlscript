import fs from "../filesystem/fs.mjs";
import {
  computePosition,
  shift,
  offset,
} from "https://esm.sh/@floating-ui/dom";

// Shared tooltip element for displaying file metadata in both the editor tabs
// and the file explorer.
class FileTooltip extends HTMLElement {
  constructor() {
    super();
    this.relativeTimeFormatter =
      typeof Intl !== "undefined" && Intl.RelativeTimeFormat
        ? new Intl.RelativeTimeFormat(undefined, { numeric: "auto" })
        : null;
    this.showRequestId = 0;
  }

  connectedCallback() {
    this.classList.add("file-tooltip");
    this.setAttribute("role", "tooltip");
  }

  escapeHtml(str) {
    return String(str).replace(/[&<>"']/g, (ch) => {
      switch (ch) {
        case "&":
          return "&amp;";
        case "<":
          return "&lt;";
        case ">":
          return "&gt;";
        case '"':
          return "&quot;";
        case "'":
          return "&#39;";
        default:
          return ch;
      }
    });
  }

  formatRelativeTime(timestamp) {
    if (!this.relativeTimeFormatter || !Number.isFinite(timestamp)) return "";
    const divisions = [
      { amount: 60, unit: "seconds" },
      { amount: 60, unit: "minutes" },
      { amount: 24, unit: "hours" },
      { amount: 7, unit: "days" },
      { amount: 4.34524, unit: "weeks" },
      { amount: 12, unit: "months" },
      { amount: Number.POSITIVE_INFINITY, unit: "years" },
    ];

    let duration = (timestamp - Date.now()) / 1000;
    for (const division of divisions) {
      if (Math.abs(duration) < division.amount) {
        return this.relativeTimeFormatter.format(
          Math.round(duration),
          division.unit.slice(0, -1)
        );
      }
      duration /= division.amount;
    }
    return "";
  }

  formatTimestamp(value) {
    if (!Number.isFinite(value)) return "—";
    const absolute = new Date(value).toLocaleString(undefined, {
      year: "numeric",
      month: "short",
      day: "numeric",
      hour: "2-digit",
      minute: "2-digit",
    });
    const relative = this.formatRelativeTime(value);
    return relative ? `${absolute} · ${relative}` : absolute;
  }

  formatAttrValue(value) {
    if (value === undefined || value === null) return "—";
    if (typeof value === "object") return JSON.stringify(value);
    if (value === true) return "true";
    if (value === false) return "false";
    return String(value);
  }

  formatSize(size) {
    if (!Number.isFinite(size) || size < 0) return "—";
    if (size === 1) return "1 byte";
    if (size < 1024) return `${size} bytes`;
    const kb = size / 1024;
    if (kb < 1024) return `${kb.toFixed(1)} KB`;
    return `${(kb / 1024).toFixed(1)} MB`;
  }

  buildContent({ path, name, sizeOverride }) {
    if (!path) return null;
    const node = fs.stat(path);
    if (!node) return null;

    const size =
      sizeOverride ??
      (typeof node.content === "string" ? node.content.length : undefined);
    const attrs =
      node.attrs && Object.keys(node.attrs).length > 0
        ? Object.entries(node.attrs)
            .map(
              ([key, value]) =>
                `${key}: ${this.escapeHtml(this.formatAttrValue(value))}`
            )
            .join(", ")
        : "—";

    const displayName = name || node.name || path.split("/").pop();

    return `
      <div class="tooltip-grid">
        <div class="tooltip-label">Name</div>
        <div class="tooltip-value">${this.escapeHtml(displayName)}</div>
        <div class="tooltip-label">Path</div>
        <div class="tooltip-value">${this.escapeHtml(path)}</div>
        <div class="tooltip-label">Size</div>
        <div class="tooltip-value">${this.formatSize(size)}</div>
        <div class="tooltip-label">Modified</div>
        <div class="tooltip-value">${this.formatTimestamp(node.mtime)}</div>
        <div class="tooltip-label">Created</div>
        <div class="tooltip-value">${this.formatTimestamp(node.birthtime)}</div>
        <div class="tooltip-label">Readonly</div>
        <div class="tooltip-value">${node.readonly ? "Yes" : "No"}</div>
        <div class="tooltip-label">Attributes</div>
        <div class="tooltip-value">${attrs}</div>
      </div>
    `;
  }

  show(targetEl, { path, name, size, placement = "right" } = {}) {
    const content = this.buildContent({
      path,
      name,
      sizeOverride: size,
    });
    if (!content || !targetEl) return;

    console.log("[file-tooltip] request show", {
      path,
      name,
      placement,
      targetPath: targetEl.dataset?.path,
      targetName: targetEl.dataset?.name,
    });

    this.innerHTML = content;
    this.dataset.placement = placement;
    const requestId = ++this.showRequestId;

    computePosition(targetEl, this, {
      placement,
      strategy: "fixed",
      middleware: [shift({ padding: 5 }), offset(8)],
    }).then(({ x, y }) => {
      if (requestId !== this.showRequestId) return;
      this.style.top = `${y}px`;
      this.style.left = `${x}px`;
      this.classList.add("visible");
      console.log("[file-tooltip] shown", {
        path,
        placement,
        x,
        y,
      });
    });
  }

  hide() {
    this.showRequestId++;
    this.classList.remove("visible");
    delete this.dataset.placement;
    console.log("[file-tooltip] hide");
  }
}

customElements.define("file-tooltip", FileTooltip);

export { FileTooltip };
