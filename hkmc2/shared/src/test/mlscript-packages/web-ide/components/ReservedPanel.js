import fs from "../filesystem/fs.mjs";
import PanelPersistence from './PanelPersistence.mjs';
import './ResizeHandle.js';

// Reserved Panel Custom Element
class ReservedPanel extends HTMLElement {
  constructor() {
    super();
    this.isCollapsed = false;
    this.collapsedFiles = new Set();
    this.collapsedDiagnostics = new Set();
  }

  connectedCallback() {
    this.render();
    this.attachEventListeners();
    this.restoreSizeFromStorage();
  }

  restoreSizeFromStorage() {
    PanelPersistence.restorePanelWidth(this, 'reserved-panel-width', 150, 600);
  }

  saveSizeToStorage(width) {
    PanelPersistence.savePanelWidth('reserved-panel-width', width);
  }

  render() {
    this.innerHTML = `
      <resize-handle direction="horizontal" side="right" min-size="150" max-size="600"></resize-handle>
      <div class="header">
        <h2>Diagnostics</h2>
        <button class="collapse-btn" title="Toggle panel">
          <i class="icon-arrow-right-to-line"></i>
        </button>
      </div>
      <div class="content">
        <div class="empty-state">
          <i class="icon-circle-check-big"></i>
          <span>No diagnostics yet</span>
        </div>
      </div>
    `;
  }

  getKindIcon(kind) {
    const icons = {
      'error': 'icon-circle-x',
      'warning': 'icon-triangle-alert',
      'internal': 'icon-bug'
    };
    return icons[kind] || 'icon-circle-alert';
  }

  getSourceOrder(source) {
    const order = {
      'lexing': 1,
      'parsing': 2,
      'typing': 3,
      'compilation': 4,
      'runtime': 5
    };
    return order[source] || 999;
  }

  getLineAndColumn(text, offset) {
    const lines = text.substring(0, offset).split('\n');
    const line = lines.length;
    const column = lines[lines.length - 1].length + 1;
    return { line, column };
  }

  extractCodeSnippet(text, start, end) {
    const startPos = this.getLineAndColumn(text, start);
    const endPos = this.getLineAndColumn(text, end);

    const lines = text.split('\n');
    const snippetLines = [];

    for (let i = startPos.line - 1; i < endPos.line; i++) {
      if (i < lines.length) {
        snippetLines.push({
          lineNumber: i + 1,
          content: lines[i]
        });
      }
    }

    return {
      startLine: startPos.line,
      startColumn: startPos.column,
      endLine: endPos.line,
      endColumn: endPos.column,
      lines: snippetLines
    };
  }

  setDiagnostics(diagnosticsPerFile) {
    const content = this.querySelector('.content');
    if (!content) return;

    // Check if there are any diagnostics
    const hasErrors = diagnosticsPerFile && diagnosticsPerFile.some(file =>
      file.diagnostics && file.diagnostics.length > 0
    );

    if (!hasErrors) {
      content.innerHTML = `
        <div class="success-state">
          <i class="icon-circle-check"></i>
          <span>Everything works fine!</span>
        </div>
      `;
      return;
    }

    let html = '<div class="diagnostics-container">';

    diagnosticsPerFile.forEach((fileData, fileIndex) => {
      const { path, diagnostics } = fileData;

      if (!diagnostics || diagnostics.length === 0) return;

      // Read the file content for extracting code snippets
      const fileContent = fs.read(path);

      const fileId = `file-${fileIndex}`;
      const isFileCollapsed = this.collapsedFiles.has(fileId);

      // Sort diagnostics by source order
      const sortedDiagnostics = [...diagnostics].sort((a, b) =>
        this.getSourceOrder(a.source) - this.getSourceOrder(b.source)
      );

      html += `<div class="file-diagnostics" data-file-id="${fileId}">`;
      html += `<div class="file-header" data-file-id="${fileId}">`;
      html += `<i class="file-toggle-icon ${isFileCollapsed ? 'icon-chevron-right' : 'icon-chevron-down'}"></i>`;
      html += `<span class="file-path">${this.escapeHtml(path)}</span>`;
      html += `<button class="collapse-all-btn" data-file-id="${fileId}" title="Collapse/Expand all diagnostics">`;
      html += `<i class="icon-list-chevrons-down-up"></i>`;
      html += `</button>`;
      html += `<span class="file-diagnostic-count">${diagnostics.length}</span>`;
      html += `</div>`;

      if (!isFileCollapsed) {
        html += `<div class="file-diagnostic-list">`;

        sortedDiagnostics.forEach((diagnostic, diagIndex) => {
          const { kind, source, mainMessage, allMessages } = diagnostic;
          const diagId = `${fileId}-diag-${diagIndex}`;
          const isDiagCollapsed = this.collapsedDiagnostics.has(diagId);

          html += `<div class="diagnostic diagnostic-${kind}" data-diag-id="${diagId}" data-main-message="${this.escapeHtml(mainMessage)}">`;
          html += `<div class="diagnostic-summary" data-diag-id="${diagId}">`;
          html += `<div class="diagnostic-header">`;
          html += `<i class="diagnostic-icon ${this.getKindIcon(kind)}"></i>`;
          html += `<span class="diagnostic-label">`;
          html += `<span class="diagnostic-kind">${this.escapeHtml(kind.charAt(0).toUpperCase() + kind.slice(1))}</span>`;
          html += `<span class="diagnostic-source">(${this.escapeHtml(source.charAt(0).toUpperCase() + source.slice(1))})</span>`;
          html += `</span>`;
          html += `<i class="diagnostic-toggle-icon ${isDiagCollapsed ? 'icon-chevron-right' : 'icon-chevron-down'}"></i>`;
          html += `</div>`;

          if (isDiagCollapsed) {
            html += `<div class="diagnostic-main-message">${this.escapeHtml(mainMessage)}</div>`;
          }

          html += `</div>`;

          if (!isDiagCollapsed && allMessages && allMessages.length > 0) {
            html += `<div class="diagnostic-details">`;
            allMessages.forEach(message => {
              const { messageBits, location } = message;
              html += `<div class="diagnostic-message">`;

              if (messageBits && messageBits.length > 0) {
                html += `<div class="message-content">`;
                messageBits.forEach(bit => {
                  if (bit.code) {
                    html += `<code class="message-code">${this.escapeHtml(bit.code)}</code>`;
                  } else if (bit.text) {
                    html += `<span class="message-text">${this.escapeHtml(bit.text)}</span>`;
                  }
                });
                html += `</div>`;
              }

              if (location && fileContent) {
                const snippet = this.extractCodeSnippet(fileContent, location.start, location.end);

                html += `<div class="code-snippet">`;
                html += `<div class="code-snippet-header">`;
                html += `<span class="snippet-location">Line ${snippet.startLine}:${snippet.startColumn}</span>`;
                html += `<button class="goto-location-btn" data-file-path="${this.escapeHtml(path)}" data-line="${snippet.startLine}" title="Go to location">`;
                html += `<i class="icon-locate"></i>`;
                html += `</button>`;
                html += `</div>`;
                snippet.lines.forEach(({ lineNumber, content }) => {
                  html += `<div class="code-line">`;
                  html += `<span class="line-number">${lineNumber}</span>`;
                  html += `<pre class="line-content">`;

                  // Check if this line contains the highlight range
                  if (lineNumber === snippet.startLine && lineNumber === snippet.endLine) {
                    // Single line highlight
                    const before = content.substring(0, snippet.startColumn - 1);
                    const highlighted = content.substring(snippet.startColumn - 1, snippet.endColumn - 1);
                    const after = content.substring(snippet.endColumn - 1);
                    html += this.escapeHtml(before);
                    html += `<mark class="highlight">${this.escapeHtml(highlighted)}</mark>`;
                    html += this.escapeHtml(after);
                  } else if (lineNumber === snippet.startLine) {
                    // Start of multi-line highlight
                    const before = content.substring(0, snippet.startColumn - 1);
                    const highlighted = content.substring(snippet.startColumn - 1);
                    html += this.escapeHtml(before);
                    html += `<mark class="highlight">${this.escapeHtml(highlighted)}</mark>`;
                  } else if (lineNumber === snippet.endLine) {
                    // End of multi-line highlight
                    const highlighted = content.substring(0, snippet.endColumn - 1);
                    const after = content.substring(snippet.endColumn - 1);
                    html += `<mark class="highlight">${this.escapeHtml(highlighted)}</mark>`;
                    html += this.escapeHtml(after);
                  } else if (lineNumber > snippet.startLine && lineNumber < snippet.endLine) {
                    // Middle of multi-line highlight
                    html += `<mark class="highlight">${this.escapeHtml(content)}</mark>`;
                  } else {
                    html += this.escapeHtml(content);
                  }

                  html += `</pre>`;
                  html += `</div>`;
                });
                html += `</div>`;
              }

              html += `</div>`;
            });
            html += `</div>`;
          }

          html += `</div>`;
        });

        html += `</div>`;
      }

      html += `</div>`;
    });

    html += '</div>';
    content.innerHTML = html;
    this.attachDiagnosticListeners();
  }

  attachDiagnosticListeners() {
    // File toggle listeners
    this.querySelectorAll('.file-header').forEach(header => {
      header.addEventListener('click', (e) => {
        const fileId = e.currentTarget.dataset.fileId;
        if (this.collapsedFiles.has(fileId)) {
          this.collapsedFiles.delete(fileId);
        } else {
          this.collapsedFiles.add(fileId);
        }
        // Re-render to reflect the change
        const content = this.querySelector('.content');
        const diagnosticsContainer = content.querySelector('.diagnostics-container');
        if (diagnosticsContainer) {
          // Trigger a re-render by finding the parent caller
          // For now, we'll just toggle classes directly
          const fileBlock = this.querySelector(`.file-diagnostics[data-file-id="${fileId}"]`);
          const list = fileBlock.querySelector('.file-diagnostic-list');
          const icon = header.querySelector('.file-toggle-icon');
          if (list) {
            list.style.display = list.style.display === 'none' ? 'block' : 'none';
          }
          if (icon) {
            icon.className = icon.classList.contains('icon-chevron-right')
              ? 'file-toggle-icon icon-chevron-down'
              : 'file-toggle-icon icon-chevron-right';
          }
        }
      });
    });

    // Diagnostic toggle listeners
    this.querySelectorAll('.diagnostic-summary').forEach(summary => {
      summary.addEventListener('click', (e) => {
        const diagId = e.currentTarget.dataset.diagId;
        const diagnostic = this.querySelector(`.diagnostic[data-diag-id="${diagId}"]`);
        const details = diagnostic.querySelector('.diagnostic-details');
        let mainMessage = summary.querySelector('.diagnostic-main-message');
        const toggleIcon = summary.querySelector('.diagnostic-toggle-icon');

        if (this.collapsedDiagnostics.has(diagId)) {
          // Expand: show details, hide main message
          this.collapsedDiagnostics.delete(diagId);
          if (details) details.style.display = 'block';
          if (mainMessage) mainMessage.remove();
          if (toggleIcon) toggleIcon.className = 'diagnostic-toggle-icon icon-chevron-down';
        } else {
          // Collapse: hide details, show main message
          this.collapsedDiagnostics.add(diagId);
          if (details) details.style.display = 'none';

          // Create and insert main message if it doesn't exist
          if (!mainMessage) {
            const mainMessageText = diagnostic.dataset.mainMessage;
            mainMessage = document.createElement('div');
            mainMessage.className = 'diagnostic-main-message';
            mainMessage.textContent = mainMessageText;
            summary.appendChild(mainMessage);
          }

          if (toggleIcon) toggleIcon.className = 'diagnostic-toggle-icon icon-chevron-right';
        }
      });
    });

    // Go to location button listeners
    this.querySelectorAll('.goto-location-btn').forEach(btn => {
      btn.addEventListener('click', (e) => {
        e.stopPropagation();
        const filePath = e.currentTarget.dataset.filePath;
        const line = parseInt(e.currentTarget.dataset.line, 10);

        // Dispatch a custom event to open the file at the specific line
        document.dispatchEvent(new CustomEvent('open-file-at-location', {
          detail: { filePath, line }
        }));
      });
    });

    // Collapse all diagnostics button listeners
    this.querySelectorAll('.collapse-all-btn').forEach(btn => {
      btn.addEventListener('click', (e) => {
        e.stopPropagation();
        const fileId = e.currentTarget.dataset.fileId;
        const fileBlock = this.querySelector(`.file-diagnostics[data-file-id="${fileId}"]`);
        const diagnostics = fileBlock.querySelectorAll('.diagnostic');
        const icon = btn.querySelector('i');

        // Check if all are currently collapsed
        let allCollapsed = true;
        diagnostics.forEach(diagnostic => {
          const diagId = diagnostic.dataset.diagId;
          if (!this.collapsedDiagnostics.has(diagId)) {
            allCollapsed = false;
          }
        });

        if (allCollapsed) {
          // Expand all
          diagnostics.forEach(diagnostic => {
            const diagId = diagnostic.dataset.diagId;
            this.collapsedDiagnostics.delete(diagId);
            const details = diagnostic.querySelector('.diagnostic-details');
            const mainMessage = diagnostic.querySelector('.diagnostic-main-message');
            const toggleIcon = diagnostic.querySelector('.diagnostic-toggle-icon');
            if (details) details.style.display = 'block';
            if (mainMessage) mainMessage.remove();
            if (toggleIcon) toggleIcon.className = 'diagnostic-toggle-icon icon-chevron-down';
          });
          icon.className = 'icon-list-chevrons-down-up';
        } else {
          // Collapse all
          diagnostics.forEach(diagnostic => {
            const diagId = diagnostic.dataset.diagId;
            this.collapsedDiagnostics.add(diagId);
            const summary = diagnostic.querySelector('.diagnostic-summary');
            const details = diagnostic.querySelector('.diagnostic-details');
            let mainMessage = summary.querySelector('.diagnostic-main-message');
            const toggleIcon = diagnostic.querySelector('.diagnostic-toggle-icon');

            if (details) details.style.display = 'none';

            if (!mainMessage) {
              const mainMessageText = diagnostic.dataset.mainMessage;
              mainMessage = document.createElement('div');
              mainMessage.className = 'diagnostic-main-message';
              mainMessage.textContent = mainMessageText;
              summary.appendChild(mainMessage);
            }

            if (toggleIcon) toggleIcon.className = 'diagnostic-toggle-icon icon-chevron-right';
          });
          icon.className = 'icon-list-chevrons-up-down';
        }
      });
    });
  }

  escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
  }

  toggleCollapse() {
    this.isCollapsed = !this.isCollapsed;
    this.classList.toggle('collapsed', this.isCollapsed);

    const container = document.querySelector('.app-container');

    if (!this.isCollapsed) {
      // Restore previous width or use default
      const width = this.getAttribute('width');
      if (width) {
        container.style.setProperty('--reserved-panel-width', `${width}px`);
      } else {
        container.style.removeProperty('--reserved-panel-width');
      }
    }
    // Collapsed state (40px) is handled by CSS :has() selector
  }

  attachEventListeners() {
    const collapseBtn = this.querySelector('.collapse-btn');
    if (collapseBtn) {
      collapseBtn.addEventListener('click', () => this.toggleCollapse());
    }
  }
}

customElements.define('reserved-panel', ReservedPanel);

export { ReservedPanel };
