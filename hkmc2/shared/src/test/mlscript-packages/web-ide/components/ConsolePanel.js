import PanelPersistence from './PanelPersistence.mjs';
import './ResizeHandle.mjs';

// Console Panel Custom Element
class ConsolePanel extends HTMLElement {
  constructor() {
    super();
    this.messages = [];
    this.isCollapsed = false;
    this.preserveLogs = false;
  }

  connectedCallback() {
    this.render();
    this.attachEventListeners();
    this.restoreSizeFromStorage();
  }

  restoreSizeFromStorage() {
    PanelPersistence.restorePanelHeight(this, 'console-panel-height', 100, 600);
  }

  saveSizeToStorage(height) {
    PanelPersistence.savePanelHeight('console-panel-height', height);
  }

  render() {
    this.innerHTML = `
      <resize-handle direction="vertical" side="top" min-size="100" max-size="600"></resize-handle>
      <div class="header">
        <div class="header-left">
          <h2>Console</h2>
          <label class="preserve-logs-label" title="Preserve logs between executions">
            <input type="checkbox" class="preserve-logs-checkbox" />
            <span>Preserve logs</span>
          </label>
          <button class="clear-btn" title="Clear console">
            <i class="icon-square-x"></i>
            <span>Clear</span>
          </button>
        </div>
        <button class="collapse-btn" title="Toggle panel">
          <i class="icon-arrow-down-to-line"></i>
        </button>
      </div>
      <div class="console-content"></div>
    `;
  }

  log(type, ...args) {
    const message = {
      type,
      content: args,
      timestamp: new Date()
    };
    this.messages.push(message);
    this.appendMessage(message);
  }

  appendMessage(message) {
    const consoleContent = this.querySelector('.console-content');
    if (!consoleContent) return;

    const messageEl = document.createElement('div');
    messageEl.className = `console-message console-${message.type}`;

    // Format the content
    const formattedContent = message.content.map(arg => {
      if (typeof arg === 'object') {
        try {
          return JSON.stringify(arg, null, 2);
        } catch (e) {
          return String(arg);
        }
      }
      return String(arg);
    }).join(' ');

    // Create icon based on type
    let iconClassName = '';
    switch (message.type) {
      case 'error':
        iconClassName = 'icon-x';
        break;
      case 'warn':
        iconClassName = 'icon-triangle-alert';
        break;
      case 'info':
        iconClassName = 'icon-info';
        break;
      default:
        iconClassName = 'icon-chevron-right';
    }

    messageEl.innerHTML = `
      <span class="console-icon"><i class=${iconClassName}></i></span>
      <span class="console-text">${this.escapeHtml(formattedContent)}</span>
    `;

    consoleContent.appendChild(messageEl);

    // Auto-scroll to bottom
    consoleContent.scrollTop = consoleContent.scrollHeight;
  }

  escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
  }

  clear() {
    if (this.preserveLogs) {
      return;
    }
    this.messages = [];
    const consoleContent = this.querySelector('.console-content');
    if (consoleContent) {
      consoleContent.innerHTML = '';
    }
  }

  toggleCollapse() {
    this.isCollapsed = !this.isCollapsed;

    if (this.isCollapsed) {
      // Store current height before collapsing
      this.dataset.lastHeight = this.style.height || '';
      this.dataset.lastMinHeight = this.style.minHeight || '';
      this.dataset.lastMaxHeight = this.style.maxHeight || '';
      this.style.height = '40px';
      this.style.minHeight = '40px';
      this.style.maxHeight = '40px';
      this.style.flexBasis = '40px';
      this.style.flexGrow = '0';
      this.style.flexShrink = '0';
    } else {
      // Restore previous height or use default
      const lastHeight = this.dataset.lastHeight;
      const lastMinHeight = this.dataset.lastMinHeight;
      const lastMaxHeight = this.dataset.lastMaxHeight;

      if (lastHeight && lastHeight !== '40px') {
        this.style.height = lastHeight;
        this.style.minHeight = lastMinHeight || '';
        this.style.maxHeight = lastMaxHeight || '';
        this.style.flexBasis = lastHeight;
      } else {
        this.style.height = '';
        this.style.minHeight = '';
        this.style.maxHeight = '';
        this.style.flexBasis = '';
        this.style.flexGrow = '';
        this.style.flexShrink = '';
      }
    }

    this.classList.toggle('collapsed', this.isCollapsed);
  }

  attachEventListeners() {
    const clearBtn = this.querySelector('.clear-btn');
    if (clearBtn) {
      clearBtn.addEventListener('click', () => this.clear());
    }

    const collapseBtn = this.querySelector('.collapse-btn');
    if (collapseBtn) {
      collapseBtn.addEventListener('click', () => this.toggleCollapse());
    }

    const preserveLogsCheckbox = this.querySelector('.preserve-logs-checkbox');
    if (preserveLogsCheckbox) {
      preserveLogsCheckbox.addEventListener('change', (e) => {
        this.preserveLogs = e.target.checked;
      });
    }
  }
}

customElements.define('console-panel', ConsolePanel);

export { ConsolePanel };
