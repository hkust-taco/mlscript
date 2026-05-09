// Resize Handle Custom Element
class ResizeHandle extends HTMLElement {
  constructor() {
    super();
    this.isResizing = false;
    this.startX = 0;
    this.startY = 0;
    this.startSize = 0;
  }

  connectedCallback() {
    this.render();
    this.attachEventListeners();
  }

  render() {
    const direction = this.getAttribute('direction') || 'horizontal';
    this.className = `resize-handle resize-handle-${direction}`;
    this.innerHTML = `<div class="resize-handle-indicator"></div>`;
  }

  attachEventListeners() {
    this.addEventListener('mousedown', this.startResize.bind(this));
  }

  startResize(e) {
    e.preventDefault();

    const direction = this.getAttribute('direction') || 'horizontal';
    const target = this.getAttribute('target');
    // Target is the parent element (the panel itself)
    const targetElement = target ? document.querySelector(target) : this.parentElement;

    if (!targetElement) return;

    this.isResizing = true;
    this.startX = e.clientX;
    this.startY = e.clientY;

    if (direction === 'horizontal') {
      this.startSize = targetElement.offsetWidth;
    } else {
      this.startSize = targetElement.offsetHeight;
    }

    document.body.style.cursor = direction === 'horizontal' ? 'ew-resize' : 'ns-resize';
    document.body.style.userSelect = 'none';
    this.classList.add('active');

    const handleMouseMove = (e) => this.handleResize(e, targetElement, direction);
    const handleMouseUp = () => this.stopResize(handleMouseMove, handleMouseUp, targetElement);

    document.addEventListener('mousemove', handleMouseMove);
    document.addEventListener('mouseup', handleMouseUp);
  }

  handleResize(e, targetElement, direction) {
    if (!this.isResizing) return;

    const minSize = parseInt(this.getAttribute('min-size')) || 150;
    const maxSize = parseInt(this.getAttribute('max-size')) || 600;

    if (direction === 'horizontal') {
      const deltaX = e.clientX - this.startX;
      const side = this.getAttribute('side') || 'left';
      const newWidth = side === 'left' ? this.startSize + deltaX : this.startSize - deltaX;

      const clampedWidth = Math.max(minSize, Math.min(maxSize, newWidth));

      // Use CSS custom properties for grid-based layouts
      const container = document.querySelector('.app-container');
      if (targetElement.tagName.toLowerCase() === 'file-explorer') {
        container.style.setProperty('--file-explorer-width', `${clampedWidth}px`);
        targetElement.setAttribute('width', clampedWidth);
      } else if (targetElement.tagName.toLowerCase() === 'reserved-panel') {
        container.style.setProperty('--reserved-panel-width', `${clampedWidth}px`);
        targetElement.setAttribute('width', clampedWidth);
      }
    } else {
      const deltaY = e.clientY - this.startY;
      const side = this.getAttribute('side') || 'top';
      // For console panel at bottom with handle at top: dragging up (negative deltaY) should increase height
      const newHeight = side === 'top' ? this.startSize - deltaY : this.startSize + deltaY;

      const clampedHeight = Math.max(minSize, Math.min(maxSize, newHeight));

      // For console panel, set height directly
      targetElement.style.height = `${clampedHeight}px`;
      targetElement.style.minHeight = `${clampedHeight}px`;
      targetElement.style.maxHeight = `${clampedHeight}px`;
      targetElement.setAttribute('height', clampedHeight);
    }

    // Dispatch resize event for panels to update internal state
    targetElement.dispatchEvent(new CustomEvent('panel-resize', {
      detail: {
        width: targetElement.offsetWidth,
        height: targetElement.offsetHeight
      }
    }));
  }

  stopResize(handleMouseMove, handleMouseUp, targetElement) {
    this.isResizing = false;
    document.body.style.cursor = '';
    document.body.style.userSelect = '';
    this.classList.remove('active');

    document.removeEventListener('mousemove', handleMouseMove);
    document.removeEventListener('mouseup', handleMouseUp);

    // Save the size to localStorage
    if (targetElement && targetElement.saveSizeToStorage) {
      const direction = this.getAttribute('direction') || 'horizontal';
      if (direction === 'horizontal') {
        const width = parseInt(targetElement.getAttribute('width'));
        if (!isNaN(width)) {
          targetElement.saveSizeToStorage(width);
        }
      } else {
        const height = parseInt(targetElement.getAttribute('height'));
        if (!isNaN(height)) {
          targetElement.saveSizeToStorage(height);
        }
      }
    }
  }
}

customElements.define('resize-handle', ResizeHandle);

export { ResizeHandle };