// Panel Persistence Utilities
// Provides localStorage persistence for resizable panels

/**
 * Restore panel width from localStorage
 * @param {HTMLElement} panel - The panel element
 * @param {string} storageKey - localStorage key
 * @param {number} minSize - Minimum valid width
 * @param {number} maxSize - Maximum valid width
 */
export function restorePanelWidth(panel, storageKey, minSize = 150, maxSize = 600) {
  const savedWidth = localStorage.getItem(storageKey);
  if (savedWidth) {
    const width = parseInt(savedWidth, 10);
    // Validate: between minSize and maxSize
    if (width >= minSize && width <= maxSize) {
      const container = document.querySelector('.app-container');
      const cssVar = `--${panel.tagName.toLowerCase()}-width`;
      container.style.setProperty(cssVar, `${width}px`);
      panel.setAttribute('width', width);
    }
  }
}

/**
 * Save panel width to localStorage
 * @param {string} storageKey - localStorage key
 * @param {number} width - Width to save
 */
export function savePanelWidth(storageKey, width) {
  localStorage.setItem(storageKey, width);
}

/**
 * Restore panel height from localStorage
 * @param {HTMLElement} panel - The panel element
 * @param {string} storageKey - localStorage key
 * @param {number} minSize - Minimum valid height
 * @param {number} maxSize - Maximum valid height
 */
export function restorePanelHeight(panel, storageKey, minSize = 100, maxSize = 600) {
  const savedHeight = localStorage.getItem(storageKey);
  if (savedHeight) {
    const height = parseInt(savedHeight, 10);
    // Validate: between minSize and maxSize
    if (height >= minSize && height <= maxSize) {
      panel.style.height = `${height}px`;
      panel.style.minHeight = `${height}px`;
      panel.style.maxHeight = `${height}px`;
      panel.setAttribute('height', height);
    }
  }
}

/**
 * Save panel height to localStorage
 * @param {string} storageKey - localStorage key
 * @param {number} height - Height to save
 */
export function savePanelHeight(storageKey, height) {
  localStorage.setItem(storageKey, height);
}
