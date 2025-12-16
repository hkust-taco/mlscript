import { getAllFiles } from "../filesystem/fs.js";

/**
 * The latest execution instance. It is `null` if there is no execution.
 * @type {{ id: string, worker: Worker, isRunning: boolean, startTime: number } | null}
 */
let latestExecution = null;

function dispatchStatusChange(status, runningTime = null) {
  const event = new CustomEvent('execution-status-change', {
    detail: { status, runningTime },
    bubbles: true
  });
  window.dispatchEvent(event);
}

/**
 * Execute the compiled JavaScript program in a Web Worker. If there is an
 * existing execution running, it will not start a new one.
 * 
 * @param {string} mainPath the path to the entry point JavaScript file
 * @returns {void}
 */
export function execute(mainPath) {
  if (latestExecution !== null) {
    if (latestExecution.isRunning) {
      // TODO: Show this error message using a toast notification.
      console.log("The previous execution is still running. Stop it before starting a new one.");
      return;
    } else {
      console.log("Clean up the previous execution.");
      latestExecution.worker.terminate();
      latestExecution = null;
    }
  }

  // Clear console before each execution (unless preserve logs is enabled)
  const consolePanel = document.querySelector('console-panel');
  if (consolePanel) {
    consolePanel.clear();
  }

  console.log(`[VM] Starting new execution for ${mainPath}`);

  const id = Date.now().toString();

  const execution = {
    id,
    worker: new Worker('execution/worker.js', { type: 'module' }),
    isRunning: false,
    startTime: null,
  };

  latestExecution = execution;

  function run() {
    const files = getAllFiles();
    console.log("[VM] Files:", Object.keys(files));
    execution.worker.postMessage({ type: 'run', id, mainPath, files });
  }

  execution.worker.onmessage = (event) => {
    if (latestExecution?.id !== id) {
      console.error('Received message from outdated worker, terminating it.');
      latestExecution.worker.terminate();
      return;
    }
    const { type, payload } = event.data;
    const consolePanel = document.querySelector('console-panel');

    switch (type) {
      case 'ready':
        console.log('[VM]', 'Ready to run.');
        execution.isRunning = true;
        execution.startTime = Date.now();
        dispatchStatusChange('running');
        run();
        break;
      case 'log':
        console.log('[VM]', payload);
        break;
      case 'error':
        console.error('[VM]', payload);
        execution.isRunning = false;
        dispatchStatusChange('error');
        break;
      case 'done':
        console.log('[VM]', payload);
        execution.isRunning = false;
        const runningTime = execution.startTime ? Date.now() - execution.startTime : null;
        dispatchStatusChange('done', runningTime);
        break;
      // Forward console messages from the VM.
      case 'console.log':
        console.log('[Execution]', ...payload);
        if (consolePanel) consolePanel.log('log', ...payload);
        break;
      case 'console.error':
        console.error('[Execution]', ...payload);
        if (consolePanel) consolePanel.log('error', ...payload);
        break;
      case 'console.warn':
        console.warn('[Execution]', ...payload);
        if (consolePanel) consolePanel.log('warn', ...payload);
        break;
    }
  };

  execution.worker.onerror = (event) => {
    console.error('[Worker error event]', {
      message: event.message,
      filename: event.filename,
      lineno: event.lineno,
      colno: event.colno,
      error: event.error,
      fullEvent: event
    });
    execution.isRunning = false;
    dispatchStatusChange('fatal');

    // Display the error in the console panel
    const consolePanel = document.querySelector('console-panel');
    if (consolePanel) {
      consolePanel.log('error', `Worker Error: ${event.message || 'Unknown error'}`);
      if (event.filename) {
        consolePanel.log('error', `  at ${event.filename}:${event.lineno}:${event.colno}`);
      }
      if (event.error?.stack) {
        consolePanel.log('error', event.error.stack);
      }
    }

    // Also display in the output panel
    const reservedPanel = document.querySelector('reserved-panel');
    if (reservedPanel) {
      let errorMsg = 'Worker Error:\n';
      if (event.message) errorMsg += `Message: ${event.message}\n`;
      if (event.filename) errorMsg += `File: ${event.filename}\n`;
      if (event.lineno) errorMsg += `Line: ${event.lineno}:${event.colno}\n`;
      if (event.error) errorMsg += `\nStack:\n${event.error.stack || event.error}`;
      reservedPanel.setOutput(errorMsg);
    }
  };

  execution.worker.addEventListener("messageerror", function (event) {
    console.error('[Worker message error]', event);
    execution.isRunning = false;
    dispatchStatusChange('fatal');

    const consolePanel = document.querySelector('console-panel');
    if (consolePanel) {
      consolePanel.log('error', 'Worker Message Error: Failed to deserialize message from worker');
    }

    const reservedPanel = document.querySelector('reserved-panel');
    if (reservedPanel) {
      reservedPanel.setOutput('Worker Message Error: Failed to deserialize message from worker');
    }
  });
}

export function terminate() {
  if (latestExecution !== null && latestExecution.isRunning) {
    console.log('[VM] Terminating worker...');
    latestExecution.worker.terminate();
    latestExecution.isRunning = false;
    dispatchStatusChange('aborted');

    const consolePanel = document.querySelector('console-panel');
    if (consolePanel) {
      consolePanel.log('warn', 'Execution terminated by user');
    }

    latestExecution = null;
  }
}