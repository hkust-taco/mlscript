let ModuleSource, Compartment;

try {
  const sesModule = await import('https://esm.sh/ses@1.14.0');

  // Compartment is a global constructor added by SES after lockdown
  Compartment = globalThis.Compartment || sesModule.Compartment;

  const endoModuleSource = await import('https://esm.sh/@endo/module-source@1.3.3');
  ModuleSource = endoModuleSource.ModuleSource;

  if (!Compartment) {
    throw new Error('Compartment constructor not found after loading SES');
  }
  if (!ModuleSource) {
    throw new Error('ModuleSource not found in @endo/module-source');
  }
  
  // // lockdown is a global function added by SES
  // if (typeof lockdown === 'function') {
  //   lockdown();
  // } else if (sesModule.lockdown) {
  //   sesModule.lockdown();
  // }
} catch (err) {
  self.postMessage({
    type: 'error',
    payload: `Failed to load worker dependencies: ${err.message}\n${err.stack}`
  });
  throw err;
} finally {
  self.postMessage({ type: "ready" })
}

function normalizePath(path) {
  const parts = [];
  for (const part of path.split('/')) {
    if (!part || part === '.') continue;
    if (part === '..') {
      if (parts.length) parts.pop();
    } else {
      parts.push(part);
    }
  }
  return '/' + parts.join('/');
}

function resolveRelative(specifier, referrer) {
  const idx = referrer.lastIndexOf('/');
  const dir = idx === -1 ? '/' : referrer.slice(0, idx + 1);
  return normalizePath(dir + specifier);
}

// Global error handler for the worker
self.onerror = (message, source, lineno, colno, error) => {
  console.error('[Worker global error]', { message, source, lineno, colno, error });
  self.postMessage({
    type: 'error',
    payload: `Uncaught error in worker: ${message}\n${error?.stack || error || ''}`
  });
  return true; // Prevent default error handling
};

self.onunhandledrejection = (event) => {
  console.error('[Worker unhandled rejection]', event.reason);
  self.postMessage({
    type: 'error',
    payload: `Unhandled promise rejection: ${event.reason?.stack || event.reason}`
  });
  event.preventDefault();
};

self.onmessage = async (event) => {
  try {
    const { type } = event.data;
    if (type !== 'run') return;
    
    self.postMessage({ type: "log", payload: "Message received..." });

    const { mainPath, files } = event.data;
    const fileMap = new Map(Object.entries(files));

    const vmConsole = {
      log: (...args) => {
        self.postMessage({ type: 'console.log', payload: args });
      },
      error: (...args) => {
        self.postMessage({ type: 'console.error', payload: args });
      },
      warn: (...args) => {
        self.postMessage({ type: 'console.warn', payload: args });
      },
    };

    const endowments = {
      console: vmConsole,
      fetch,
      structuredClone,
    };

    const compartment = new Compartment(endowments, {}, {
      resolveHook(moduleSpecifier, moduleReferrer) {
        self.postMessage({ type: "log", payload: `Resolving module: ${moduleSpecifier} from ${moduleReferrer}` });
        if (moduleSpecifier.startsWith('./') || moduleSpecifier.startsWith('../')) {
          return resolveRelative(moduleSpecifier, moduleReferrer);
        }
        if (moduleSpecifier.startsWith('/')) {
          return normalizePath(moduleSpecifier);
        }
        return moduleSpecifier;
      },
      importHook(fullSpecifier) {
        const path = normalizePath(fullSpecifier);
        const src = fileMap.get(path);
        if (src == null) {
          throw new Error(`Module not found: ${path}`);
        }
        self.postMessage({ type: "log", payload: `Importing module: ${path}` });
        return new ModuleSource(src, path);
      },
    });

    try {
      self.postMessage({ type: "log", payload: "Importing the main module..." });
      await compartment.import(normalizePath(mainPath));
      self.postMessage({ type: 'done', payload: null });
    } catch (err) {
      const msg = err && err.stack ? String(err.stack) : String(err);
      self.postMessage({ type: 'error', payload: Object.keys(err) });
      self.postMessage({ type: 'error', payload: msg });
    }
  } catch (err) {
    // Catch any errors in the message handler setup
    const msg = `Error in worker message handler: ${err?.stack || err}`;
    console.error(msg);
    self.postMessage({ type: 'error', payload: msg });
  }
};
