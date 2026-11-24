import RuntimeWasm from "../RuntimeWasm.mjs";
const loaded = await RuntimeWasm.loadModule(import.meta.url, { runtime: { path: "../RuntimeWasm.wat", entry: "entry" },
  wat: "./Box.wat", entry: "entry", pages: 0,
  dependencies: [], export: { kind: "function", name: "Box_ctor", optionalParams: [], constructor: null } }, { importModule: url => import(url), apply: (fn, receiver, args) => ({ value: Reflect.apply(fn, receiver, args) }) });
export const wasmExports = loaded.wasmExports;
export default loaded.defaultExport;
