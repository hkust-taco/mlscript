import { instantiate, system, invoke } from "../RuntimeWasm.mjs";

const instance = await instantiate(new URL("./Box.wat", import.meta.url), { system,  }, 0);
export const wasmExports = instance.exports;
invoke(wasmExports["entry"]);
export default ((...args) => invoke(wasmExports["Box_ctor"], ...args));
