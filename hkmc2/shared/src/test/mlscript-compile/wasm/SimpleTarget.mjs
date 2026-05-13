import { __mlx_compileWatFromUrl, __mlx_buildSystem } from "./RuntimeWASM.mjs"


const __mlx_wat_url = new URL("./SimpleTarget.wat", import.meta.url)

async function __mlx_importObject() {
  const importObject = {
    system: await __mlx_buildSystem(0)
  }

  return importObject
}

const __mlx_wasmPromise = __mlx_importObject()
  .then(importObject => __mlx_compileWatFromUrl(__mlx_wat_url, importObject))

export const __mlx_wasm = () => __mlx_wasmPromise

const { instance } = await __mlx_wasm()

export default instance.exports["SimpleTarget"]()
