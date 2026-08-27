package hkmc2

import hkmc2.utils.*, shorthands.*


class WasmCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.wasmCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = WasmCompileTestRunner.cctx

end WasmCompileTestRunner


object WasmCompileTestRunner:
  
  given cctx: CompilerCtx = TestFolders.compilerCtx(os.pwd)

end WasmCompileTestRunner
