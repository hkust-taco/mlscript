package hkmc2

import hkmc2.utils.*, shorthands.*
import io.PlatformPath.given


class WasmCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.wasmCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = WasmCompileTestRunner.cctx

end WasmCompileTestRunner


object WasmCompileTestRunner:
  
  given cctx: CompilerCtx = CompilerCtx.fresh(io.FileSystem.default)

end WasmCompileTestRunner
