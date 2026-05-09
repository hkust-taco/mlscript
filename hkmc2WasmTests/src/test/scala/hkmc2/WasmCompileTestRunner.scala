package hkmc2

import mlscript.utils._, shorthands._
import io.PlatformPath.given


class WasmCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.wasmCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = WasmCompileTestRunner.cctx

end WasmCompileTestRunner


object WasmCompileTestRunner:
  
  private val workingDir = os.pwd
  private val stdPath = TestFolders.compileTestDir(workingDir)
  private val nodeModulesPath = workingDir / "node_modules"
  
  given cctx: CompilerCtx =
    CompilerCtx.fresh(io.FileSystem.default, LocalModuleResolver(stdPath, S(nodeModulesPath)))

end WasmCompileTestRunner
