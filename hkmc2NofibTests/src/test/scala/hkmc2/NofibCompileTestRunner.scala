package hkmc2

import hkmc2.utils.*, shorthands.*
import io.PlatformPath.given


class NofibCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.nofibCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = NofibCompileTestRunner.cctx

end NofibCompileTestRunner


object NofibCompileTestRunner:
  
  private val workingDir = os.pwd
  private val stdPath = TestFolders.compileTestDir(workingDir)
  private val nodeModulesPath = workingDir / "node_modules"
  
  given cctx: CompilerCtx =
    CompilerCtx.fresh(io.FileSystem.default, LocalModuleResolver(stdPath, S(nodeModulesPath)))

end NofibCompileTestRunner
