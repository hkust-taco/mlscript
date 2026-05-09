package hkmc2

import mlscript.utils._, shorthands._
import io.PlatformPath.given


class AppsCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.appsCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = AppsCompileTestRunner.cctx

end AppsCompileTestRunner


object AppsCompileTestRunner:
  
  private val workingDir = os.pwd
  private val stdPath = TestFolders.compileTestDir(workingDir)
  private val nodeModulesPath = workingDir / "node_modules"
  
  given cctx: CompilerCtx =
    CompilerCtx.fresh(io.FileSystem.default, LocalModuleResolver(stdPath, S(nodeModulesPath)))

end AppsCompileTestRunner
