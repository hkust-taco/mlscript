package hkmc2

import mlscript.utils._, shorthands._
import io.PlatformPath.given


class AppsCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.appsCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = AppsCompileTestRunner.cctx

end AppsCompileTestRunner


object AppsCompileTestRunner:
  
  given cctx: CompilerCtx = CompilerCtx.fresh(io.FileSystem.default)

end AppsCompileTestRunner

