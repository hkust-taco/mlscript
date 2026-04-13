package hkmc2

import mlscript.utils._, shorthands._
import io.PlatformPath.given


class NofibCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.nofibCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = NofibCompileTestRunner.cctx

end NofibCompileTestRunner


object NofibCompileTestRunner:
  
  given cctx: CompilerCtx = CompilerCtx.fresh(io.FileSystem.default)

end NofibCompileTestRunner

