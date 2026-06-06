package hkmc2

import hkmc2.utils.*, shorthands.*
import io.PlatformPath.given


class CompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.mainCompileDirs(os.pwd),
  excludedDirs = TestFolders.mainExcludedCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = CompileTestRunner.cctx

end CompileTestRunner


object CompileTestRunner:
  
  given cctx: CompilerCtx = CompilerCtx.fresh(io.FileSystem.default)
  
end CompileTestRunner

