package hkmc2

import hkmc2.utils.*, shorthands.*


class CompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.mainCompileDirs(os.pwd),
  excludedDirs = TestFolders.mainExcludedCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = CompileTestRunner.cctx

end CompileTestRunner


object CompileTestRunner:
  
  given cctx: CompilerCtx = TestFolders.compilerCtx(os.pwd)
  
end CompileTestRunner
