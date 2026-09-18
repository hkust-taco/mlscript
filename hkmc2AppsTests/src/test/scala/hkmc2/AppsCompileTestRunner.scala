package hkmc2

import hkmc2.utils.*, shorthands.*


class AppsCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.appsCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = AppsCompileTestRunner.cctx

end AppsCompileTestRunner


object AppsCompileTestRunner:
  
  given cctx: CompilerCtx = TestFolders.compilerCtx(os.pwd)

end AppsCompileTestRunner
