package hkmc2

import hkmc2.utils.*, shorthands.*


class NofibCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.nofibCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = NofibCompileTestRunner.cctx

end NofibCompileTestRunner


object NofibCompileTestRunner:
  
  given cctx: CompilerCtx = TestFolders.compilerCtx(os.pwd)

end NofibCompileTestRunner
