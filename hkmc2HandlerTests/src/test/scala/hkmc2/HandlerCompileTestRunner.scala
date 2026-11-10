package hkmc2

import hkmc2.utils.*, shorthands.*


class HandlerCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.handlerCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = HandlerCompileTestRunner.cctx

end HandlerCompileTestRunner


object HandlerCompileTestRunner:
  
  given cctx: CompilerCtx = TestFolders.compilerCtx(os.pwd)

end HandlerCompileTestRunner
