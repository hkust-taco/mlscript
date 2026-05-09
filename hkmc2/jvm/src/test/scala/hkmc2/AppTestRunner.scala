package hkmc2

import org.scalatest.{funsuite, funspec, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}

import mlscript.utils.*, shorthands.*
import io.PlatformPath.given

import AppTestRunner.given
import hkmc2.codegen.Local
import hkmc2.io.Path
import hkmc2.io.FileSystem

/**
  * A simple test runner that compiles apps written in MLscript.
  */
class AppTestRunner
  extends funspec.AnyFunSpec
  // with ParallelTestExecution // Can `MLsCompiler` handle parallel compilation?
  // with TimeLimitedTests // TODO
:
  import AppTestRunner.*
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  // val timeLimit = TimeLimit
  
  for appDir <- os.list(appsDir).filter(os.isDir) do
    val allFiles = os.walk(appDir).filter(os.isFile).filter(_.ext == "mls").toSeq
    val appName = appDir.baseName
    
    // The compiler context is created per app to avoid interference.
    given cctx: CompilerCtx = CompilerCtx.fresh(fs, AppModuleResolver(appDir))
    // We might need to read `Config` from a config file later.
    given Config = Config.default(mainTestDir)
    
    val wrap: (=> Unit) => Unit = body => AppTestRunner.synchronized(body)
    val report = ReportFormatter(System.out.println, colorize = true, wrap = Some(wrap))
    val compiler = MLsCompiler(paths, mkRaise = report.mkRaise)
    
    describe(s"$appName (${"file" countBy allFiles.size})"):
    
      allFiles.foreach: file =>
        val relativeName = file.relativeTo(appDir).toString()
        
        it(relativeName):
          
          AppTestRunner.synchronized:
            println(s"Compiling: [${fansi.Bold.On(appName)}] ${fansi.Color.Green(relativeName)}")
          
          assert(true, s"Placeholder test for app: $relativeName")

          compiler.compileModule(file)
          
          if report.badLines.nonEmpty then
            fail(s"Unexpected diagnostic at: " +
              report.badLines.distinct.sorted
                .map("\n\t"+relativeName+"."+file.ext+":"+_).mkString(", "))
end AppTestRunner

object AppTestRunner:
  
  val mainTestDir = os.pwd / "hkmc2" / "shared" / "src" / "test"
  val appsDir = mainTestDir / "mlscript-apps"
  val stdlibDir = mainTestDir / "mlscript-compile"
  
  val paths = new MLsCompiler.Paths:
    val preludeFile = mainTestDir / "mlscript" / "decls" / "Prelude.mls"
    val runtimeFile = stdlibDir / "Runtime.mjs"
    val termFile = stdlibDir / "Term.mjs"
  
  val nodeModulesPath = os.pwd / "node_modules"
  
  given fs: FileSystem = io.FileSystem.default
  
  // TODO: Read from `manifest.json`.
  val vendors = LocalModuleResolver.Vendor("std/", stdlibDir, Ls("*.mls")) :: Nil
  
  // We may use a different module resolver for URL modules in browsers. For
  // example, `import "https://esm.sh/nanoid"` should be accepted.
  class AppModuleResolver(appDir: os.Path) extends LocalModuleResolver(vendors, N):
    private val appVendorDir = appDir / "vendor"
    
    private def getVendoredPath(moduleName: Str): io.Path =
      val dir = appVendorDir / moduleName
      if os.exists(dir) then
        if os.isDir(dir) then dir
        else
          throw new Exception(s"The vendored module path is not a directory: $dir")
      else
        os.makeDir.all(dir)
        dir
  
end AppTestRunner
