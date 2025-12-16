package hkmc2

import org.scalatest.{funsuite, funspec, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}

import mlscript.utils.*, shorthands.*
import io.PlatformPath.given

import AppTestRunner.given

/**
  * A simple test runner that compiles apps written in MLscript.
  */
class AppTestRunner
  extends funspec.AnyFunSpec
  // with ParallelTestExecution // Can `MLsCompiler` handle parallel compilation?
  // with TimeLimitedTests // TODO
:
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  // val timeLimit = TimeLimit
  
  val mainTestDir = os.pwd / "hkmc2" / "shared" / "src" / "test"
  val appsDir = mainTestDir / "mlscript-apps"
  val stdlibDir = mainTestDir / "mlscript-compile"
  
  val paths = new MLsCompiler.Paths:
    val preludeFile = mainTestDir / "mlscript" / "decls" / "Prelude.mls"
    val runtimeFile = stdlibDir / "Runtime.mjs"
    val termFile = stdlibDir / "Term.mjs"
  
  for app <- os.list(appsDir).filter(os.isDir) do
    val allFiles = os.walk(app).filter(os.isFile).filter(_.ext == "mls").toSeq
    val appName = app.baseName
    
    given Config = Config.default
    val wrap: (=> Unit) => Unit = body => AppTestRunner.synchronized(body)
    val report = ReportFormatter(System.out.println, colorize = true, wrap = Some(wrap))
    val compiler = MLsCompiler(paths, mkRaise = report.mkRaise)
    
    describe(s"$appName (${"file" countBy allFiles.size})"):
    
      allFiles.foreach: file =>
        val relativeName = file.relativeTo(app).toString()
        
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
  
  given cctx: CompilerCtx = CompilerCtx.fresh(io.FileSystem.default)
  
end AppTestRunner
