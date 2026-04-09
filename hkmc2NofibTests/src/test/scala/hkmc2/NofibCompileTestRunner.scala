package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}
import os.up

import mlscript.utils._, shorthands._
import io.PlatformPath.given

import NofibCompileTestRunner.given


class NofibCompileTestRunner
  extends funsuite.AnyFunSuite
  with ParallelTestExecution
:
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  val pwd = os.pwd
  val workingDir = pwd

  val mainTestDir = workingDir/"hkmc2"/"shared"/"src"/"test"  
  
  val dirs = workingDir/"hkmc2Benchmarks"/"src"/"test" :: Nil
  
  val validExt = Set("mls")
    
  for dir <- dirs do {
    val allFiles = os.walk(dir)
      .filter(_.toIO.isFile)
      .filter(_.ext in validExt)
      
    lazy val compileTestFiles = allFiles.filter: file =>
        file.segments.contains("mlscript-compile")
    
    compileTestFiles.foreach: file =>
      
      val basePath = file.segments.drop(dir.segmentCount).toList.init
      val relativeName = basePath.map(_ + "/").mkString + file.baseName
      
      test(relativeName):
        
        NofibCompileTestRunner.synchronized:
          println(s"Compiling: $relativeName")
        
        given Config = Config.default(mainTestDir)
        
        val wrap: (=> Unit) => Unit = body => NofibCompileTestRunner.synchronized(body)
        val report = ReportFormatter(System.out.println, colorize = true, wrap = Some(wrap))
        val compiler = MLsCompiler(
          paths = new MLsCompiler.Paths:
            val preludeFile = mainTestDir / "mlscript" / "decls" / "Prelude.mls"
            val runtimeFile = mainTestDir / "mlscript-compile" / "Runtime.mjs"
            val termFile = mainTestDir / "mlscript-compile" / "Term.mjs",
          mkRaise = report.mkRaise
        )
        compiler.compileModule(file)
        
        if report.badLines.nonEmpty then
          fail(s"Unexpected diagnostic at: " +
            report.badLines.distinct.sorted
              .map("\n\t"+relativeName+"."+file.ext+":"+_).mkString(", "))
  }
      
end NofibCompileTestRunner


object NofibCompileTestRunner:
  
  given cctx: CompilerCtx = CompilerCtx.fresh(io.FileSystem.default)

end NofibCompileTestRunner

