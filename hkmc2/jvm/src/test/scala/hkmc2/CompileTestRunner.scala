package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}
import os.up

import mlscript.utils._, shorthands._
import io.PlatformPath.given

import CompileTestRunner.given


class CompileTestRunner
  extends funsuite.AnyFunSuite
  with ParallelTestExecution
  // with TimeLimitedTests // TODO
:
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  // val timeLimit = TimeLimit
  
  val pwd = os.pwd
  val workingDir = pwd

  val mainTestDir = workingDir/"hkmc2"/"shared"/"src"/"test"  
  
  // The compilation tests currently include compiling the benchmark instrumentation code.
  val dirs = mainTestDir :: workingDir/"hkmc2Benchmarks"/"src"/"test" :: Nil
  
  val validExt = Set("mls")
    
  for dir <- dirs do {
    val allFiles = os.walk(dir)
      .filter(_.toIO.isFile)
      .filter(_.ext in validExt)
      
    lazy val compileTestFiles = allFiles.filter: file =>
        file.segments.contains("mlscript-compile")
    
    // TODO dedup path stuff with DiffTestRunner?
    compileTestFiles.foreach: file =>
      
      val basePath = file.segments.drop(dir.segmentCount).toList.init
      val relativeName = basePath.map(_ + "/").mkString + file.baseName
      
      test(relativeName):
        
        CompileTestRunner.synchronized:
          println(s"Compiling: $relativeName")
        
        // * Stack safety relies on the fact that runtime uses while loops for resumption
        // * and does not create extra stack depth. Hence, while loop rewriting should be disabled here.
        // * (It used to be on by default, but now is off by default, so nothing to do.)
        given Config = Config.default(mainTestDir)
        
        // Synchronize diagnostic output to avoid interleaving since the compiler tests run in parallel.
        val wrap: (=> Unit) => Unit = body => CompileTestRunner.synchronized(body)
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
      
end CompileTestRunner


object CompileTestRunner:
  
  given cctx: CompilerCtx = CompilerCtx.fresh(io.FileSystem.default)
  
end CompileTestRunner


