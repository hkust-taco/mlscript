package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}
import os.up

import mlscript.utils._, shorthands._
import io.PlatformPath.given


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
        
        println(s"Compiling: $relativeName")
        
        // Stack safety relies on the fact that runtime uses while loops for resumption
        // and does not create extra stack depth. Hence we disable while loop rewriting here.
        given Config = Config.default.copy(rewriteWhileLoops = false)
        given io.FileSystem = io.FileSystem.default
        
        val output: Str => Unit = System.out.println
        // Synchronize diagnostic output to avoid interleaving since the compiler tests run in parallel.
        val wrap: (=> Unit) => Unit = body => CompileTestRunner.synchronized(body)
        val report = ReportFormatter(output, Some(wrap))
        def mkRaise(file: io.Path): Raise =
          val wd = file.up
          d => wrap:
            val relPath = file.relativeTo(wd.up).map(_.toString).getOrElse(file.toString)
            output(fansi.Color.LightRed(s"/!!!\\ Error in $relPath /!!!\\").toString)
          report(0, d :: Nil, showRelativeLineNums = false)
        
        val compiler = MLsCompiler(
          new MLsCompiler.Paths:
            val preludeFile = mainTestDir / "mlscript" / "decls" / "Prelude.mls"
            val runtimeFile = mainTestDir / "mlscript-compile" / "Runtime.mjs"
            val termFile = mainTestDir / "mlscript-compile" / "Term.mjs",
          mkRaise
        )
        compiler.compileModule(file)
        
        if report.badLines.nonEmpty then
          fail(s"Unexpected diagnostic at: " +
            report.badLines.distinct.sorted
              .map("\n\t"+relativeName+"."+file.ext+":"+_).mkString(", "))
  }
      
end CompileTestRunner

object CompileTestRunner


