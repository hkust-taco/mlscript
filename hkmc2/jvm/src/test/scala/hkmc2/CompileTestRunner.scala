package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}
import os.up

import mlscript.utils._, shorthands._


class CompileTestRunner
  extends funsuite.AnyFunSuite
  with ParallelTestExecution
  // with TimeLimitedTests // TODO
:
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  // val timeLimit = TimeLimit
  
  val pwd = os.pwd
  val workingDir = pwd
  
  val dir = workingDir/"hkmc2"/"shared"/"src"/"test"
  
  val validExt = Set("mls")
  
  val allFiles = os.walk(dir)
    .filter(_.toIO.isFile)
    .filter(_.ext in validExt)
    
  protected lazy val compileTestFiles = allFiles.filter: file =>
      file.segments.contains("mlscript-compile")
  
  // TODO dedup path stuff with DiffTestRunner?
  compileTestFiles.foreach: file =>
    
    val basePath = file.segments.drop(dir.segmentCount).toList.init
    val relativeName = basePath.map(_ + "/").mkString + file.baseName
    
    test(relativeName):
      
      println(s"Compiling: $relativeName")
      
      val preludePath = dir/"mlscript"/"decls"/"Prelude.mls"
      
      val compiler = MLsCompiler(preludePath)
      compiler.compileModule(file)
      
      if compiler.report.badLines.nonEmpty then
        fail(s"Unexpected diagnostic at: " +
          compiler.report.badLines.distinct.sorted
            .map("\n\t"+relativeName+"."+file.ext+":"+_).mkString(", "))
      
end CompileTestRunner


