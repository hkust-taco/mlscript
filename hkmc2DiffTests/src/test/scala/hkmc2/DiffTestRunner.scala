package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}
import os.up

import mlscript.utils._, shorthands._


// * Note: we used to use:
// *    class AllTests extends org.scalatest.Suites(
// *      new CompileTestRunner(DiffTestRunner.State){},
// *      new DiffTestRunner(DiffTestRunner.State){},
// *    )
// * but this (very surprisinbgly) disables parallel execution each individual suite.
// * So now we just split tests into separate SBT projects.


object DiffTestRunner:
  
  class State:
    
    val pwd = os.pwd
    
    // println(s"INITIALIZING DiffTestRunner.State in ${pwd}")
    
    val workingDir = if pwd.last == "hkmc2DiffTests"
      then pwd/up // For some reason, when run from ~hkmc2JVM/Test/run in sbt, the pwd is ".../hkmc2/jvm"
      else pwd
    // val dir = workingDir/"hkmc2"/"shared"/"src"/"test"/"mlscript"
    
    val dir = workingDir/"hkmc2"/"shared"/"src"/"test"
    
    val validExt = Set("mls")
    
    val allFiles = os.walk(dir)
      .filter(_.toIO.isFile)
      .filter(_.ext in validExt)
    
    def filter(file: os.RelPath): Bool = true
    
    val TimeLimit =
      if sys.env.get("CI").isDefined then Span(60, Seconds)
      else Span(30, Seconds)
    
  end State
  
  class StateWithGit extends State:
    
    println(s"Running git in ${dir}...")
    
    // * Aggregate unstaged modified files to only run the tests on them, if there are any
    val modified: Set[os.RelPath] =
      try os.proc("git", "status", "--porcelain", dir).call().out.lines().iterator.flatMap { gitStr =>
        println(" [git] " + gitStr)
        val prefix = gitStr.take(2)
        val filePath = os.RelPath(gitStr.drop(3))
        if prefix =:= "A " || prefix =:= "M " || prefix =:= "R " || prefix =:= "D " then
          N // * Disregard modified files that are staged
        else if filePath.ext =/= "mls" then N
        else S(filePath)
      }.toSet catch
        case err: Throwable =>
          System.err.println("/!\\ git command failed with: " + err)
          Set.empty
    
    if modified.isEmpty then
      println("No test file with unstaged changes detected; no test will run.")
    
    override def filter(file: os.RelPath): Bool =
      // println(s"Filtering: $file ${modified(file)}")
      modified(file)
    
  end StateWithGit
  
  lazy val State = new State
  
end DiffTestRunner


class DiffTestRunner
  extends DiffTestRunnerBase(DiffTestRunner.State)
  with ParallelTestExecution

class DiffTestRunnerBase(state: DiffTestRunner.State)
  extends funsuite.AnyFunSuite
  with TimeLimitedTests
:
  import state.*
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  val timeLimit = TimeLimit
  
  override val defaultTestSignaler: Signaler = new Signaler:
    @annotation.nowarn("msg=method stop in class Thread is deprecated") def apply(testThread: Thread): Unit =
      println(s"!! Test at $testThread has run out out time !! stopping..." +
        "\n\tNote: you can increase this limit by changing DiffTests.TimeLimit")
      // * Thread.stop() is considered bad practice because normally it's better to implement proper logic
      // * to terminate threads gracefully, avoiding leaving applications in a bad state.
      // * But here we DGAF since all the test is doing is running a type checker and some Node REPL,
      // * which would be a much bigger pain to make receptive to "gentle" interruption.
      // * It would feel extremely wrong to intersperse the pure type checker algorithms
      // * with ugly `Thread.isInterrupted` checks everywhere...
      testThread.stop()
  
  protected lazy val diffTestFiles = allFiles.filter: file =>
    (
      !file.segments.contains("staging") // Exclude staging test files
      && !file.segments.contains("mlscript-compile")
      && filter(file.relativeTo(state.workingDir))
    )
  
  diffTestFiles.foreach: file =>
    
    val basePath = file.segments.drop(dir.segmentCount).toList.init
    val relativeName = basePath.map(_ + "/").mkString + file.baseName
    
    test(relativeName):
      
      val preludePath = dir/"mlscript"/"decls"/"Prelude.mls"
      val predefPath = dir/"mlscript-compile"/"Predef.mls"
      
      val dm = new MainDiffMaker(workingDir.toString, file, preludePath, predefPath, relativeName)
      
      dm.run()
      
      if dm.failures.nonEmpty then
        fail(s"Unexpected test outcome(s) at: " +
          dm.failures.distinct.map("\n\t"+relativeName+"."+file.ext+":"+_).mkString(", "))
  
end DiffTestRunnerBase


