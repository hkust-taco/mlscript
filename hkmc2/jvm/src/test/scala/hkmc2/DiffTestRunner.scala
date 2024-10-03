package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}
import os.up

import mlscript.utils._, shorthands._



class MainDiffMaker(val file: os.Path, val predefFile: os.Path, val relativeName: Str)
  extends BbmlDiffMaker


object DiffTestRunner:
  
  class State:
    
    val TimeLimit =
      if sys.env.get("CI").isDefined then Span(60, Seconds)
      else Span(30, Seconds)
    
    val pwd = os.pwd
    val workingDir = if pwd.last == "jvm"
      then pwd/up/up // For some reason, when run from ~hkmc2JVM/Test/run in sbt, the pwd is ".../hkmc2/jvm"
      else pwd
    val dir = workingDir/"hkmc2"/"shared"/"src"/"test"/"mlscript"
    
    val validExt = Set("mls")
    
    val allFiles = os.walk(dir)
      .filter(_.toIO.isFile)
      .filter(_.ext in validExt)
    
    // Aggregate unstaged modified files to only run the tests on them, if there are any
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
        case err: Throwable => System.err.println("/!\\ git command failed with: " + err)
        Set.empty
    
  end State
  
  lazy val State = new State

end DiffTestRunner


class DiffTestRunner(state: DiffTestRunner.State)
  extends funsuite.AnyFunSuite
  with ParallelTestExecution
  with TimeLimitedTests
:
  import state.*
  
  // def newInstance = ???
  def this() = this(DiffTestRunner.State)
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  // scala test will not execute a test if the test class has constructor parameters.
  // override this to get the correct paths of test files.
  protected lazy val files = allFiles.filter: file =>
    (modified(file.relativeTo(workingDir)) || modified.isEmpty) &&
      !file.segments.contains("staging") // Exclude staging test files
  
  /* 
  println(pwd)
  println(workingDir)
  println(modified)
  println(allFiles.map(_.relativeTo(workingDir)))
  */
  
  val timeLimit = TimeLimit
  
  override val defaultTestSignaler: Signaler = new Signaler:
    @annotation.nowarn("msg=method stop in class Thread is deprecated") def apply(testThread: Thread): Unit =
      println(s"!! Test at $testThread has run out out time !! stopping..." +
        "\n\tNote: you can increase this limit by changing DiffTests.TimeLimit")
      // * Thread.stop() is considered bad practice because normally it's better to implement proper logic
      // * to terminate threads gracefully, avoiding leaving applications in a bad state.
      // * But here we DGAF since all the test is doing is runnign a type checker and some Node REPL,
      // * which would be a much bigger pain to make receptive to "gentle" interruption.
      // * It would feel extremely wrong to intersperse the pure type checker algorithms
      // * with ugly `Thread.isInterrupted` checks everywhere...
      testThread.stop()
  
  files.foreach: file =>
    val basePath = file.segments.drop(dir.segmentCount).toList.init
    val relativeName = basePath.map(_ + "/").mkString + file.baseName
    test(relativeName):
      
      val predefPath = dir/"decls"/"Predef.mls"
      
      val dm = new MainDiffMaker(file, predefPath, relativeName)
      
      dm.run()
      
      if dm.failures.nonEmpty then
        fail(s"Unexpected test outcome(s) at: " +
          dm.failures.distinct.map("\n\t"+relativeName+"."+file.ext+":"+_).mkString(", "))
  
end DiffTestRunner


