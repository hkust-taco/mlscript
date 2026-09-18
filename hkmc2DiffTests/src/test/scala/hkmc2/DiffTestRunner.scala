package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}
import os.up

import hkmc2.utils.*, shorthands.*
import io.PlatformPath.given, io.FileSystem


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
    
    val workingDir = DiffMaker.projectRoot(pwd)
    // val dir = workingDir/"hkmc2"/"shared"/"src"/"test"/"mlscript"
    
    val dir = workingDir/"hkmc2"/"shared"/"src"/"test"
    
    // * All diff tests in a run share this context, and therefore the compilation units they
    // * import. Pinning the root configuration keeps those units independent of whichever
    // * worksheet happens to reach them first, and makes them come out the same as when the
    // * compile tests build the corresponding `.mjs` modules — which use this same base
    // * directory, so that source locations baked into generated code agree.
    val cctx: CompilerCtx =
      CompilerCtx.fresh(io.FileSystem.default, TestFolders.compilerPaths(workingDir), Config.default(dir))
    
    // To be overridden in subproject-specific State classes
    def testDir: os.Path = dir
    
    val validExt = Set("mls")
    
    val allFiles = os.walk(testDir)
      .filter(_.toIO.isFile)
      .filter(_.ext in validExt)
    
    def filter(file: os.RelPath): Bool = true
    
    val TimeLimit =
      if sys.env.get("CI").isDefined then Span(60, Seconds)
      else Span(25, Seconds)
    
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
  with ParallelTestExecution:
  
  override protected def excludedDiffDirs: Ls[os.Path] =
    TestFolders.mainExcludedDiffDirs(state.workingDir)

class DiffTestRunnerBase(val state: DiffTestRunner.State) extends TimeOutTests:
  import state.*
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  val timeLimit = TimeLimit
  
  protected def excludedDiffDirs: Ls[os.Path] =
    TestFolders.alwaysExcludedDiffDirs(state.workingDir)
  
  protected lazy val diffTestFiles = allFiles.filter: file =>
    (
      !TestFolders.isExcluded(file, excludedDiffDirs)
      && filter(file.relativeTo(state.workingDir))
    )
  
  protected def createDiffMaker(
    file: os.Path,
    preludePath: os.Path,
    predefPath: os.Path,
    relativeName: String
  ): DiffMaker =
    new MainDiffMaker(workingDir.toString, file, preludePath, predefPath, relativeName):
      def cctx = state.cctx
  
  diffTestFiles.foreach: file =>
    
    val basePath = file.segments.drop(dir.segmentCount).toList.init
    val relativeName = basePath.map(_ + "/").mkString + file.baseName
    
    test(relativeName):
      
      val preludePath = dir/"mlscript"/"decls"/"Prelude.mls"
      val predefPath = dir/"mlscript-compile"/"Predef.mls"
      
      val dm = createDiffMaker(file, preludePath, predefPath, relativeName)
      
      dm.run()
      
      if dm.failures.nonEmpty then
        fail(s"Unexpected test outcome(s) at: " +
          dm.failures.distinct.map("\n\t"+relativeName+"."+file.ext+":"+_).mkString(", "))
  
end DiffTestRunnerBase
