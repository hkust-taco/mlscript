package hkmc2

import scala.collection.mutable

import org.scalatest.{funsuite, Args, ParallelTestExecution, Status}
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
    
    val preludePath = dir/"mlscript"/"decls"/"Prelude.mls"
    val predefPath = dir/"mlscript-compile"/"Predef.mls"
    
    private val importPattern = """(?m)^\s*import\s+"([^"]+\.mls)"""".r
    
    /** The library modules that the diff test `file` elaborates through `cctx`, besides the Prelude:
      * the `Predef` that every test imports, and the `mlscript-compile` modules that `file` imports.
      * Other imported files can be fixtures whose diagnostics the importing test is expected to show.
      */
    def importedModules(file: os.Path): Ls[os.Path] =
      predefPath :: importPattern.findAllMatchIn(os.read(file)).toList
        .map(m => os.Path(m.group(1), file / os.up))
        .filter(module => module.segments.contains("mlscript-compile") && os.isFile(module))
    
    /** Whether runs on this state elaborate the modules their tests import before starting them. */
    def warmsUpImports: Bool = true
    
    // * The artifact obtained for each warmed-up path, with the diagnostics raised while obtaining it.
    // * `warmUpImports` writes it before a run starts its tests, which read it on other runner instances
    // * (see `ParallelTestExecution`). Comparing artifacts tells a file elaborated anew, whose diagnostics
    // * replace the recorded ones, from a cached artifact, which raises none when it is obtained again.
    private val warmUps = scala.collection.concurrent.TrieMap.empty[os.Path, (Opt[AnyRef], Ls[Str])]
    
    /** Elaborates the Prelude and the modules imported by the diff tests `files` in `cctx`, before
      * these tests start.
      *
      * `cctx` elaborates each imported module once, under a lock dedicated to its path. Otherwise, the
      * first test to import a module pays for elaborating it, and the other tests importing it meanwhile
      * block on that lock, all within their own time limits. A small test such as `basics/Puns.mls` then
      * timed out on slow CI runners while `LazyArray.mls` was being elaborated, and stopping its thread
      * discarded that elaboration, so that the next test importing it timed out too.
      *
      * The compile tests check that library modules elaborate without diagnostics. Any raised here are
      * recorded, and the tests importing the module report them (see `warmUpDiagnostics`).
      */
    def warmUpImports(files: Iterable[os.Path]): Unit =
      import java.util.concurrent.{Callable, Executors}
      import scala.jdk.CollectionConverters.*
      val start = System.currentTimeMillis()
      val modules = files.iterator.flatMap(importedModules).toList.distinct.sortBy(_.toString)
      def warmUp[A <: AnyRef](path: os.Path)(obtain: (TL, Raise) ?=> A): Opt[A] =
        val diagnostics = mutable.Buffer.empty[Str]
        given DebugPrinter = new DebugPrinter(N)
        given TL = TraceLogger.silent
        given Raise = d =>
          diagnostics += d.toString
          ()
        val artifact =
          try S(obtain) catch case err: Throwable =>
            diagnostics += s"Uncaught $err"
            N
        if !artifact.exists(a => warmUps.get(path).exists(_._1.exists(_ eq a))) then
          warmUps(path) = (artifact, diagnostics.toList)
        artifact
      warmUp(preludePath)(cctx.getPrelude(preludePath)).foreach: prelude =>
        // * Modules sharing a dependency wait on its path lock, as tests importing them would.
        val tasks = modules.map[Callable[Unit]]: module =>
          () => warmUp(module)(cctx.getElaboratedBlock(module, prelude.ctx)).fold(())(_ => ())
        val pool = Executors.newFixedThreadPool(Runtime.getRuntime.availableProcessors)
        try pool.invokeAll(tasks.asJava) finally pool.shutdown()
      println(s"Warmed up the Prelude and ${modules.size} imported module(s) in ${
        System.currentTimeMillis() - start} ms")
    
    /** The diagnostics recorded by `warmUpImports` for the Prelude and the modules that `file` imports. */
    def warmUpDiagnostics(file: os.Path): Ls[Str] =
      (preludePath :: importedModules(file)).flatMap: path =>
        warmUps.get(path).toList.flatMap(_._2).map(d => s"${path.relativeTo(dir)}: $d")
    
    // To be overridden in subproject-specific State classes
    def testDir: os.Path = dir
    
    val allFiles = os.walk(testDir)
      .filter(_.toIO.isFile)
      .filter(TestFolders.isTestSource)
    
    def filter(file: os.RelPath): Bool = true
    
    // Benchmark states override this limit.
    val TimeLimit = TimeOutTests.TimeLimit
    
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
        else if !TestFolders.isTestSource(filePath) then N
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
    
    // * This state serves the `:tests` command of watcher sessions, which run a few changed tests
    // * and report them as soon as possible; like the watcher itself, they elaborate imports on demand.
    override def warmsUpImports: Bool = false
    
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
  
  private def relativeName(file: os.Path): Str =
    val basePath = file.segments.drop(dir.segmentCount).toList.init
    basePath.map(_ + "/").mkString + file.baseName
  
  private lazy val diffTestFilesByName: Map[Str, os.Path] =
    diffTestFiles.map(file => relativeName(file) -> file).toMap
  
  /** Elaborates the modules imported by the tests this run selects, such as with `-z`, before starting
    * them (see `DiffTestRunner.State.warmUpImports`), so that no test's time limit covers them.
    * ScalaTest then runs each test on a fresh runner instance with its name (see `ParallelTestExecution`).
    */
  override def run(testName: Opt[Str], args: Args): Status =
    if testName.isEmpty && warmsUpImports then
      warmUpImports(args.filter(testNames, tags, suiteId).collect:
        case (name, false) => diffTestFilesByName(name))
    super.run(testName, args)
  
  diffTestFiles.foreach: file =>
    
    val relativeName = this.relativeName(file)
    
    test(relativeName):
      
      val dm = createDiffMaker(file, preludePath, predefPath, relativeName)
      
      dm.run()
      
      // * The warm-up elaborated the modules that this test shares with others, so report their diagnostics.
      val importDiagnostics = warmUpDiagnostics(file)
      if importDiagnostics.nonEmpty then
        fail(s"Diagnostics while elaborating imported modules:" + importDiagnostics.map("\n\t" + _).mkString)
      
      if dm.failures.nonEmpty then
        fail(s"Unexpected test outcome(s) at: " +
          dm.failures.distinct.map("\n\t"+relativeName+"."+file.ext+":"+_).mkString(", "))
  
end DiffTestRunnerBase
