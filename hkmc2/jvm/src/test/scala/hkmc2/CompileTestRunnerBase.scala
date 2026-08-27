package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler}

import hkmc2.utils.*, shorthands.*
import io.PlatformPath.given


// Reusable base class for compile test runners. Subclasses provide the
// directories to scan and the compiler context to use, and this base class
// handles walking directories, filtering for mlscript-compile files,
// and registering ScalaTest tests.
abstract class CompileTestRunnerBase(
  compileDirs: Ls[os.Path],
  excludedDirs: Ls[os.Path] = Nil,
) extends TimeOutTests, ParallelTestExecution:
  
  
  val timeLimit = Span(25, Seconds)
  
  
  given CompilerCtx = cctx
  
  protected def cctx: CompilerCtx
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  val workingDir: os.Path = os.pwd
  
  val mainTestDir: os.Path = TestFolders.mainTestDir(workingDir)
  
  val validExt = Set("mls")
  
  for dir <- compileDirs do {
    val allFiles = os.walk(dir)
      .filter(_.toIO.isFile)
      .filter(_.ext in validExt)
    
    lazy val compileTestFiles = allFiles.filter: file =>
      file.segments.contains("mlscript-compile")
        && !TestFolders.isExcluded(file, excludedDirs)
    
    compileTestFiles.foreach: file =>
      
      val basePath = file.segments.drop(dir.segmentCount).toList.init
      val relativeName = basePath.map(_ + "/").mkString + file.baseName
      
      test(relativeName):
        
        this.synchronized:
          println(s"Compiling: $relativeName")
        
        // Synchronize diagnostic output to avoid interleaving since the compiler tests run in parallel.
        val wrap: (=> Unit) => Unit = body => this.synchronized(body)
        val report = ReportFormatter(System.out.println, colorize = true, wrap = Some(wrap))
        val compiler = MLsCompiler(mkRaise = report.mkRaise)
        compiler.compileModule(file)
        
        if report.badLines.nonEmpty then
          fail(s"Unexpected diagnostic at: " +
            report.badLines.distinct.sorted
              .map("\n\t"+relativeName+"."+file.ext+":"+_).mkString(", "))
  }

end CompileTestRunnerBase
