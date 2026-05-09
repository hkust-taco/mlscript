package hkmc2

import org.scalatest.{funspec, ParallelTestExecution}

import mlscript.utils.*, shorthands.*
import io.PlatformPath.given

import hkmc2.io.FileSystem

/**
  * A simple test runner that compiles packages written in MLscript.
  */
class PackageTestRunner
  extends funspec.AnyFunSpec
  // with ParallelTestExecution // Can `MLsCompiler` handle parallel compilation?
  // with TimeLimitedTests // TODO
:
  import PackageTestRunner.*
  import PackageTestRunner.given
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  // val timeLimit = TimeLimit
  
  for packageDir <- os.list(packagesDir).filter(os.isDir) do
    val allFiles = os.walk(packageDir).filter(os.isFile).filter(_.ext == "mls").toSeq
    val packageName = packageDir.baseName
    
    // The compiler context is created per package to avoid interference.
    given cctx: CompilerCtx = CompilerCtx.fresh(fs, PackageModuleResolver(packageDir))
    // We might need to read `Config` from a config file later.
    given Config = Config.default(mainTestDir)
    
    val wrap: (=> Unit) => Unit = body => PackageTestRunner.synchronized(body)
    val report = ReportFormatter(System.out.println, colorize = true, wrap = Some(wrap))
    val compiler = MLsCompiler(paths, mkRaise = report.mkRaise)
    
    describe(s"$packageName (${"file" countBy allFiles.size})"):
    
      allFiles.foreach: file =>
        val relativeName = file.relativeTo(packageDir).toString()
        
        it(relativeName):
          
          PackageTestRunner.synchronized:
            println(s"Compiling: [${fansi.Bold.On(packageName)}] ${fansi.Color.Green(relativeName)}")
          
          assert(true, s"Placeholder test for package: $relativeName")

          compiler.compileModule(file)
          
          if report.badLines.nonEmpty then
            fail(s"Unexpected diagnostic at: " +
              report.badLines.distinct.sorted
                .map("\n\t"+relativeName+"."+file.ext+":"+_).mkString(", "))
end PackageTestRunner

object PackageTestRunner:
  
  val mainTestDir = TestFolders.mainTestDir(os.pwd)
  val packagesDir = TestFolders.packagesTestDir(os.pwd)
  val stdlibDir = mainTestDir / "mlscript-compile"
  
  val paths = new MLsCompiler.Paths:
    val preludeFile = mainTestDir / "mlscript" / "decls" / "Prelude.mls"
    val runtimeFile = stdlibDir / "Runtime.mjs"
    val termFile = stdlibDir / "Term.mjs"
  
  val nodeModulesPath = os.pwd / "node_modules"
  
  given fs: FileSystem = io.FileSystem.default
  
  // TODO: Read from `manifest.json`.
  val vendors = LocalModuleResolver.Vendor("std/", stdlibDir, Ls("*.mls")) :: Nil
  
  // We may use a different module resolver for URL modules in browsers. For
  // example, `import "https://esm.sh/nanoid"` should be accepted.
  class PackageModuleResolver(packageDir: os.Path) extends LocalModuleResolver(vendors, N):
    private val packageVendorDir = packageDir / "vendor"
    
    private def getVendoredPath(moduleName: Str): io.Path =
      val dir = packageVendorDir / moduleName
      if os.exists(dir) then
        if os.isDir(dir) then dir
        else
          throw new Exception(s"The vendored module path is not a directory: $dir")
      else
        os.makeDir.all(dir)
        dir
  
end PackageTestRunner
