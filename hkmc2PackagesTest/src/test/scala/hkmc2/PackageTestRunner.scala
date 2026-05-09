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
  // with ParallelTestExecution // Support parallel compilation in the future.
  // with TimeLimitedTests // Support time limits when necessary.
:
  import PackageTestRunner.*
  import PackageTestRunner.given
  
  private val inParallel = isInstanceOf[ParallelTestExecution]
  
  for packageDir <- os.list(packagesDir).filter(os.isDir) do
    val allFiles = os.walk(packageDir)
      .filter(os.isFile)
      .filter(_.ext == "mls")
      .filter(file => !file.startsWith(packageDir / "vendors"))
      .toSeq
    val packageName = packageDir.baseName
    val manifest = PackageManifest.read(packageDir)
    val moduleResolver = PackageModuleResolver(packageDir, manifest, S(nodeModulesPath))
    val vendoredSources = moduleResolver.vendoredSources.toSeq
    val copiedVendorFiles = moduleResolver.copiedVendorFiles.toSeq
    
    // The compiler context is created per package to avoid interference.
    given cctx: CompilerCtx = CompilerCtx.fresh(fs, moduleResolver)
    // We might need to read `Config` from a config file later.
    given Config = Config.default(mainTestDir)
    
    val wrap: (=> Unit) => Unit = body => PackageTestRunner.synchronized(body)
    val report = ReportFormatter(System.out.println, colorize = true, wrap = Some(wrap))
    val compiler = MLsCompiler(paths, mkRaise = report.mkRaise)
    
    describe(s"$packageName (${"file" countBy allFiles.size})"):
    
      if vendoredSources.nonEmpty || copiedVendorFiles.nonEmpty then
        it("vendors"):
          os.remove.all(packageDir / "vendors")
          copiedVendorFiles.foreach: file =>
            os.makeDir.all(file.target / os.up)
            os.copy.over(file.source, file.target)
            
          vendoredSources.foreach: file =>
            os.makeDir.all(file.target / os.up)
            PackageTestRunner.synchronized:
              println(s"Vendoring: [${fansi.Bold.On(packageName)}] ${fansi.Color.Green(file.source.toString)}")
            compiler.compileModule(file.source, S(file.target))
            assert(os.exists(file.target), s"Expected vendored artifact at ${file.target}")
          
          copiedVendorFiles.foreach: file =>
            assert(os.exists(file.target), s"Expected copied vendor artifact at ${file.target}")
          
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
  
end PackageTestRunner
