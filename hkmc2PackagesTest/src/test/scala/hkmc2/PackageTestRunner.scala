package hkmc2

import org.scalatest.{funspec, ParallelTestExecution}

import hkmc2.utils.*, shorthands.*
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
    val moduleResolver = PackageModuleResolver(packageDir, manifest, S(nodeModulesPath), stdlibDir)
    val vendoredSources = moduleResolver.vendoredSources.toSeq
    val copiedVendorFiles = moduleResolver.copiedVendorFiles.toSeq
    
    // The compiler context is created per package to avoid interference.
    given cctx: CompilerCtx = CompilerCtx.fresh(fs, moduleResolver)
    given Config = configForPackage(packageName)
    
    val wrap: (=> Unit) => Unit = body => PackageTestRunner.synchronized(body)
    val report = ReportFormatter(System.out.println, colorize = true, wrap = Some(wrap))
    val compiler = MLsCompiler(pathsForPackage(packageDir), mkRaise = report.mkRaise)
    
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
              println(s"Vendoring: [${fansi.Bold.On(packageName)}] ${fansi.Color.Green(displayPath(file.source))}")
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
  
  def displayPath(path: os.Path): Str =
    if path.startsWith(mainTestDir) then path.relativeTo(mainTestDir).toString
    else if path.startsWith(os.pwd) then path.relativeTo(os.pwd).toString
    else path.toString
  
  def pathsForPackage(packageDir: os.Path): MLsCompiler.Paths = new MLsCompiler.Paths:
    val preludeFile = mainTestDir / "mlscript" / "decls" / "Prelude.mls"
    val runtimeFile = PackageModuleResolver.runtimeTarget(packageDir)
    val runtimeSourceFile = stdlibDir / "Runtime.mls"
    val termFile = PackageModuleResolver.termTarget(packageDir)

  def configForPackage(packageName: Str): Config =
    val defaultConfig = Config.default(mainTestDir)
    // Definition lifting currently changes callback interop in generated JS for web IDE code.
    // Keep this package on the pre-lifting codegen path until that compiler bug is fixed.
    if packageName == "web-ide" then defaultConfig.copy(liftDefns = N)
    else defaultConfig
  
  val nodeModulesPath = os.pwd / "node_modules"
  
  given fs: FileSystem = io.FileSystem.default
  
end PackageTestRunner
