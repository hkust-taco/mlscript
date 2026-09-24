package hkmc2

import org.scalatest.funsuite.AnyFunSuite
import io.{InMemoryFileSystem, Path, node}
import hkmc2.utils.*, shorthands.*
import scala.scalajs.js
import scala.scalajs.js.annotation._
import scala.scalajs.js.Dynamic.global

class CompilerTest extends AnyFunSuite:
  private class CountingFileSystem(initialFiles: Map[String, String])
      extends InMemoryFileSystem(initialFiles):
    private val readCounts = scala.collection.mutable.Map.empty[Path, Int]

    override def read(path: Path): String =
      readCounts.updateWith(path)(_.map(_ + 1).orElse(Some(1)))
      super.read(path)

    def readCount(path: Path): Int = readCounts.getOrElse(path, 0)

  private def loadStandardLibrary(): Map[String, String] =
    val projectRoot = node.process.cwd()
    val compilePath = node.path.join(projectRoot, "hkmc2", "shared", "src", "test", "mlscript-compile")
    val preludePath = node.path.join(projectRoot, "hkmc2", "shared", "src", "test", "mlscript", "decls", "Prelude.mls")
    
    node.fs.readdirSync(compilePath).filter(_.endsWith(".mls")).toSeq.flatMap: fileName =>
      val filePath = node.path.join(compilePath, fileName)
      if node.fs.existsSync(filePath) then
        Some(s"/std/$fileName" -> node.fs.readFileSync(filePath, "utf-8"))
      else
        None
    .toMap + ("/std/Prelude.mls" -> node.fs.readFileSync(preludePath, "utf-8"))
  
  private val paths = new Paths("/std/Prelude.mls", "/std/Runtime.mjs", "/std/Runtime.mls", "/std/Term.mjs")
  
  private def createCompiler(): (InMemoryFileSystem, Compiler) =
    val stdLib = loadStandardLibrary()
    val fs = new InMemoryFileSystem(stdLib)
    given CompilerCtx = CompilerCtx.fresh(fs, paths, Config.default(io.Path("/")))
    (fs, new Compiler)

  test("compiler parses each compilation unit only once"):
    val fs = new CountingFileSystem(loadStandardLibrary())
    given CompilerCtx = CompilerCtx.fresh(fs, paths, Config.default(io.Path("/")))
    val compiler = new Compiler
    val inputPath = Path("/singleParse.mls")
    fs.write(inputPath, "fun answer() = 42")

    compiler.compile(inputPath.toString)
    compiler.compile(inputPath.toString)

    assert(fs.readCount(inputPath) == 1,
      "The first compilation should parse the source once and the second should reuse its artifact")
  
  test("compiler can compile a simple program"):
    val (fs, compiler) = createCompiler()
    
    // Write test program to the file system
    val code = """|import "./std/Option.mls"
                  |import "./std/Stack.mls"
                  |import "./std/Predef.mls"
                  |
                  |open Stack
                  |open Option
                  |open Predef
                  |
                  |fun findFirst(xs, f) = if xs is
                  |  Nil then None
                  |  Cons(x, xs') and
                  |    f(x) then Some(x)
                  |    else findFirst(xs', f)
                  |
                  |let nums = 1 :: 2 :: 3 :: 4 :: 5 :: Nil
                  |let result = nums \findFirst of x => x * 6 is 24
                  |""".stripMargin
    val inputPath = "/findFirstTest.mls"
    val outputPath = "/findFirstTest.mjs"
    
    fs.write(inputPath, code)
    
    val diagnostics = compiler.compile(inputPath)
    
    val hasErrors = diagnostics.exists: perFile =>
      val fileDiagnostics = perFile.diagnostics.asInstanceOf[scala.scalajs.js.Array[scala.scalajs.js.Dynamic]]
      fileDiagnostics.exists(_.kind is "error")
    assert(!hasErrors, "Compilation should succeed without errors")
    
    val outputExists = fs.exists(Path(outputPath))
    assert(outputExists, "Output JavaScript file should be generated")
    
    val output = fs.read(outputPath)
    assert(output.contains("findFirst"), "Output should contain the findFirst function")
  
  test("compiler can compile two files that import each other"):
    val (fs, compiler) = createCompiler()
    
    val foo = """|import "./std/Predef.mls"
                 |
                 |open Predef
                 |
                 |module Foo with...
                 |
                 |fun sayHello() = print of "Hello, world!"
                 |""".stripMargin
    fs.write("/Foo.mls", foo)
    
    val bar = """|import "./Foo.mls"
                 |
                 |Foo.sayHello()
                 |""".stripMargin
    fs.write("/Bar.mls", bar)
    
    val diag1 = compiler.compile("/Foo.mls")
    val diag2 = compiler.compile("/Bar.mls")
    
    assert(fs.exists(Path("/Foo.mjs")), "First output should exist")
    assert(fs.exists(Path("/Bar.mjs")), "Second output should exist")

  test("private ABI allocation avoids existing top-level names"):
    given state: semantics.Elaborator.State = new semantics.Elaborator.State
    given Raise = diagnostic => fail(diagnostic.toString)
    val existing = semantics.BlockMemberSymbol("_$_modulePrivate_$_helper", Nil)
    val helper = semantics.BlockMemberSymbol("helper", Nil)
    val program = codegen.Program(Nil, codegen.Scoped(Set(existing, helper), codegen.End()))

    val names = CompilerCtx.allocateModulePrivateExportNames(program)

    assert(names(helper) == "_$_modulePrivate_$_helper1",
      "The private name should receive the normal scope collision suffix")

  test("private ABI names survive UID shifts and invalidate cached importers"):
    val (fs, compiler) = createCompiler()

    def source(prefix: String, suffix: String): String =
      s"""|$prefix
          |fun helper() = "This body is deliberately too large for automatic inlining."
          |module A with
          |  fun exposed() = helper() + "$suffix"
          |""".stripMargin

    fs.write("/A.mls", source("", "before"))
    fs.write("/B.mls", """import "./A.mls"
                           |A.exposed()
                           |""".stripMargin)
    compiler.compile("/A.mls")
    compiler.compile("/B.mls")

    val privateExport = """export \{ helper as (\S*modulePrivate\S*) \};""".r
    val privateImport = """import \{ (\S*modulePrivate\S*) as helper \}""".r
    val initialExport = privateExport.findFirstMatchIn(fs.read("/A.mjs")).map(_.group(1))

    // The extra definition shifts `helper`'s UID, but its scope-allocated ABI name stays stable.
    // Changing the inlined suffix also verifies that requesting cached `B` notices the stale `A`.
    fs.write("/A.mls", source("fun shiftsFollowingSymbolIds() = 0", "after"))
    compiler.compile("/B.mls")
    compiler.compile("/A.mls")

    val aExport = privateExport.findFirstMatchIn(fs.read("/A.mjs")).map(_.group(1))
    val bJs = fs.read("/B.mjs")
    val bImport = privateImport.findFirstMatchIn(bJs).map(_.group(1))
    assert(initialExport.nonEmpty, "The defining module should export the referenced private helper")
    assert(aExport == initialExport, "Shifting symbol UIDs should not change private ABI names")
    assert(bImport == aExport, "The importer and exporter should use the same private ABI name")
    assert(bJs.contains("after"), "The cached importer should be rebuilt after its dependency changes")

  test("cached artifacts validate only their transitive dependencies"):
    val fs = new CountingFileSystem(loadStandardLibrary())
    given CompilerCtx = CompilerCtx.fresh(fs, paths, Config.default(io.Path("/")))
    val compiler = new Compiler

    fs.write("/A.mls", """fun helper() = "before"
                           |module A with
                           |  fun value() = helper()
                           |""".stripMargin)
    fs.write("/B.mls", """import "./A.mls"
                           |module B with
                           |  fun value() = A.value()
                           |""".stripMargin)
    fs.write("/C.mls", """import "./B.mls"
                           |let result = B.value()
                           |""".stripMargin)
    fs.write("/Unrelated.mls", "let result = 0")

    compiler.compile("/C.mls")
    compiler.compile("/Unrelated.mls")
    val initialReads = List("/A.mls", "/B.mls", "/C.mls", "/Unrelated.mls")
      .map(path => Path(path) -> fs.readCount(Path(path))).toMap

    fs.write("/A.mls", """fun helper() = "after"
                           |module A with
                           |  fun value() = helper()
                           |""".stripMargin)
    compiler.compile("/C.mls")
    compiler.compile("/Unrelated.mls")

    List("/A.mls", "/B.mls", "/C.mls").foreach: path =>
      assert(fs.readCount(Path(path)) == initialReads(Path(path)) + 1,
        s"Changing A should rebuild the transitive importer $path exactly once")
    assert(fs.readCount(Path("/Unrelated.mls")) == initialReads(Path("/Unrelated.mls")),
      "Changing A should not rebuild an unrelated cached artifact")

  test("cross-state import dependencies use deterministic module-path ordering"):
    val (fs, compiler) = createCompiler()

    def source(moduleName: String, importedName: String): String =
      s"""|import "./nested/../$importedName.js"
          |fun helper() = "This body is deliberately too large for automatic inlining."
          |module $moduleName with
          |  fun exposed() = helper() + $importedName
          |""".stripMargin

    fs.write("/Z.mls", source("Z", "Alpha"))
    fs.write("/A.mls", source("A", "Zulu"))
    // Reverse source order makes UID-only ordering expose state-local UID ties from the two
    // equivalently-shaped imported units. Module paths must decide both import and alias order.
    fs.write("/B.mls", """import "./Z.mls"
                           |import "./A.mls"
                           |A.exposed() + Z.exposed()
                           |""".stripMargin)

    compiler.compile("/B.mls")

    val js = fs.read("/B.mjs")
    val defaultDependencies = js.linesIterator.filter: line =>
      line.startsWith("import Alpha") || line.startsWith("import Zulu")
    val privateDependencies = js.linesIterator.filter(_.contains("modulePrivate")).toList
    assert(defaultDependencies.toList == List(
      "import Alpha from \"./Alpha.js\";",
      "import Zulu from \"./Zulu.js\";",
    ))
    assert(privateDependencies == List(
      "import { _$_modulePrivate_$_helper as helper } from \"./A.mjs\";",
      "import { _$_modulePrivate_$_helper as helper1 } from \"./Z.mjs\";",
    ))

  test("importers reuse immutable inliner body summaries"):
    val stdLib = loadStandardLibrary()
    val fs = new InMemoryFileSystem(stdLib)
    given cctx: CompilerCtx = CompilerCtx.fresh(fs, paths, Config.default(io.Path("/")))
    val compiler = new Compiler

    fs.write("/A.mls", """module A with
                           |  fun value(n) = n + 1
                           |""".stripMargin)
    fs.write("/B.mls", """import "./A.mls"
                           |A.value(1)
                           |""".stripMargin)
    fs.write("/C.mls", """import "./A.mls"
                           |A.value(2)
                           |""".stripMargin)

    compiler.compile("/B.mls")

    given DebugPrinter = new DebugPrinter
    given TL = new TraceLogger:
      override def doTrace = false
    given Raise = diagnostic => fail(diagnostic.toString)
    val prelude = cctx.getPrelude(paths.preludeFile).ctx
    val artifact = cctx.getElaboratedBlock(Path("/A.mls"), prelude)
    var valueDefn: Opt[codegen.FunDefn] = N
    (new codegen.BlockTraverser:
      override def applyFunDefn(fun: codegen.FunDefn): Unit =
        if fun.dSym.nme === "value" then valueDefn = S(fun)
        super.applyFunDefn(fun)
    ).applyProgram(artifact.ir)
    val summary = valueDefn.flatMap(_.inlinerBodySummary |> Option.apply).getOrElse:
      fail("The imported function definition should carry a body summary")

    compiler.compile("/C.mls")

    assert(valueDefn.flatMap(_.inlinerBodySummary |> Option.apply).exists(_ is summary),
      "The second importer should reuse the published summary instead of replacing it")
  
  test("generic method inference does not mutate shared prelude parameters"):
    val fs = new InMemoryFileSystem(loadStandardLibrary())
    given cctx: CompilerCtx = CompilerCtx.fresh(fs, paths, Config.default(io.Path("/")))
    given DebugPrinter = new DebugPrinter
    given TL = new TraceLogger:
      override def doTrace = false
    given Raise = diagnostic => fail(diagnostic.toString)
    val prelude = cctx.getPrelude(paths.preludeFile).ctx
    val map = prelude.builtins.Array.defn.get.body.members("map").asTrm.get.defn.get
    val parameter = map.tparams.get.head.sym
    val originalShapes = parameter.shapes.toVector
    val originalListeners = parameter.shapeListeners.length
    val callbackSignature = map.params.head.params.head.sign.get
    val originalInterpretation = callbackSignature.typeInterpretation

    fs.write("/Generic.mls", """module Generic with
                                 |  fun identity[A](x: A): A = x
                                 |""".stripMargin)
    fs.write("/First.mls", """#lang(0.3.x, strictResolution: true)
                               |import "./Generic.mls"
                               |class Item(val first: Int)
                               |[0].map((x, ...) => Generic.identity(Item(1)))
                               |  .map((x, ...) => x.first)
                               |""".stripMargin)
    fs.write("/Second.mls", """#lang(0.3.x, strictResolution: true)
                                |import "./Generic.mls"
                                |class Item(val second: Int)
                                |[0].map((x, ...) => Generic.identity[Item](Item(2)))
                                |  .map((x, ...) => x.second)
                                |""".stripMargin)
    val compiler = new MLsCompiler(_ => summon[Raise])
    compiler.compileModule(Path("/First.mls"))
    compiler.compileModule(Path("/Second.mls"))

    assert(parameter.shapes.toVector == originalShapes,
      "Consumer inference must not publish into the shared prelude parameter")
    assert(parameter.shapeListeners.length == originalListeners,
      "Consumer inference must not attach listeners to the shared prelude parameter")
    assert(callbackSignature.typeInterpretation == originalInterpretation,
      "Interpreting a legacy signature must not cache consumer listeners on shared syntax")

  test("imported inferred results leave the cached definition's listeners and candidates unchanged"):
    val fs = new InMemoryFileSystem(loadStandardLibrary())
    given cctx: CompilerCtx = CompilerCtx.fresh(fs, paths, Config.default(io.Path("/")))
    given DebugPrinter = new DebugPrinter
    given TL = new TraceLogger:
      override def doTrace = false
    given Raise = diagnostic => fail(diagnostic.toString)
    fs.write("/Generic.mls", """#lang(0.3.x, strictResolution: true)
                                 |module Generic with
                                 |  class Known(val known: Int)
                                 |  val mapped = [Known(4)].map((item, ...) => Known(5))
                                 |  fun identity[A](x: A) = x
                                 |""".stripMargin)
    val compiler = new MLsCompiler(_ => summon[Raise])
    compiler.compileModule(Path("/Generic.mls"))
    val prelude = cctx.getPrelude(paths.preludeFile).ctx
    val library = cctx.getElaboratedBlock(io.Path("/Generic.mls"), prelude)
    val module = library.compilationUnit.defaultExport.get.asModOrObj.get.defn.get
    val identity = module.body.members("identity").asTrm.get.defn.get
    val parameters = identity.params.flatMap(_.params.map(_.sym)) ::: identity.tparams.get.map(_.sym)
    val before = parameters.map(p => (p.shapes.toVector, p.shapeListeners.toVector))
    List("first", "second").foreach: field =>
      val path = s"/$field.mls"
      fs.write(path, s"""#lang(0.3.x, strictResolution: true)
                       |import "./Generic.mls"
                       |class Item(val $field: Int)
                       |Generic.identity(Item(1)).$field
                       |Generic.mapped.map((item, ...) => item.known)
                       |""".stripMargin)
      compiler.compileModule(Path(path))
      assert(parameters.map(p => (p.shapes.toVector, p.shapeListeners.toVector)) == before,
        "A consumer must not change the cached definition's inference graph")

  test("mutable array parameter flow stays private to each importer"):
    val fs = new InMemoryFileSystem(loadStandardLibrary())
    given cctx: CompilerCtx = CompilerCtx.fresh(fs, paths, Config.default(io.Path("/")))
    given DebugPrinter = new DebugPrinter
    given TL = new TraceLogger:
      override def doTrace = false
    given Raise = diagnostic => fail(diagnostic.toString)
    val prelude = cctx.getPrelude(paths.preludeFile).ctx
    val parameter = prelude.builtins.Array.defn.get.tparams.head.sym
    val originalShapes = parameter.shapes.toVector
    val originalListeners = parameter.shapeListeners.toVector
    fs.write("/Arrays.mls", """#lang(0.3.x, strictResolution: true)
                                |module Arrays with
                                |  fun empty() = mut []
                                |  fun singleton[A](x: A) = mut [x]
                                |""".stripMargin)
    val compiler = new MLsCompiler(_ => summon[Raise])
    List("first", "second").foreach: field =>
      val path = s"/$field.mls"
      fs.write(path, s"""#lang(0.3.x, strictResolution: true)
                       |import "./Arrays.mls"
                       |class Item(val $field: Int)
                       |let xs = Arrays.empty()
                       |xs.push(Item(1))
                       |xs.0.$field
                       |Arrays.singleton(Item(2)).0.$field
                       |""".stripMargin)
      compiler.compileModule(Path(path))
      assert(parameter.shapes.toVector == originalShapes,
        "Mutable element inference must not publish into the shared Array parameter")
      assert(parameter.shapeListeners.toVector == originalListeners,
        "Mutable element inference must not attach listeners to the shared Array parameter")

  test("an exported generic selection is rejected before a consumer can specialize it"):
    val fs = new InMemoryFileSystem(loadStandardLibrary())
    given cctx: CompilerCtx = CompilerCtx.fresh(fs, paths, Config.default(io.Path("/")))
    given DebugPrinter = new DebugPrinter
    given TL = new TraceLogger:
      override def doTrace = false
    val errors = scala.collection.mutable.ArrayBuffer.empty[Diagnostic]
    given Raise = errors += _
    fs.write("/Unsafe.mls", """#lang(0.3.x, strictResolution: true)
                                |module Unsafe with
                                |  fun foo[A](x: A) = x.a
                                |Unsafe.foo({a: 1})
                                |""".stripMargin)
    val compiler = new MLsCompiler(_ => summon[Raise])
    compiler.compileModule(Path("/Unsafe.mls"))
    assert(errors.exists(_.theMsg.contains("Resolution error")))
    assert(errors.exists(_.allMsgs.exists(_._1.show.contains("Type parameter 'A'"))))
    assert(!errors.exists(_.allMsgs.exists(_._1.show.contains("exposed by this compilation unit"))))

  test("non-strict files still check their exported interfaces"):
    val fs = new InMemoryFileSystem(loadStandardLibrary())
    given cctx: CompilerCtx = CompilerCtx.fresh(fs, paths, Config.default(io.Path("/")))
    given DebugPrinter = new DebugPrinter
    given TL = new TraceLogger:
      override def doTrace = false
    val errors = scala.collection.mutable.ArrayBuffer.empty[Diagnostic]
    given Raise = errors += _
    fs.write("/Unsafe.mls", """#lang(0.3.x, strictResolution: false)
                                |module Unsafe with
                                |  fun foo(x) = x.a
                                |Unsafe.foo({a: 1})
                                |""".stripMargin)
    val compiler = new MLsCompiler(_ => summon[Raise])
    compiler.compileModule(Path("/Unsafe.mls"))
    assert(errors.exists(_.allMsgs.exists(_._1.show.contains("exposed by this compilation unit"))))

  test("compiler can report errors"):
    val (fs, compiler) = createCompiler()
    
    fs.write("/test.mls", """fun f(x) = x + y""") // `y` is not defined.
    
    val diagnostics = compiler.compile("/test.mls")
    
    assert(diagnostics.length is 1, "Should report diagnostics for only one file")
    
    val hasErrors = diagnostics.exists: perFile =>
      val fileDiagnostics = perFile.diagnostics.asInstanceOf[scala.scalajs.js.Array[scala.scalajs.js.Dynamic]]
      fileDiagnostics.exists(_.kind is "error")
    
    assert(hasErrors, "Compilation should report errors")
