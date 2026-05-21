package hkmc2

import org.scalatest.funsuite.AnyFunSuite
import io.{InMemoryFileSystem, Path, node}
import mlscript.utils.*, shorthands.*

class AnalysisTest extends AnyFunSuite:
  val projectRoot = node.process.cwd()
  val compilePath = node.path.join(projectRoot, "hkmc2", "shared", "src", "test", "mlscript-compile")
  val runtimePath = node.path.join(projectRoot, "hkmc2", "shared", "src", "test", "mlscript-compile", "RuntimeJS.mjs")
  val preludePath = node.path.join(projectRoot, "hkmc2", "shared", "src", "test", "mlscript", "decls", "Prelude.mls")

  private def loadStandardLibrary(): Map[String, String] =
    node.fs.readdirSync(compilePath).filter:
      fileName => fileName.endsWith(".mls") || fileName.endsWith(".mjs")
    .toSeq.flatMap: fileName =>
      val filePath = node.path.join(compilePath, fileName)
      if node.fs.existsSync(filePath) then
        Some(s"/std/$fileName" -> node.fs.readFileSync(filePath, "utf-8"))
      else
        None
    .toMap
      + ("/std/RuntimeJS.mjs" -> node.fs.readFileSync(runtimePath, "utf-8"))
      + ("/std/Prelude.mls" -> node.fs.readFileSync(preludePath, "utf-8"))

  private val paths = new Paths("/std/Prelude.mls", "/std/Runtime.mjs", "/std/Term.mjs", "/std")

  private def createCompiler(): (InMemoryFileSystem, Compiler) =
    val fs = new InMemoryFileSystem(loadStandardLibrary())
    given CompilerCtx = CompilerCtx.fresh(fs, WebModuleResolver())
    (fs, new Compiler(paths))

  private def child(node: analysis.SymbolNode, name: String): analysis.SymbolNode =
    node.children.find(_.name === name).getOrElse:
      fail(s"Expected child '$name' under '${node.name}', got ${node.children.map(_.name).mkString(", ")}")

  test("analyze returns an elaboration-backed recursive symbol tree without emitting JavaScript"):
    val (fs, compiler) = createCompiler()
    val inputPath = "/OutlineSample.mls"
    val outputPath = "/OutlineSample.mjs"

    fs.write(inputPath,
      """|module OutlineSample with
         |  class Box with
         |    fun get() = 1
         |
         |  object Tools with
         |    fun identity(x) = x
         |
         |  fun top(x) = x
         |""".stripMargin)

    val document = compiler.analyzeDocument(inputPath)

    assert(document.schema === "mlscript.symbol-tree")
    assert(document.version === 1)
    assert(document.rootFile === inputPath)
    assert(document.root.isDefined)
    assert(!fs.exists(Path(outputPath)), "Analysis should not emit a JavaScript output file")

    val root = document.root.get
    assert(root.kind === analysis.SymbolKind.File)
    val module = child(root, "OutlineSample")
    assert(module.kind === analysis.SymbolKind.Module)
    assert(child(module, "Box").kind === analysis.SymbolKind.Class)
    assert(child(child(module, "Box"), "get").kind === analysis.SymbolKind.Function)
    assert(child(module, "Tools").kind === analysis.SymbolKind.Object)
    assert(child(child(module, "Tools"), "identity").kind === analysis.SymbolKind.Function)
    assert(child(module, "top").kind === analysis.SymbolKind.Function)
    assert(document.diagnostics.isEmpty)
