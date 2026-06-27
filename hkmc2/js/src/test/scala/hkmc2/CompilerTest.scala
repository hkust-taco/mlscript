package hkmc2

import org.scalatest.funsuite.AnyFunSuite
import io.{InMemoryFileSystem, Path, node}
import hkmc2.utils.*, shorthands.*
import scala.scalajs.js
import scala.scalajs.js.annotation._
import scala.scalajs.js.Dynamic.global

class CompilerTest extends AnyFunSuite:
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
    given CompilerCtx = CompilerCtx.fresh(fs)
    (fs, new Compiler(paths))
  
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
  
  test("compiler can report errors"):
    val (fs, compiler) = createCompiler()
    
    fs.write("/test.mls", """fun f(x) = x + y""") // `y` is not defined.
    
    val diagnostics = compiler.compile("/test.mls")
    
    assert(diagnostics.length is 1, "Should report diagnostics for only one file")
    
    val hasErrors = diagnostics.exists: perFile =>
      val fileDiagnostics = perFile.diagnostics.asInstanceOf[scala.scalajs.js.Array[scala.scalajs.js.Dynamic]]
      fileDiagnostics.exists(_.kind is "error")
    
    assert(hasErrors, "Compilation should report errors")
