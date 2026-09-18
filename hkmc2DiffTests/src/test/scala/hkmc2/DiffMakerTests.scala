package hkmc2

import java.nio.file.Files

import org.scalatest.funsuite.AnyFunSuite

import io.{FileSystem, PlatformPath}
import io.PlatformPath.given

class DiffMakerTests extends AnyFunSuite:
  
  private class StubDiffMaker(
    val cctx: CompilerCtx,
    val file: io.Path,
    val relativeName: String,
  ) extends DiffMaker:
    val dbgPrinter: DebugPrinter = new DebugPrinter
    def processOrigin(origin: Origin)(using Raise): Unit =
      origin.fph.blockStr match
        case "1" => output("= 1")
        case "2" => output("= 2")
        case _ => ()
  
  private def rewrite(source: String): String =
    val dir = os.Path(Files.createTempDirectory("diff-maker-tests").toString)
    val testFile = dir / s"Test-${System.nanoTime}.mls"
    os.write.over(testFile, source)
    // * `StubDiffMaker` never reaches the compiler, so these are not read; they name the
    // * project's real layout rather than something under `dir`, so that they stay correct
    // * should a test here ever exercise a `DiffMaker` that does compile.
    val compilerCtx = CompilerCtx.fresh(
      FileSystem.default, TestFolders.compilerPaths(DiffMaker.projectRoot(os.pwd)), Config.default(dir))
    try
      val dm = new StubDiffMaker(compilerCtx, testFile, "Test")
      dm.run()
      os.read(testFile)
    finally
      os.remove.all(dir)
  
  test("preserves an output separator line between adjacent blocks") {
    val input =
      """fun f() = 1
        |//│ old A
        |//│ old B
        |//│ old C
        |1
        |//│ = 1""".stripMargin
    val expected =
      """fun f() = 1
        |//│ 
        |1
        |//│ = 1
        |""".stripMargin
    
    val rewritten = rewrite(input)
    
    assert(rewritten === expected)
    assert(rewrite(rewritten) === expected)
  }
  
  test("does not add a separator line when the previous block still has output") {
    val input =
      """1
        |//│ old 1
        |2
        |//│ old 2""".stripMargin
    val expected =
      """1
        |//│ = 1
        |2
        |//│ = 2
        |""".stripMargin
    
    val rewritten = rewrite(input)
    
    assert(rewritten === expected)
    assert(rewrite(rewritten) === expected)
  }
  
end DiffMakerTests
