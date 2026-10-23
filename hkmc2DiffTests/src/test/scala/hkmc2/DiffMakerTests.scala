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
  
  private def withTestFile[A](source: String)(body: (CompilerCtx, io.Path) => A): A =
    val dir = os.Path(Files.createTempDirectory("diff-maker-tests").toString)
    val testFile = dir / s"Test-${System.nanoTime}.mls"
    os.write.over(testFile, source)
    // * `StubDiffMaker` never reaches the compiler, so these are not read; they name the
    // * project's real layout rather than something under `dir`, so that they stay correct
    // * should a test here ever exercise a `DiffMaker` that does compile.
    val compilerCtx = CompilerCtx.fresh(
      FileSystem.default, TestFolders.compilerPaths(DiffMaker.projectRoot(os.pwd)), Config.default(dir))
    try
      body(compilerCtx, testFile)
    finally
      os.remove.all(dir)
  
  private def rewrite(source: String): String = withTestFile(source): (compilerCtx, testFile) =>
    val dm = new StubDiffMaker(compilerCtx, testFile, "Test")
    dm.run()
    compilerCtx.fs.read(testFile)
  
  // These reports exercise unexpected failures without making the real diff suite
  // fail. They include current, earlier, and imported origins so location policy
  // is checked independently of the line numbers or filenames they happen to use.
  private def rewriteLocationReports(source: String, preludeLine: Int): (String, List[Int]) =
    withTestFile(source): (compilerCtx, testFile) =>
      val dm = new StubDiffMaker(compilerCtx, testFile, "Test"):
        override def doFail(blockLineNum: Int, msg: String): Unit = ()
        override def processOrigin(origin: Origin)(using Raise): Unit =
          if origin.fph.blockStr == "crash" then throw new IllegalStateException("test failure")
          val preludeSource = "first line\nsecond line"
          val preludeOrigin = Origin(cctx.paths.preludeFile, preludeLine,
            new FastParseHelpers(preludeSource.split('\n').toIndexedSeq))
          val previousOrigin = Origin(file, 1, new FastParseHelpers(Vector("previous block")))
          val otherOrigin = Origin(file.up / "Prelude.mls", 17, new FastParseHelpers(Vector("other line")))
          summon[Raise](WarningReport(List(
            Message.fromStr("Test source") -> Some(Loc(0, origin.fph.blockStr.length, origin)),
            Message.fromStr("Earlier test source") -> Some(Loc(0, 0, previousOrigin)),
            Message.fromStr("Prelude definition") -> Some(Loc(0, preludeSource.length, preludeOrigin)),
            Message.fromStr("Other definition") -> Some(Loc(0, 0, otherOrigin)),
            Message.fromStr("Current test source again") -> Some(Loc(0, 0, origin)),
          )))
          output("Ordinary output: l.1234 Prelude.mls:1234")
      dm.run()
      (compilerCtx.fs.read(testFile), dm.failures.toList)
  
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
  
  test("diagnostics use stable block locations until an unexpected failure") {
    val source = "\n:w\nmessage\ncontinuation\n\nmessage\ncontinuation\n\n:w\nmessage\ncontinuation\n"
    val (rewritten, failures) = rewriteLocationReports(source, 1234)
    assert(failures.nonEmpty)
    val sourceLines = rewritten.linesIterator.zipWithIndex.collect:
      case ("message", index) => index + 1
    val expectedCurrentLocations = sourceLines.zipWithIndex.flatMap: (line, block) =>
      List.fill(2)(s"//│ ║  l.${if block == 0 then "+1" else line.toString}: \tmessage")
    assert(rewritten.linesIterator.filter(_.endsWith(": \tmessage")).toList === expectedCurrentLocations.toList)
    assert(rewritten.contains("l.+2: \tcontinuation"))
    assert(rewritten.linesIterator.exists(line => line.contains("in Test-") && line.endsWith(".mls:+1")))
    assert(rewritten.linesIterator.filter(_.endsWith(": \tprevious block")).toList === List(
      "//│ ║  l.XX: \tprevious block",
      "//│ ║  l.1: \tprevious block",
      "//│ ║  l.1: \tprevious block",
    ))
    assert(rewritten.linesIterator.filter(_.endsWith(": \tfirst line")).toList === List(
      "//│ ║  l.XX: \tfirst line",
      "//│ ║  l.1234: \tfirst line",
      "//│ ║  l.1234: \tfirst line",
    ))
    assert(rewritten.contains("l.1235: \tsecond line"))
    assert(rewritten.contains("Prelude.mls:1234"))
  }
  
end DiffMakerTests
