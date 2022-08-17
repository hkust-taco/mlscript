package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class MultiFiles extends AnyFunSuite {
  test("Multiple Files Declaration Generation") {
    val program = TSProgram(MultiFiles.testFiles)
    var writer = DecWriter(MultiFiles.diffFile)

    program.visit(writer)
    writer.close
  }

  test("No File Generation") {
    val program = TSProgram(MultiFiles.emptyTestFiles)
    var writer = DecWriter(MultiFiles.emptyDiffFile)

    program.visit(writer)
    writer.close
  }
}

object MultiFiles {
  private val testFiles = TSTypeTest.tsPathes(Seq("Multi1.ts", "Multi2.ts", "Multi3.ts"))
  private val diffFile = TSTypeTest.diffPath("MultiFiles.d.mls")

  private val emptyTestFiles = TSTypeTest.tsPathes(Seq())
  private val emptyDiffFile = TSTypeTest.diffPath("Empty.d.mls")
}