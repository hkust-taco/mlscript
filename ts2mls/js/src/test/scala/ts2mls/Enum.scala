package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class Enum extends AnyFunSuite {
  test("Enum Declaration Generation") {
    val program = TSProgram(Enum.testFiles)
    var writer = DecWriter(Enum.diffFile)

    program.visit(writer)
    writer.close
  }
}

object Enum {
  private val testFiles = TSTypeTest.tsPathes(Seq("Enum.ts"))
  private val diffFile = TSTypeTest.diffPath("Enum.d.mls")
}