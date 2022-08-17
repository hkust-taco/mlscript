package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class Overload extends AnyFunSuite {
  test("Overload Declaration Generation") {
    val program = TSProgram(Overload.testFiles)
    var writer = DecWriter(Overload.diffFile)

    program.visit(writer)
    writer.close
  }
}

object Overload {
  private val testFiles = TSTypeTest.tsPathes(Seq("Overload.ts"))
  private val diffFile = TSTypeTest.diffPath("Overload.d.mls")
}
