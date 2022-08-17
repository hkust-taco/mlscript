package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class Tuple extends AnyFunSuite {
  test("Tuple Declaration Generation") {
    val program = TSProgram(Tuple.testFiles)
    var writer = DecWriter(Tuple.diffFile)

    program.visit(writer)
    writer.close
  }
}

object Tuple {
  private val testFiles = TSTypeTest.tsPathes(Seq("Tuple.ts"))
  private val diffFile = TSTypeTest.diffPath("Tuple.d.mls")
}