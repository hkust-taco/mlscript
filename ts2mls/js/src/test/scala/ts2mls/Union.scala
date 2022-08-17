package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class Union extends AnyFunSuite {
  test("Union Declaration Generation") {
    val program = TSProgram(Union.testFiles)
    var writer = DecWriter(Union.diffFile)

    program.visit(writer)
    writer.close
  }
}

object Union {
  private val testFiles = TSTypeTest.tsPathes(Seq("Union.ts"))
  private val diffFile = TSTypeTest.diffPath("Union.d.mls")
}