package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class BasicFunction extends AnyFunSuite {
  test("Basic Function Declaration Generation") {
    val program = TSProgram(BasicFunction.testFiles)
    var writer = DecWriter(BasicFunction.diffFile)

    program.visit(writer)
    writer.close
  }
}

object BasicFunction {
  private val testFiles = TSTypeTest.tsPathes(Seq("BasicFunctions.ts"))
  private val diffFile = TSTypeTest.diffPath("BasicFunctions.d.mls")
}