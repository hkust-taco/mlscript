package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class HighOrderFunc extends AnyFunSuite {
  test("High Order Declaration Generation") {
    val program = TSProgram(HighOrderFunc.testFiles)
    var writer = DecWriter(HighOrderFunc.diffFile)

    program.visit(writer)
    writer.close
  }
}

object HighOrderFunc {
  private val testFiles = TSTypeTest.tsPathes(Seq("HighOrderFunc.ts"))
  private val diffFile = TSTypeTest.diffPath("HighOrder.d.mls")
}