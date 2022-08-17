package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class Optional extends AnyFunSuite {
  test("Optional Declaration Generation") {
    val program = TSProgram(Optional.testFiles)
    var writer = DecWriter(Optional.diffFile)

    program.visit(writer)
    writer.close
  }
}

object Optional {
  private val testFiles = TSTypeTest.tsPathes(Seq("Optional.ts"))
  private val diffFile = TSTypeTest.diffPath("Optional.d.mls")
}