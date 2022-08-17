package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class TypeVariable extends AnyFunSuite {
  test("Type Variable Declaration Generation") {
    val program = TSProgram(TypeVariable.testFiles)
    var writer = DecWriter(TypeVariable.diffFile)

    program.visit(writer)
    writer.close
  }
}

object TypeVariable {
  private val testFiles = TSTypeTest.tsPathes(Seq("TypeVariable.ts"))
  private val diffFile = TSTypeTest.diffPath("TypeVariable.d.mls")
}