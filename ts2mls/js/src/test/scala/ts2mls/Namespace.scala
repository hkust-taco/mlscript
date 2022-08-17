package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class Namespace extends AnyFunSuite {
  test("Namespace Declaration Generation") {
    val program = TSProgram(Namespace.testFiles)
    var writer = DecWriter(Namespace.diffFile)

    program.visit(writer)
    writer.close
  }
}

object Namespace {
  private val testFiles = TSTypeTest.tsPathes(Seq("NameSpace.ts"))
  private val diffFile = TSTypeTest.diffPath("Namespace.d.mls")
}