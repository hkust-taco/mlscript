package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class InterfaceMember extends AnyFunSuite {
  test("Interface Function Declaration Generation") {
    val program = TSProgram(InterfaceMember.testFiles)
    var writer = DecWriter(InterfaceMember.diffFile)

    program.visit(writer)
    writer.close
  }
}

object InterfaceMember {
  private val testFiles = TSTypeTest.tsPathes(Seq("InterfaceMember.ts"))
  private val diffFile = TSTypeTest.diffPath("InterfaceMember.d.mls")
}