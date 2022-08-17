package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class ClassMember extends AnyFunSuite {
  test("Class Declaration Generation") {
    val program = TSProgram(ClassMember.classMemberFiles)
    var writer = DecWriter(ClassMember.classMemberDiff)

    program.visit(writer)
    writer.close
  }

  test("Inherit Declaration Generation") {
    val program = TSProgram(ClassMember.inheritFiles)
    var writer = DecWriter(ClassMember.inheritDiff)

    program.visit(writer)
    writer.close
  }
}

object ClassMember {
  private val classMemberFiles = TSTypeTest.tsPathes(Seq("ClassMember.ts"))
  private val inheritFiles = TSTypeTest.tsPathes(Seq("Inherit.ts"))
  private val classMemberDiff = TSTypeTest.diffPath("ClassMember.d.mls")
  private val inheritDiff = TSTypeTest.diffPath("Inherit.d.mls")
}