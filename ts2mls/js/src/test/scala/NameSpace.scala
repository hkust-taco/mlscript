import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class NameSpace extends AnyFunSuite {
  test("Name Space") {
    val program = TSProgram(Seq("src/test/typescript/NameSpace.ts"))
    val ns = program.>>("N1")
    assert(TypeCompare(ns.>("f"), "(any) => number"))
    assert(TypeCompare(ns.>("C").>("f"), "void"))
    assert(TypeCompare(ns.>>("N2").>("fff"), "(boolean) => number"))
    assert(TypeCompare(ns.>>("N2").>("f"), "(any) => number"))
  }
}
