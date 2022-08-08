import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class Array extends AnyFunSuite {
  test("Array") {
    val program = TSProgram(Seq("src/test/typescript/Array.ts"))
    assert(TypeCompare(program.>("first"), "(string[]) => string"))
    assert(TypeCompare(program.>("getZero3"), "number[]"))
    assert(TypeCompare(program.>("first2"), "(((number) => number)[]) => (number) => number"))
  }

  test("Array Convert") {
    import mlscript._

    val program = TSProgram(Seq("src/test/typescript/Array.ts"))

    program.getMLSType("getZero3") match {
      case Function(p, r) => r match {
        case TypeName(name) => assert(name.equals("MutArray"))
        case _ => assert(false)
      }
      case _ => assert(false)
    }
  }
}
