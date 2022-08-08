import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class Optional extends AnyFunSuite {
  test("Optional") {
    val program = TSProgram(Seq("src/test/typescript/Optional.ts"))
    assert(TypeCompare(program.>("buildName"), "(string, string | undefined) => string"))
    assert(TypeCompare(program.>("buildName2"), "(string, string | undefined) => string"))
    assert(TypeCompare(program.>("buildName3"), "(string, any[]) => string"))

    assert(TypeCompare(program.>("SquareConfig").>("color"), "string | undefined"))
    assert(TypeCompare(program.>("SquareConfig").>("width"), "number | undefined"))

    assert(TypeCompare(program.>("did"), "(number, ((number) => number) | undefined) => number"))
    assert(TypeCompare(program.>("getOrElse"), "(object[] | undefined) => object"))
    assert(TypeCompare(program.>("testABC"), "(ABC | undefined) => void"))
    assert(TypeCompare(program.>("testSquareConfig"), "(SquareConfig | undefined) => void"))
    assert(TypeCompare(program.>("err"), "([number, string] | undefined) => void"))
    assert(TypeCompare(program.>("toStr"), "(number | boolean | undefined) => string"))
    assert(TypeCompare(program.>("boo"), "(T' & U' | undefined) => void"))
    assert(TypeCompare(program.>("boom"), "(B<never> | undefined) => any"))
  }
}
