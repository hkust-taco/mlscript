import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class Overload extends AnyFunSuite {
  test("Overload") {
    val program = TSProgram(Seq("src/test/typescript/Overload.ts"))
    assert(TypeCompare(program.>("f"), "((number) => number) & ((string) => string)"))

    assert(TypeCompare(program.>("M").>("foo"), "((number) => number) & ((string) => string)"))

    assert(TypeCompare(program.>("app"), "(((number) => void, number) => void) & (((string) => void, string) => void)"))
    assert(TypeCompare(program.>("create"), "((number) => number) & ((boolean) => boolean)"))
    assert(TypeCompare(program.>("g0"), "((string[]) => string) & ((object[]) => object)"))
    assert(TypeCompare(program.>("db"), "((number) => number[]) & ((object) => object[])"))

    assert(TypeCompare(program.>("id"), "((M) => {foo: (any) => any}) & ((N) => {})"))

    assert(TypeCompare(program.>("tst"), "(({z: number}) => {y: string}) & (({z: boolean}) => {y: string})"))
    assert(TypeCompare(program.>("op"), "((number, number | undefined) => void) & ((number, boolean | undefined) => void)"))
    assert(TypeCompare(program.>("swap"), "(([number, string]) => [string, number]) & (([string, number]) => [number, string])"))
    assert(TypeCompare(program.>("u"), "((number | boolean) => string) & ((object) => string | object)"))
    assert(TypeCompare(program.>("doSome"), "((T' & U') => T' & U') & ((string) => never)"))

    assert(TypeCompare(program.>("bar"), "((G<string>) => G<string>) & ((G<number>) => G<number>) & ((G<boolean>) => G<boolean>)"))
  }
}

