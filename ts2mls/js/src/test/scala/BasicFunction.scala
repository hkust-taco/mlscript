import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class BasicFunction extends AnyFunSuite {
  test("Basic Function") {
    val program = TSProgram(Seq("src/test/typescript/BasicFunctions.ts"))
    assert(TypeCompare(program.>("hello"), "void"))
    assert(TypeCompare(program.>("add"), "(number, number) => number"))
    assert(TypeCompare(program.>("sub"), "(number, number) => number"))
    assert(TypeCompare(program.>("foo"), "number"))
    assert(TypeCompare(program.>("id"), "(any) => any"))
    assert(TypeCompare(program.>("odd"), "(number) => boolean"))
    assert(TypeCompare(program.>("isnull"), "(any) => boolean"))
    assert(TypeCompare(program.>("bar"), "any"))
    assert(TypeCompare(program.>("nu"), "(null) => null"))
    assert(TypeCompare(program.>("un"), "(undefined) => undefined"))
    assert(TypeCompare(program.>("fail"), "never"))
    assert(TypeCompare(program.>("create"), "object"))
    assert(TypeCompare(program.>("pa"), "(number) => number"))
    assert(TypeCompare(program.>("wtf"), "(unknown) => void"))
  }

  test("Basic Convert") {
    import mlscript._

    val program = TSProgram(Seq("src/test/typescript/BasicFunctions.ts"))

    program.getMLSType("hello") match {
      case Function(lhs, rhs) => {
        rhs match {
          case TypeName(name) => assert(name.equals("unit"))
          case _ => assert(false)
        }

        lhs match {
          case TypeName(name) => assert(name.equals("unit"))
          case _ => assert(false)
        }
      }
      case _ => assert(false)
    }

    program.getMLSType("add") match {
      case Function(lhs, rhs) => {
        lhs match {
          case TypeName(name) => assert(name.equals("number"))
          case _ => assert(false)
        }

        rhs match {
          case Function(lhs2, rhs2) => assert(true)
          case _ => assert(false)
        }
      }
      case _ => assert(false)
    }

    program.getMLSType("id") match {
      case Function(lhs, rhs) => {
        lhs match {
          case Top => assert(true)
          case _ => assert(false)
        }

        rhs match {
          case Top => assert(true)
          case _ => assert(false)
        }
      }
      case _ => assert(false)
    }

    program.getMLSType("wtf") match {
      case Function(p, r) => p match {
        case Top => assert(true)
        case _ => assert(false)
      }
      case _ => assert(false)
    }
  } 
}
