import org.scalatest.funsuite.AnyFunSuite
import ts2mls.TSProgram
import ts2mls.types._

class ClassMember extends AnyFunSuite {
  test("Class Member") {
    val program = TSProgram(Seq("src/test/typescript/ClassMember.ts"))
    val cls: TSType = program.>("Student")
    assert(TypeCompare(cls.>("getID"), "number"))
    assert(TypeCompare(cls.>("addScore"), "(string, number) => void"))
    assert(TypeCompare(cls.>("isFriend"), "(Student) => boolean"))
    assert(TypeCompare(cls.>("name"), "string"))
    assert(TypeCompare(cls.>("a"), "- number"))
    assert(TypeCompare(cls.>("b"), "o string"))

    assert(TypeCompare(program.>("Foo").>("bar"), "(T') => void"))
  }

  test("Inherit") {
    val program = TSProgram(Seq("src/test/typescript/Inherit.ts"))
    val cls: TSType = program.>("B")
    assert(TypeCompare(cls.>("foo"), "void"))

    program.>("D") match {
      case TSClassType(_, _, _, parents) => assert(TypeCompare(parents(0), "class C<number>"))
    }

    assert(TypeCompare(program.>("D").>("set"), "(number) => void"))
    assert(TypeCompare(program.>("D").>("get"), "number"))
  }

  test("Class Convert") {
    import mlscript._

    val program = TSProgram(Seq("src/test/typescript/ClassMember.ts"))

    program.getMLSType("EZ") match {
      case Record(members) => {
        assert(members.length == 1)

        members(0)._1 match {
          case Var(name) => assert(name.equals("inc"))
          case _ => assert(false)
        }
      }
      case _ => assert(false)
    }
  }
}
