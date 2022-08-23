package ts2mls

import org.scalatest.funsuite.AnyFunSuite

class TSTypeGenerationTest(tsFiles: Seq[String], diffFile: String) extends AnyFunSuite {
  test(diffFile) {
    import TSTypeGenerationTest._

    val program = TSProgram(tsPath(tsFiles))
    var writer = DecWriter(diffPath(diffFile))
    program.visit(writer)
    writer.close
  }
}

object TSTypeGenerationTest {
  private def tsPath(filenames: Seq[String]) = filenames.map((fn) => s"ts2mls/js/src/test/typescript/$fn")
  private def diffPath(filename: String) = s"ts2mls/js/src/test/diff/$filename"
}

class ArrayTest extends TSTypeGenerationTest(Seq("Array.ts"), "Array.d.mls")
class BasicFunctionTest extends TSTypeGenerationTest(Seq("BasicFunctions.ts"), "BasicFunctions.d.mls")
class ClassMemberTest extends TSTypeGenerationTest(Seq("ClassMember.ts"), "ClassMember.d.mls")
class EnumTest extends TSTypeGenerationTest(Seq("Enum.ts"), "Enum.d.mls")
class HeritageTest extends TSTypeGenerationTest(Seq("Heritage.ts"), "Heritage.d.mls")
class HighOrderFuncTest extends TSTypeGenerationTest(Seq("HighOrderFunc.ts"), "HighOrderFunc.d.mls")
class InterfaceMemberTest extends TSTypeGenerationTest(Seq("InterfaceMember.ts"), "InterfaceMember.d.mls")
class IntersectionTest extends TSTypeGenerationTest(Seq("Intersection.ts"), "Intersection.d.mls")
class MultiFilesTest extends TSTypeGenerationTest(Seq("Multi1.ts", "Multi2.ts", "Multi3.ts"), "MultiFiles.d.mls")
class NamespaceTest extends TSTypeGenerationTest(Seq("Namespace.ts"), "Namespace.d.mls")
class OptionalTest extends TSTypeGenerationTest(Seq("Optional.ts"), "Optional.d.mls")
class OverloadTest extends TSTypeGenerationTest(Seq("Overload.ts"), "Overload.d.mls")
class TupleTest extends TSTypeGenerationTest(Seq("Tuple.ts"), "Tuple.d.mls")
class TypeVariableTest extends TSTypeGenerationTest(Seq("TypeVariable.ts"), "TypeVariable.d.mls")
class UnionTest extends TSTypeGenerationTest(Seq("Union.ts"), "Union.d.mls")
