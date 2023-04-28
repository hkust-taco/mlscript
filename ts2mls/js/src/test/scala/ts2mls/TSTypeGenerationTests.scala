package ts2mls

import org.scalatest.funsuite.AnyFunSuite

class TSTypeGenerationTest extends AnyFunSuite {
  import TSTypeGenerationTest._

  testsData.foreach((data) => test(data._2) {
    val program = TSProgram(tsPath(data._1), true)
    var writer = JSWriter(diffPath(data._2))
    program.generate(writer)
    writer.close()
  })
}

object TSTypeGenerationTest {
  private def tsPath(filenames: Seq[String]) = filenames.map((fn) => s"ts2mls/js/src/test/typescript/$fn")
  private def diffPath(filename: String) = s"ts2mls/js/src/test/diff/$filename"

  private val testsData = List(
    (Seq("Array.ts"), "Array.mlsi"),
    (Seq("BasicFunctions.ts"), "BasicFunctions.mlsi"),
    (Seq("ClassMember.ts"), "ClassMember.mlsi"),
    (Seq("Dec.d.ts"), "Dec.mlsi"),
    (Seq("Enum.ts"), "Enum.mlsi"),
    (Seq("ES5.d.ts"), "ES5.mlsi"),
    (Seq("Export.ts"), "Export.mlsi"),
    (Seq("Heritage.ts"), "Heritage.mlsi"),
    (Seq("HighOrderFunc.ts"), "HighOrderFunc.mlsi"),
    (Seq("InterfaceMember.ts"), "InterfaceMember.mlsi"),
    (Seq("Intersection.ts"), "Intersection.mlsi"),
    (Seq("Literal.ts"), "Literal.mlsi"),
    (Seq("Namespace.ts"), "Namespace.mlsi"),
    (Seq("Optional.ts"), "Optional.mlsi"),
    (Seq("Overload.ts"), "Overload.mlsi"),
    (Seq("Tuple.ts"), "Tuple.mlsi"),
    (Seq("Type.ts"), "Type.mlsi"),
    (Seq("TypeParameter.ts"), "TypeParameter.mlsi"),
    (Seq("Union.ts"), "Union.mlsi"),
    (Seq("Variables.ts"), "Variables.mlsi"),
  )
}
