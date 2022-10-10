package ts2mls

import org.scalatest.funsuite.AnyFunSuite

class TSTypeGenerationTest extends AnyFunSuite {
  import TSTypeGenerationTest._
  
  testsData.foreach((data) => test(data._2) {
    val program = TSProgram(tsPath(data._1))
    var writer = JSWriter(diffPath(data._2))
    program.generate(writer)
    writer.close()
  })
}

object TSTypeGenerationTest {
  private def tsPath(filenames: Seq[String]) = filenames.map((fn) => s"ts2mls/js/src/test/typescript/$fn")
  private def diffPath(filename: String) = s"ts2mls/js/src/test/diff/$filename"

  private val testsData = List(
    (Seq("Array.ts"), "Array.d.mls"),
    (Seq("BasicFunctions.ts"), "BasicFunctions.d.mls"),
    (Seq("ClassMember.ts"), "ClassMember.d.mls"),
    (Seq("Enum.ts"), "Enum.d.mls"),
    (Seq("Heritage.ts"), "Heritage.d.mls"),
    (Seq("HighOrderFunc.ts"), "HighOrderFunc.d.mls"),
    (Seq("InterfaceMember.ts"), "InterfaceMember.d.mls"),
    (Seq("Intersection.ts"), "Intersection.d.mls"),
    (Seq("Multi1.ts", "Multi2.ts", "Multi3.ts"), "MultiFiles.d.mls"),
    (Seq("Namespace.ts"), "Namespace.d.mls"),
    (Seq("Optional.ts"), "Optional.d.mls"),
    (Seq("Overload.ts"), "Overload.d.mls"),
    (Seq("Tuple.ts"), "Tuple.d.mls"),
    (Seq("TypeParameter.ts"), "TypeParameter.d.mls"),
    (Seq("Union.ts"), "Union.d.mls"),
    (Seq("Type.ts"), "Type.d.mls")
  )
}
