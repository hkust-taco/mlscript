package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import scala.collection.immutable

class TSTypeGenerationTest extends AnyFunSuite {
  import TSTypeGenerationTest._

  testsData.foreach((data) => test(data._2) {
    val program = TSProgram(tsPath(data._1), !directlyImportedSet.contains(data._1))
    var writer = JSWriter(diffPath(data._2))
    program.generate(writer)
    writer.close()
  })
}

object TSTypeGenerationTest {
  private def tsPath(filename: String) = s"ts2mls/js/src/test/typescript/$filename"
  private def diffPath(filename: String) = s"ts2mls/js/src/test/diff/$filename"

  // TODO: do better?
  private val testsData = List(
    ("Array.ts", "Array.mlsi"),
    ("BasicFunctions.ts", "BasicFunctions.mlsi"),
    ("ClassMember.ts", "ClassMember.mlsi"),
    ("Dec.d.ts", "Dec.mlsi"),
    ("Enum.ts", "Enum.mlsi"),
    ("ES5.d.ts", "ES5.mlsi"),
    ("Export.ts", "Export.mlsi"),
    ("Heritage.ts", "Heritage.mlsi"),
    ("HighOrderFunc.ts", "HighOrderFunc.mlsi"),
    ("InterfaceMember.ts", "InterfaceMember.mlsi"),
    ("Intersection.ts", "Intersection.mlsi"),
    ("Literal.ts", "Literal.mlsi"),
    ("Namespace.ts", "Namespace.mlsi"),
    ("Optional.ts", "Optional.mlsi"),
    ("Overload.ts", "Overload.mlsi"),
    ("Tuple.ts", "Tuple.mlsi"),
    ("Type.ts", "Type.mlsi"),
    ("TypeParameter.ts", "TypeParameter.mlsi"),
    ("Union.ts", "Union.mlsi"),
    ("Variables.ts", "Variables.mlsi"),
  )

  private val directlyImportedSet = Set[String]("ES5.d.ts")
}
