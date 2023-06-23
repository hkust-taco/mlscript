package ts2mls

import org.scalatest.funsuite.AnyFunSuite
import scala.collection.immutable
import TSPathResolver.basename
import ts2mls.TSPathResolver

class TSTypeGenerationTest extends AnyFunSuite {
  import TSTypeGenerationTest._

  testsData.foreach((filename) => test(filename) {
    val program = TSProgram(
      FileInfo("./ts2mls/js/src/test/typescript", filename, "../diff/"),
      !directlyImportedSet.contains(filename),
      None
    )
    program.generate
  })
}

object TSTypeGenerationTest {
  private val testsData = List(
    "./BasicFunctions.ts",
    "./ClassMember.ts",
    "./Cycle1.ts",
    "./Dec.d.ts",
    "./Dom.d.ts",
    "./Enum.ts",
    "./ES5.d.ts",
    "./Escape.ts",
    "./Export.ts",
    "./Heritage.ts",
    "./HighOrderFunc.ts",
    "./Import.ts",
    "./InterfaceMember.ts",
    "./Intersection.ts",
    "./Literal.ts",
    "./Namespace.ts",
    "./Optional.ts",
    "./Overload.ts",
    "./TSArray.ts",
    "./Tuple.ts",
    "./Type.ts",
    "./TypeParameter.ts",
    "./Union.ts",
    "./Variables.ts",
  )

  private val directlyImportedSet = Set[String]("./ES5.d.ts", "./Dom.d.ts")
}
