package ts2mls

import org.scalatest.funsuite.AnyFunSuite

class TSTypeGenerationTest extends AnyFunSuite {
  import TSTypeGenerationTest._

  testsData.foreach((filename) => test(filename) {
    val program = TSProgram(
      FileInfo("./ts2mls/js/src/test/typescript", filename, "../diff/"),
      false, None)
    program.generate
  })
}

object TSTypeGenerationTest {
  // we only generate type information for builtin declarations here.
  // user-defined scripts may contain errors and printing error messages can lead to test failure
  // if we use the two-pass test.
  // builtin declarations should never contain an error.
  private val testsData = List(
    "./Dom.d.ts",
    "./ES5.d.ts",
  )
}
