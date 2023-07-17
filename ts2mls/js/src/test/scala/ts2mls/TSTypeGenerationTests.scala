package ts2mls

import org.scalatest.funsuite.AnyFunSuite

class TSTypeGenerationTest extends AnyFunSuite {
  import TSTypeGenerationTest._

  testsData.foreach((filename) => test(filename) {
    val program = TSProgram(
      FileInfo("./ts2mls/js/src/test/typescript", filename, "../../../../../driver/npm/predefs"),
      false, None, (file: FileInfo, writer: JSWriter) => (), None) // No need for builtin check
    program.generate
  })
}

object TSTypeGenerationTest {
  // We only generate type information for builtin declarations here.
  // User-defined scripts may contain errors and printing error messages can lead to test failure
  // if we use the two-pass test.
  // Builtin declarations should never contain an error.
  private val testsData = List(
    "./Dom.d.ts",
    "./ES5.d.ts",
  )
}
