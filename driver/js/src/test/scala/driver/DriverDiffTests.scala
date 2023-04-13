package driver

import org.scalatest.funsuite.AnyFunSuite

class DriverDiffTests extends AnyFunSuite {
  import DriverDiffTests._

  testCases.foreach {
    case TestOption(filename, expectError) => test(filename) {
      val options = DriverOptions(filename, mlscriptPath, jsPath, forceCompiling)
      val driver = Driver(options)
      driver.genPackageJson()
      val success = driver.execute

      assert(success != expectError, s"failed when compiling $filename.")
    }
  }
}

object DriverDiffTests {
  // For local environment, we may change the driver so forcing compiling is necessary
  // but we can ban it during CI
  private val forceCompiling = sys.env.get("CI").isEmpty

  private val diffPath = "driver/js/src/test/"
  private val mlscriptPath = s"${diffPath}mlscript/"
  private val jsPath = s"${diffPath}js/"

  private case class TestOption(
    filename: String,
    expectError: Boolean
  )

  private def entry(filename: String, expectError: Boolean = false) =
    TestOption(s"${mlscriptPath}${filename}", expectError)

  private val testCases = List(
    entry("Simple.mls"),
    entry("Cycle2.mls"),
    entry("Self.mls", true),
    entry("C.mls", true) // FIXME: access to class member not yet supported
  )
}
