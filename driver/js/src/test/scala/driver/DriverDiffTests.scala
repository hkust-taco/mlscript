package driver

import org.scalatest.funsuite.AnyFunSuite
import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import mlscript.utils._, shorthands._

class DriverDiffTests extends AnyFunSuite {
  import DriverDiffTests._

  testCases.foreach {
    case TestOption(filename, executionFile, outputFile, expectError) => test(filename) {
      val options = DriverOptions(filename, mlscriptPath, jsPath, forceCompiling)
      val driver = Driver(options)
      driver.genPackageJson()
      val success = driver.execute

      assert(success != expectError, s"failed when compiling $filename.")

      if (!expectError) {
        val output = cp.execSync(s"node $executionFile").toString()
        val original = Driver.readFile(outputFile).getOrElse("")
        if (original =/= output) fs.writeFileSync(outputFile, output)
      }
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
  private val outputPath = s"${diffPath}output/"

  private case class TestOption(
    filename: String,
    executionFile: String,
    outputFile: String,
    expectError: Boolean
  )

  private def entry(entryModule: String, expectError: Boolean = false) =
    TestOption(
      s"${mlscriptPath}${entryModule}.mls",
      s"${jsPath}${entryModule}.js",
      s"${outputPath}${entryModule}.txt",
      expectError
    )

  private val testCases = List(
    entry("Simple"),
    entry("Cycle2"),
    entry("Self", true),
    entry("C", true)
  )

  private val cp = g.require("child_process")
  private val fs = g.require("fs")
}
