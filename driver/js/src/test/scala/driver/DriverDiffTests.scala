package driver

import org.scalatest.funsuite.AnyFunSuite
import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import mlscript.utils._, shorthands._

class DriverDiffTests extends AnyFunSuite {
  import DriverDiffTests._
  import ts2mls.JSFileSystem._

  testCases.foreach {
    case TestOption(filename, workDir, outputDir, interfaceDir, cjs, execution, tsconfig, ignoreTypeError, expectError) => test(filename) {
      val options =
        DriverOptions(filename, workDir, outputDir, tsconfig, interfaceDir, cjs, ignoreTypeError, forceCompiling)
      val driver = Driver(options)
      if (!outputDir.isEmpty()) driver.genPackageJson()
      val success = driver.execute

      assert(success != expectError, s"failed when compiling $filename.")

      if (!expectError) execution match {
        case Some((executionFile, outputFile)) =>
          val output = cp.execSync(s"node $executionFile").toString()
          val original = readFile(outputFile).getOrElse("")
          if (original =/= output) fs.writeFileSync(outputFile, output)
        case None => ()
      }
    }
  }
}

object DriverDiffTests {
  // For local environment, we may change the driver so forcing compiling is necessary
  // but we can ban it during CI
  private val forceCompiling = true

  private val diffPath = "driver/js/src/test/"
  private val outputPath = s"${diffPath}output/"
  private val ts2mlsPath = "ts2mls/js/src/test/diff"

  private case class TestOption(
    filename: String,
    workDir: String,
    outputDir: String,
    interfaceDir: String,
    commonJS: Boolean,
    execution: Option[(String, String)],
    tsconfig: Option[String],
    ignoreTypeError: Boolean,
    expectError: Boolean
  )

  private def driverEntry(
    entryModule: String,
    tsconfig: Option[String],
    workDir: String,
    jsPath: String,
    ignoreTypeError: Boolean,
    expectError: Boolean,
    commonJS: Boolean
  ) = TestOption(
      s"./mlscript/${entryModule}.mls",
      workDir,
      jsPath,
      ".interfaces",
      commonJS,
      Some((s"${jsPath}mlscript/${entryModule}.js", s"${outputPath}${entryModule}.check")),
      tsconfig,
      ignoreTypeError,
      expectError
    )

  private def cjsEntry(
    entryModule: String,
    tsconfig: Option[String] = None,
    ignoreTypeError: Boolean = false,
    expectError: Boolean = false
  ) = driverEntry(entryModule, tsconfig, s"${diffPath}cjsprojects/",
    s"${diffPath}cjsprojects/js/", ignoreTypeError, expectError, true)

  private def esEntry(
    entryModule: String,
    tsconfig: Option[String] = None,
    ignoreTypeError: Boolean = false,
    expectError: Boolean = false
  ) = driverEntry(entryModule, tsconfig, s"${diffPath}esprojects/",
    s"${diffPath}esprojects/js/", ignoreTypeError, expectError, false)

  private def ts2mlsEntry(entryModule: String, ignoreTypeError: Boolean = false, expectError: Boolean = false) =
    TestOption(s"./${entryModule}.mlsi", ts2mlsPath, "", ".", false, None, None, ignoreTypeError, expectError)

  private val testCases = List[TestOption](
    esEntry("Simple"),
    esEntry("Cycle2"),
    esEntry("Self", expectError = true),
    esEntry("C", ignoreTypeError = true, expectError = true),
    esEntry("TS", Some("./tsconfig.json"), ignoreTypeError = true), // TODO: type members
    esEntry("Output", Some("./tsconfig.json"), ignoreTypeError = true), // TODO: type parameter position
    esEntry("Output2", Some("./tsconfig.json"), ignoreTypeError = true), // TODO: type parameter position
    esEntry("MLS2TheMax", Some("./tsconfig.json")),
    esEntry("MyPartialOrder", Some("./tsconfig.json"), expectError = true), // TODO: type traits in modules
    cjsEntry("Lodash", Some("./tsconfig.json"), ignoreTypeError = true), // TODO: module member selection
    esEntry("Builtin"),
    cjsEntry("CJS1"),
    ts2mlsEntry("BasicFunctions", ignoreTypeError = true),
    ts2mlsEntry("ClassMember"),
    ts2mlsEntry("Cycle1", ignoreTypeError = true),
    ts2mlsEntry("Dec", ignoreTypeError = true),
    ts2mlsEntry("Enum"),
    ts2mlsEntry("Escape"),
    ts2mlsEntry("Export", ignoreTypeError = true),
    ts2mlsEntry("Heritage", ignoreTypeError = true),
    ts2mlsEntry("HighOrderFunc"),
    ts2mlsEntry("Import"),
    ts2mlsEntry("InterfaceMember", ignoreTypeError = true),
    ts2mlsEntry("Intersection", ignoreTypeError = true),
    ts2mlsEntry("Literal"),
    ts2mlsEntry("Namespace", expectError = true),
    ts2mlsEntry("Optional", ignoreTypeError = true),
    ts2mlsEntry("Overload", ignoreTypeError = true),
    ts2mlsEntry("TSArray", ignoreTypeError = true),
    ts2mlsEntry("Tuple", ignoreTypeError = true),
    ts2mlsEntry("Type", ignoreTypeError = true),
    ts2mlsEntry("TypeParameter", ignoreTypeError = true),
    ts2mlsEntry("Union"),
    ts2mlsEntry("Variables", expectError = true),
  )

  private val cp = g.require("child_process")
  private val fs = g.require("fs")
}
