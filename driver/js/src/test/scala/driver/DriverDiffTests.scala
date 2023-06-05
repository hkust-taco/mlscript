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
    case TestOption(filename, workDir, interfaceDir, execution, tsconfig, expectError) => test(filename) {
      val options = DriverOptions(filename, workDir, jsPath, tsconfig, interfaceDir, forceCompiling)
      val driver = Driver(options)
      driver.genPackageJson()
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
  private val forceCompiling = sys.env.get("CI").isEmpty

  private val diffPath = "driver/js/src/test/projects/"
  private val jsPath = s"${diffPath}js/"
  private val outputPath = s"${diffPath}../output/"
  private val ts2mlsPath = "ts2mls/js/src/test/diff"

  private case class TestOption(
    filename: String,
    workDir: String,
    interfaceDir: String,
    execution: Option[(String, String)],
    tsconfig: Option[String],
    expectError: Boolean
  )

  private def entry(entryModule: String, tsconfig: Option[String] = None, expectError: Boolean = false) =
    TestOption(
      s"./mlscript/${entryModule}.mls",
      diffPath,
      ".interfaces",
      Some((s"${jsPath}mlscript/${entryModule}.js", s"${outputPath}${entryModule}.check")),
      tsconfig,
      expectError
    )

  private def ts2mlsEntry(entryModule: String, expectError: Boolean = false) =
    TestOption(s"./${entryModule}.mlsi", ts2mlsPath, ".", None, None, expectError)

  private val testCases = List[TestOption](
    entry("Simple"),
    entry("Cycle2"),
    entry("Self", expectError = true),
    entry("C", expectError = true),
    entry("TS", Some("./tsconfig.json"), true), // TODO: type members
    entry("Output", Some("./tsconfig.json")),
    entry("Output2", Some("./tsconfig.json"), true), // TODO
    ts2mlsEntry("Array"),
    ts2mlsEntry("BasicFunctions"),
    ts2mlsEntry("ClassMember"),
    ts2mlsEntry("Cycle1", true), // TODO: ???
    ts2mlsEntry("Dec"),
    ts2mlsEntry("Enum"),
    ts2mlsEntry("ES5"),
    ts2mlsEntry("Export"),
    ts2mlsEntry("Heritage"),
    ts2mlsEntry("HighOrderFunc"),
    ts2mlsEntry("Import"),
    ts2mlsEntry("InterfaceMember"),
    ts2mlsEntry("Intersection"),
    ts2mlsEntry("Literal"),
    ts2mlsEntry("Namespace"),
    ts2mlsEntry("Optional"),
    ts2mlsEntry("Overload"),
    ts2mlsEntry("Tuple"),
    ts2mlsEntry("Type"),
    ts2mlsEntry("TypeParameter"),
    ts2mlsEntry("Union"),
    ts2mlsEntry("Variables"),
  )

  private val cp = g.require("child_process")
  private val fs = g.require("fs")
}
