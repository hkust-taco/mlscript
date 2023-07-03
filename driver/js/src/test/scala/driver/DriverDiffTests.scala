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
    case TestOption(filename, workDir, outputDir, interfaceDir, cjs, execution, tsconfig, expectTypeError, expectError) => test(filename) {
      val options =
        DriverOptions(filename, workDir, outputDir, tsconfig, interfaceDir, cjs, expectTypeError, expectError, forceCompiling)
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
  private val forceCompiling = true // TODO: check based on git

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
    expectTypeError: Boolean,
    expectError: Boolean
  )

  private def driverEntry(
    entryModule: String,
    tsconfig: Option[String],
    workDir: String,
    jsPath: String,
    expectTypeError: Boolean,
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
      expectTypeError,
      expectError
    )

  private def cjsEntry(
    entryModule: String,
    tsconfig: Option[String] = None,
    expectTypeError: Boolean = false,
    expectError: Boolean = false
  ) = driverEntry(entryModule, tsconfig, s"${diffPath}cjsprojects/",
    s"${diffPath}cjsprojects/js/", expectTypeError, expectError, true)

  private def esEntry(
    entryModule: String,
    tsconfig: Option[String] = None,
    expectTypeError: Boolean = false,
    expectError: Boolean = false
  ) = driverEntry(entryModule, tsconfig, s"${diffPath}esprojects/",
    s"${diffPath}esprojects/js/", expectTypeError, expectError, false)

  private def ts2mlsEntry(entryFile: String, expectTypeError: Boolean = false, expectError: Boolean = false) =
    TestOption(s"./${entryFile}", "ts2mls/js/src/test/typescript", "", "../diff", false, None, None, expectTypeError, expectError)

  private val testCases = List[TestOption](
    esEntry("Simple"),
    esEntry("Cycle2"),
    esEntry("Self", expectError = true),
    esEntry("C", expectError = true),
    esEntry("TS", Some("./tsconfig.json"), expectTypeError = true), // TODO: type members
    esEntry("Output", Some("./tsconfig.json"), expectTypeError = true), // TODO: type parameter position
    esEntry("Output2", Some("./tsconfig.json"), expectTypeError = true), // TODO: type parameter position
    esEntry("MLS2TheMax", Some("./tsconfig.json")),
    esEntry("MyPartialOrder", Some("./tsconfig.json"), expectError = true), // TODO: type traits in modules
    cjsEntry("Lodash", Some("./tsconfig.json"), expectTypeError = true), // TODO: module member selection/trait types
    esEntry("Builtin"),
    cjsEntry("CJS1"),
    ts2mlsEntry("BasicFunctions.ts", expectTypeError = true),
    ts2mlsEntry("ClassMember.ts"),
    ts2mlsEntry("Cycle1.ts", expectTypeError = true),
    ts2mlsEntry("Dec.d.ts"),
    ts2mlsEntry("Enum.ts"),
    ts2mlsEntry("Escape.ts"),
    ts2mlsEntry("Export.ts", expectTypeError = true),
    ts2mlsEntry("Heritage.ts", expectTypeError = true),
    ts2mlsEntry("HighOrderFunc.ts"),
    ts2mlsEntry("Import.ts"),
    ts2mlsEntry("InterfaceMember.ts"),
    ts2mlsEntry("Intersection.ts", expectTypeError = true),
    ts2mlsEntry("Literal.ts"),
    ts2mlsEntry("Namespace.ts", expectError = true),
    ts2mlsEntry("Optional.ts", expectTypeError = true),
    ts2mlsEntry("Overload.ts", expectTypeError = true),
    ts2mlsEntry("TSArray.ts", expectTypeError = true),
    ts2mlsEntry("Tuple.ts", expectTypeError = true),
    ts2mlsEntry("Type.ts", expectTypeError = true),
    ts2mlsEntry("TypeParameter.ts", expectTypeError = true),
    ts2mlsEntry("Union.ts"),
    ts2mlsEntry("Variables.ts", expectError = true),
  )

  private val cp = g.require("child_process")
  private val fs = g.require("fs")
}
