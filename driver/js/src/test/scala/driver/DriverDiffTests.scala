package driver

import org.scalatest.funsuite.AnyFunSuite
import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import mlscript.utils._, shorthands._

class DriverDiffTests extends AnyFunSuite {
  import DriverDiffTests._
  import ts2mls.JSFileSystem._

  private def run(cases: List[TestOption], workDir: Str, outputDir: Str, interfaceDir: Str, cjs: Bool) = {
    cases.foreach {
      case TestOption(filename, execution, tsconfig, expectTypeError, expectError) => test(filename) {
        val options =
          DriverOptions(filename, workDir, "./driver/npm/lib/predefs/", outputDir, tsconfig, interfaceDir, cjs, expectTypeError, expectError, true)
        val driver = Driver(options)
        if (!outputDir.isEmpty()) driver.genPackageJson()
        val res = driver.execute

        import DriverResult._
        res match {
          case Error => fail(s"Compiling error(s) found in $filename.")
          case TypeError => fail(s"Type error(s) found in $filename")
          case ExpectError => fail(s"Expect compiling error(s) in $filename")
          case ExpectTypeError => fail(s"Expect type error(s) in $filename")
          case OK => ()
        }

        if (!expectError) execution.fold(()){
          case (executionFile, checkFile) =>
            val output = cp.execSync(s"node $outputDir/$executionFile").toString()
            val outputFile = s"$checkPath/$checkFile"
            val original = readFile(outputFile).getOrElse("")
            if (original =/= output) fs.writeFileSync(outputFile, output)
        }
      }
    }
  }

  run(ts2mlsCases, ts2mlsPath, "", "../diff", false)
  run(esCases, esPath, s"${esPath}/js/", ".interfaces", false)
  run(cjsCases, cjsPath, s"${cjsPath}/js/", ".interfaces", true)
}

object DriverDiffTests {
  private val diffPath = "driver/js/src/test/"
  private val checkPath = s"${diffPath}output/"
  private val ts2mlsPath = "ts2mls/js/src/test/typescript/"
  private val esPath = s"${diffPath}esprojects/"
  private val cjsPath = s"${diffPath}cjsprojects/"

  private case class TestOption(
    filename: String,
    execution: Option[(String, String)],
    tsconfig: Option[String],
    expectTypeError: Boolean,
    expectError: Boolean
  )

  private def driverEntry(
    entryModule: String, tsconfig: Option[String] = None, expectTypeError: Boolean = false, expectError: Boolean = false,
  ) = TestOption(s"./mlscript/${entryModule}.mls", S((s"mlscript/${entryModule}.js", s"${entryModule}.check")),
      tsconfig, expectTypeError, expectError)

  private def ts2mlsEntry(entryFile: String, expectTypeError: Boolean = false, expectError: Boolean = false) =
    TestOption(s"./${entryFile}", None, None, expectTypeError, expectError)

  private val ts2mlsCases = List(
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
    ts2mlsEntry("Namespace.ts", expectTypeError = true),
    ts2mlsEntry("Optional.ts", expectTypeError = true),
    ts2mlsEntry("Overload.ts"),
    ts2mlsEntry("TSArray.ts", expectTypeError = true),
    ts2mlsEntry("Tuple.ts", expectTypeError = true),
    ts2mlsEntry("Type.ts", expectTypeError = true),
    ts2mlsEntry("TypeParameter.ts", expectTypeError = true),
    ts2mlsEntry("Union.ts"),
    ts2mlsEntry("Variables.ts", expectTypeError = true),
  )

  private val esCases = List(
    driverEntry("Simple"),
    driverEntry("Cycle2"),
    driverEntry("Self", expectError = true),
    driverEntry("C", expectError = true, expectTypeError = true),
    driverEntry("TS", Some("./tsconfig.json"), expectTypeError = true), // TODO: type members
    driverEntry("Output", Some("./tsconfig.json"), expectTypeError = true), // TODO: type parameter position
    driverEntry("Output2", Some("./tsconfig.json"), expectTypeError = true), // TODO: type parameter position
    driverEntry("MLS2TheMax", Some("./tsconfig.json")),
    driverEntry("MyPartialOrder", Some("./tsconfig.json"), expectError = true, expectTypeError = true), // TODO: type traits in modules
    driverEntry("Builtin"),
    driverEntry("TyperDebug"),
    driverEntry("Debug1"),
    driverEntry("Child", expectTypeError = true),
    driverEntry("NewTSClass", Some("./tsconfig.json"), expectTypeError = true),
    driverEntry("Mixin1", expectTypeError = true)
  )

  private val cjsCases = List(
    driverEntry("Lodash", Some("./tsconfig.json"), expectTypeError = true), // TODO: module member selection/trait types
    driverEntry("CJS1"),
    driverEntry("Bar", Some("./tsconfig.json")),
    driverEntry("BazBaz", Some("./tsconfig.json"), expectTypeError = true),
    driverEntry("Call", Some("./tsconfig.json"), expectError = true)
  )

  private val cp = g.require("child_process")
  private val fs = g.require("fs")
}
