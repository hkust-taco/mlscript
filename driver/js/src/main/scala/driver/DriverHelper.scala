package driver

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._
import scala.scalajs.js.annotation._
import mlscript.utils._

@JSExportTopLevel("MLscriptDriver")
object DriverHelper {
  private val fs = g.require("fs")

  @JSExport
  def watch(
    filename: String,
    workDir: String,
    outputDir: String,
    tsconfig: Option[String],
    commonJS: Boolean,
    expectTypeError: Boolean
  ): Unit = {
    val options = DriverOptions(filename, workDir, outputDir, tsconfig, ".interfaces", commonJS, expectTypeError, false, false)
    fs.watch(workDir, (event: js.Dynamic) => {
      if (event.toString() === "change") {
        val res = Driver(options).execute

        import DriverResult._
        res match {
          case Error => System.err.println(s"Compiling error(s) found in $filename.")
          case TypeError => System.err.println(s"Type error(s) found in $filename")
          case ExpectError => System.err.println(s"Expect compiling error(s) in $filename")
          case ExpectTypeError => System.err.println(s"Expect type error(s) in $filename")
          case OK => ()
        }
      }
    })
  }
}
