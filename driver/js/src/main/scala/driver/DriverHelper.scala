package driver

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._
import scala.scalajs.js.annotation._
import mlscript.utils._
import ts2mls.TypeScript

object DriverHelper {
  // Do not use fs.watch
  // See https://github.com/paulmillr/chokidar
  private val watcher = TypeScript.load("chokidar")

  private def run(
    filename: String,
    workDir: String,
    outputDir: String,
    tsconfig: Option[String],
    commonJS: Boolean,
    expectTypeError: Boolean
  ): Unit = {
    System.out.println(s"start watching $workDir")
    val options = DriverOptions(filename, workDir, s"${g.__dirname}/predefs/", outputDir, tsconfig, ".interfaces", commonJS, expectTypeError, false, false)
    watcher.watch(workDir,
      js.Dictionary("ignoreInitial" -> true, "ignored" -> "(.*\\.mlsi) | (.*\\.js)")
    ).on("all", (event: js.Dynamic, file: js.Dynamic) => {
      if (event.toString() === "change" || event.toString() === "add") {
        val driver = Driver(options)
        driver.genPackageJson()
        val res = driver.execute

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

  @JSExportTopLevel("watch")
  def watch(
    filename: String,
    workDir: String,
    outputDir: String,
    tsconfig: String,
    commonJS: Boolean,
    expectTypeError: Boolean
  ): Unit = run(filename, workDir, outputDir, Some(tsconfig), commonJS, expectTypeError)

  @JSExportTopLevel("watch")
  def watch(
    filename: String,
    workDir: String,
    outputDir: String,
    commonJS: Boolean,
    expectTypeError: Boolean
  ): Unit = run(filename, workDir, outputDir, None, commonJS, expectTypeError)
}
