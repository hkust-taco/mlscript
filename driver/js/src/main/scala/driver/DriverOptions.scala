package driver

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

final case class DriverOptions(
  val filename: String,
  val path: String,
  val outputDir: String = ".",
  val force: Boolean = false // force to recompile if it is true
) // TODO: add more options

object DriverOptions {
  def parse: Option[DriverOptions] = {
    val process = g.require("process") // TODO: better parse
    val args = process.argv
    if (args.length > 4) {
      val filename = args.selectDynamic("2").toString
      Some(DriverOptions(filename, filename.substring(0, filename.lastIndexOf("/") + 1), args.selectDynamic("3").toString, true))
    }
    else if (args.length > 3) {
      val filename = args.selectDynamic("2").toString
      Some(DriverOptions(filename, filename.substring(0, filename.lastIndexOf("/") + 1), args.selectDynamic("3").toString))
    }
    else if (args.length > 2) {
      val filename = args.selectDynamic("2").toString
      Some(DriverOptions(filename, filename.substring(0, filename.lastIndexOf("/") + 1)))
    }
    else None
  }
}
