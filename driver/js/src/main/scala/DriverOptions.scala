import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

final case class DriverOptions(
  val filename: String,
  val outputDir: String = "."
) // TODO: add more options

object DriverOptions {
  def parse: Option[DriverOptions] = {
    val process = g.require("process")
    val args = process.argv
    if (args.length > 3) Some(DriverOptions(args.selectDynamic("2").toString, args.selectDynamic("3").toString))
    else if (args.length > 2) Some(DriverOptions(args.selectDynamic("2").toString))
    else None
  }
}
