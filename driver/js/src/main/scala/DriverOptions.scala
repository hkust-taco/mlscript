import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

final case class DriverOptions(
  val filename: String,
  val outputDir: String = ".",
  val force: Boolean = false // force to recompile if it is true
) // TODO: add more options

object DriverOptions {
  def parse: Option[DriverOptions] = {
    val process = g.require("process") // TODO: better parse
    val args = process.argv
    if (args.length > 4) Some(DriverOptions(args.selectDynamic("2").toString, args.selectDynamic("3").toString, true))
    else if (args.length > 3) Some(DriverOptions(args.selectDynamic("2").toString, args.selectDynamic("3").toString))
    else if (args.length > 2) Some(DriverOptions(args.selectDynamic("2").toString))
    else None
  }
}
