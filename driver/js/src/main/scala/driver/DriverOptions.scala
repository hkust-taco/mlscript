package driver

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

final case class DriverOptions(
  val filename: String,
  val path: String,
  val outputDir: String,
  val force: Boolean // force to recompile if it is true
)
