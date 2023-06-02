package driver

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

final case class DriverOptions(
  filename: String,
  path: String,
  outputDir: String,
  tsconfig: Option[String],
  interfaceDir: String,
  force: Boolean // force to recompile if it is true
)
