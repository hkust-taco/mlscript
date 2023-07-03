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
  commonJS: Boolean, // generate common js or es5
  expectTypeError: Boolean, // ignore type errors for test
  expectError: Boolean, // the test should raise errors
  force: Boolean // force to recompile if it is true
)
