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
  commonJS: Boolean, // Generate common js or es5
  expectTypeError: Boolean, // Type errors are expected
  expectError: Boolean, // Other errors(e.g., code generation errors) are expected
)

object DriverResult extends Enumeration {
  type DriverResult = Value
  val OK, Error, TypeError, ExpectError, ExpectTypeError = Value
}
