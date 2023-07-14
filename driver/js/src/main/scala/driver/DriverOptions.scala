package driver

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

final case class DriverOptions(
  filename: String, // The entry file's name
  path: String, // Work path
  watchDir: String, // Watch mlscript files and recompile automatically
  outputDir: String, // JS output path
  tsconfig: Option[String], // TS configuration filename (if applicable)
  interfaceDir: String, // Interface file output path
  commonJS: Boolean, // Generate common js or es5
  expectTypeError: Boolean, // Type errors are expected
  expectError: Boolean, // Other errors(e.g., code generation errors) are expected
  forceIfNoChange: Boolean // If it is true, recompile everything when there is no change
)

object DriverResult extends Enumeration {
  type DriverResult = Value
  val OK, Error, TypeError, ExpectError, ExpectTypeError = Value
}
