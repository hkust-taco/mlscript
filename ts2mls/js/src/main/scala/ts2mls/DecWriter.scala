package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._

class DecWriter(filename: String) {
  private val out = DecWriter.fs.openSync(filename, "w+")

  def generate(str: String): Unit = DecWriter.fs.writeSync(out, s"$str\n")

  def close(): Unit = DecWriter.fs.closeSync(out)
}

object DecWriter {
  private val fs = g.require("fs")

  def apply(filename: String) = new DecWriter(filename)
}