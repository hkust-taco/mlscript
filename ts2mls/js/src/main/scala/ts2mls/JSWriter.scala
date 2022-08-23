package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._

class JSWriter(filename: String) {
  import JSWriter.fs
  private val out = fs.openSync(filename, "w+")

  def writeln(str: String): Unit = fs.writeSync(out, s"$str\n")
  def close(): Unit = fs.closeSync(out)
}

object JSWriter {
  private val fs = g.require("fs") // must use fs module to manipulate files in JS

  def apply(filename: String) = new JSWriter(filename)
}