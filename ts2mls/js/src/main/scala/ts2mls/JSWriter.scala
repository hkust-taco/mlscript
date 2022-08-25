package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._

class JSWriter(filename: String) {
  import JSWriter.{fs, createBuffer}
  private val out = fs.openSync(filename, "w+")

  def writeln(str: String): Unit = {
    val strln = s"$str\n"
    val buffer = createBuffer(strln.length)
    fs.readSync(out, buffer, 0, strln.length)
    if (!strln.equals(buffer.toString()))
      fs.writeSync(out, strln, -strln.length)
  }

  def close(): Unit = fs.closeSync(out)
}

object JSWriter {
  private val fs = g.require("fs") // must use fs module to manipulate files in JS
  // private val buffer = g.require("buffer")

  def apply(filename: String) = new JSWriter(filename)

  private def createBuffer(length: Int) = g.Buffer.alloc(length)
}