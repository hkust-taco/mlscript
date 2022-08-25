package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._

class JSWriter(filename: String) {
  import JSWriter.{fs, createBuffer}
  private val out = fs.openSync(filename, "rs+")
  private var fileSize = 0
  private var needTruncate = false

  def writeln(str: String): Unit = {
    val strln = s"$str\n"
    val buffer = createBuffer(strln.length)
    val len = fs.readSync(out, buffer, 0, strln.length).asInstanceOf[Int]
    
    if (!strln.equals(buffer.toString())) {
      fs.writeSync(out, strln, fileSize).asInstanceOf[Int]
      needTruncate = true
    }

    fileSize += strln.length
  }

  def close(): Unit = {
    if (needTruncate) fs.truncateSync(out, fileSize) // remove other content to keep the file from chaos

    fs.closeSync(out)
  }
}

object JSWriter {
  private val fs = g.require("fs") // must use fs module to manipulate files in JS

  def apply(filename: String) = new JSWriter(filename)

  private def createBuffer(length: Int) = g.Buffer.alloc(length)
}