package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import mlscript.utils._

class JSWriter(filename: String) {
  import JSWriter._
  // the mode `rs+` would fail when the file does not exist, so it can not be used to generate new files or tests
  // the mode `w+` would lead to modification of test files even though nothing has benn changed, thus the diffTests would failed too
  private val out =
    if (fs.existsSync(filename)) fs.openSync(filename, "rs+") else fs.openSync(filename, "w+")
  private var fileSize = 0 // how many bytes we've written in the file
  private var needTruncate = false

  writeln(":NewParser\n:ParseOnly")

  def writeln(str: String) = {
    val strln = str + "\n"
    val buffer = createBuffer(strln.length)
    fs.readSync(out, buffer, 0, strln.length)
    
    // override when the content is different
    if (strln =/= buffer.toString()) {
      fs.writeSync(out, strln, fileSize) // `fileSize` is the offset from the beginning of the file
      needTruncate = true // if the file has been modified, we need to truncate the file to keep it clean
    }

    fileSize += strln.length
  }

  def close() = {
    if (needTruncate) fs.truncateSync(out, fileSize) // remove other content to keep the file from chaos

    fs.closeSync(out)
  }
}

object JSWriter {
  private val fs = g.require("fs") // must use fs module to manipulate files in JS

  def apply(filename: String) = new JSWriter(filename)

  private def createBuffer(length: Int) = g.Buffer.alloc(length)
}
