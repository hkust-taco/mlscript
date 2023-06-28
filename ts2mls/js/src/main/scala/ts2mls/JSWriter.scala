package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import mlscript.utils._
import scala.collection.mutable.StringBuilder

class JSWriter(filename: String) {
  import JSFileSystem._

  private val buffer = new StringBuilder()

  def writeln(str: String): Unit = write(str + "\n")
  def write(str: String): Unit = buffer ++= str

  // return true if the file has been updated
  def close(): Boolean = {
    val str = buffer.toString()
    val origin = readFile(filename).getOrElse("")
    val updated = str =/= origin
    if (updated) writeFile(filename, str)
    updated
  }
}

object JSWriter {
  def apply(filename: String) = new JSWriter(filename)
}
