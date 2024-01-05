package ts2mls

import scala.scalajs.js
import js.DynamicImplicits._
import mlscript.utils._
import scala.collection.mutable.StringBuilder

class JSWriter(filename: String) {
  import JSFileSystem._

  private val buffer = new StringBuilder()
  private val dbg = new StringBuilder()
  private val err = new StringBuilder()

  def writeln(str: String): Unit = write(str + "\n")
  def write(str: String): Unit = buffer ++= str
  def writeErr(str: String): Unit = err ++= s"//| $str\n"
  def writeDbg(str: String): Unit = str.split("\n").foreach(s => dbg ++= s"//| $s\n")

  def close(): Boolean = {
    val str = buffer.toString() + dbg.toString() + err.toString()
    val origin = readFile(filename).getOrElse("")
    val updated = str =/= origin
    if (updated) writeFile(filename, str)
    updated
  }

  def getContent: String = buffer.toString()
}

object JSWriter {
  def apply(filename: String) = new JSWriter(filename)
}
