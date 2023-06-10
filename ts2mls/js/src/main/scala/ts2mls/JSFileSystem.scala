package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

object JSFileSystem {
  private val fs = g.require("fs") // must use fs module to manipulate files in JS

  def exists(filename: String): Boolean = fs.existsSync(filename)

  def readFile(filename: String): Option[String] =
    if (!exists(filename)) None
    else Some(fs.readFileSync(filename).toString)

  def writeFile(filename: String, content: String): Unit = {
    val dir = TSModuleResolver.dirname(filename)
    if (!exists(dir)) fs.mkdirSync(dir, js.Dictionary("recursive" -> true))
    fs.writeFileSync(filename, content)
  }

  def getModificationTime(filename: String): String =
    if (!exists(filename)) ""
    else {
      val state = fs.statSync(filename)
      state.mtimeMs.toString
    }
}