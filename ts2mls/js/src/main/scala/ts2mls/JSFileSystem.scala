package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._
import ts2mls.TSPathResolver

object JSFileSystem {
  private val fs = g.require("fs") // must use fs module to manipulate files in JS

  def exists(filename: String): Boolean = fs.existsSync(filename)

  def readFile(filename: String): Option[String] =
    if (!exists(filename)) None
    else Some(fs.readFileSync(filename).toString)

  def writeFile(filename: String, content: String): Unit = {
    val dir = TSPathResolver.dirname(filename)
    if (!exists(dir)) fs.mkdirSync(dir, js.Dictionary("recursive" -> true))
    fs.writeFileSync(filename, content)
  }

  def getModificationTime(filename: String): Double =
    if (!exists(filename)) 0.0
    else {
      val state = fs.statSync(filename)
      state.mtimeMs.asInstanceOf[Double]
    }
}
