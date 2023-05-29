package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

object TSModuleResolver {
  private val np: js.Dynamic = g.require("path") // built-in node module

  def resolve(path: String): String = np.resolve(path).toString()
  def dirname(filename: String): String = np.dirname(filename).toString()
  def isLocal(path: String): Boolean =
    path.startsWith("./") || path.startsWith("/") || path.startsWith("../")
  def normalize(path: String): String = np.normalize(path).toString()

  def relative(from: String, to: String) = np.relative(from, to).toString()
  def extname(path: String) = np.extname(path).toString()
  def basename(filename: String) =
    if (filename.contains(".d.ts")) np.basename(filename, ".d.ts").toString()
    else np.basename(filename, extname(filename)).toString()
}
