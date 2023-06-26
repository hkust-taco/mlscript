package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

object TSPathResolver {
  private val np: js.Dynamic = g.require("path") // built-in node module

  def resolve(path: String): String = np.resolve(path).toString()
  def dirname(filename: String): String = np.dirname(filename).toString()
  def isLocal(path: String): Boolean =
    path.startsWith("./") || path.startsWith("/") || path.startsWith("../")
  def isMLScirpt(path: String): Boolean =
    path.endsWith(".mls") || path.endsWith(".mlsi")
  def normalize(path: String): String = np.normalize(path).toString()

  def relative(from: String, to: String) = np.relative(from, to).toString()
  def extname(path: String) =
    if (path.endsWith(".d.ts")) ".d.ts"
    else np.extname(path).toString()
  def basename(filename: String) =
    np.basename(filename, extname(filename)).toString()
  def basenameWithExt(filename: String) = np.basename(filename).toString()
}
