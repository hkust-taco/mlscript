package ts2mls

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import js.JSConverters._

class TSModuleResolver(workDir: String) {
  import TSModuleResolver.{resolve, relative, parseName, extname}

  private val absWorkDir = resolve(workDir)

  def getAbsolutePath(path: String): String =
    if (path.startsWith("./") || path.startsWith("/") || path.startsWith("../"))
      resolve(path)
    else
      TypeScript.resolveNodeModulePath(path)
  
  def getRelatedPath(path: String): String =
    relative(absWorkDir, resolve(path))

  def getModuleName(filename: String): String =
    parseName(filename)

  def getExtName(filename: String): String =
    extname(filename)
}

object TSModuleResolver {
  private val np: js.Dynamic = g.require("path") // built-in node module

  def apply(path: String) = new TSModuleResolver(path)

  def resolve(path: String): String = np.resolve(path).toString()

  private def relative(from: String, to: String) = np.relative(from, to).toString()
  private def parseName(filename: String) = np.parse(filename).name.toString()
  private def extname(path: String) = np.extname(path).toString()
}
