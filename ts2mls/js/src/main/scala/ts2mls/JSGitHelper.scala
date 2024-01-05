package ts2mls

import mlscript.utils.GitHelper
import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._

class JSGitHelper(rootDir: String, workDir: String, val forceIfNoChange: Boolean) extends GitHelper[String, String](rootDir, workDir) {
  override protected def str2RelPath(s: String): String = s
  override protected def diff: Iterator[String] = {
    val res = JSGitHelper.cp.execSync(s"git status --porcelain $workDir").toString()
    if (res.isEmpty()) Iterator()
    else res.split("\n").iterator
  }

  override def filter(file: String): Boolean =
    modified(TSPathResolver.normalize(file)) || (forceIfNoChange && modified.isEmpty)
}

object JSGitHelper {
  def apply(rootDir: String, workDir: String, forceIfNoChange: Boolean): JSGitHelper =
    new JSGitHelper(rootDir, workDir, forceIfNoChange)

  private val cp = g.require("child_process")
}
