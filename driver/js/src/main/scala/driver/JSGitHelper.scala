package driver

import mlscript.utils.GitHelper
import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import ts2mls.TSPathResolver

class JSGitHelper(rootDir: String, workDir: String) extends GitHelper[String, String](rootDir, workDir) {
  override protected def str2RelPath(s: String): String = s
  override protected def diff: Iterator[String] = {
    val res = JSGitHelper.cp.execSync(s"git status --porcelain $workDir").toString()
    if (res.isEmpty()) Iterator()
    else res.split("\n").iterator
  }

  override protected def filter(file: String): Boolean =
    modified(TSPathResolver.normalize(file)) || modified.isEmpty
}

object JSGitHelper {
  def apply(rootDir: String, workDir: String): JSGitHelper =
    new JSGitHelper(rootDir, workDir)

  private val cp = g.require("child_process")
}
