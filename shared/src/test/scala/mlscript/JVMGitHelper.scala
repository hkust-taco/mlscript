package mlscript

import mlscript.utils.GitHelper
import mlscript.utils._, shorthands._
import os.FilePath
import os.Path
import scala.collection.Iterator

class JVMGitHelper(rootDir: os.Path, workDir: os.Path) extends GitHelper[os.Path, os.RelPath](rootDir, workDir) {
  override protected def str2RelPath(s: Str): os.RelPath = os.RelPath(s)
  override protected def diff: Iterator[Str] =
    os.proc("git", "status", "--porcelain", workDir).call().out.lines().iterator
  override def filter(file: Path): Bool = {
    JVMGitHelper.validExt(file.ext) && filter(file.relativeTo(rootDir))
  }

  // Allow overriding which specific tests to run, sometimes easier for development:
  private val focused = Set[Str](
    // "LetRec"
    // "Ascribe",
    // "Repro",
    // "RecursiveTypes",
    // "Simple",
    // "Inherit",
    // "Basics",
    // "Paper",
    // "Negations",
    // "RecFuns",
    // "With",
    // "Annoying",
    // "Tony",
    // "Lists",
    // "Traits",
    // "BadTraits",
    // "TraitMatching",
    // "Subsume",
    // "Methods",
  ).map(os.RelPath(_))
  def filter(file: os.RelPath): Bool = {
    if (focused.nonEmpty) focused(file) else modified(file) || modified.isEmpty &&
      true
  }
}

object JVMGitHelper {
  def apply(rootDir: os.Path, workDir: os.Path): JVMGitHelper =
    new JVMGitHelper(rootDir, workDir)

  private val validExt = Set("fun", "mls")
}
