package mlscript

import mlscript.utils._, shorthands._
import os.FilePath
import os.Path
import scala.collection.Iterator

abstract class GitHelper[PathType, RelPathType](rootDir: PathType, workDir: PathType) {
  protected def diff: Iterator[Str]
  protected def str2RelPath(s: Str): RelPathType
  protected def filter(file: PathType): Bool

  // Aggregate unstaged modified files to only run the tests on them, if there are any
  final protected lazy val modified: Set[RelPathType] = try diff.flatMap { gitStr =>
    println(" [git] " + gitStr)
    val prefix = gitStr.take(2)
    val filePath = str2RelPath(gitStr.drop(3))
    if (prefix =:= "A " || prefix =:= "M " || prefix =:= "R " || prefix =:= "D ")
      N // * Disregard modified files that are staged
    else S(filePath)
  }.toSet catch {
    case err: Throwable => System.err.println("/!\\ git command failed with: " + err)
    Set.empty
  }

  final def getFiles(allFiles: IndexedSeq[PathType]): IndexedSeq[PathType] = allFiles.filter(filter(_))
}

class JVMGitHelper(rootDir: os.Path, workDir: os.Path) extends GitHelper[os.Path, os.RelPath](rootDir, workDir) {
  override protected def str2RelPath(s: Str): os.RelPath = os.RelPath(s)
  override protected def diff: Iterator[Str] =
    os.proc("git", "status", "--porcelain", workDir).call().out.lines().iterator
  override protected def filter(file: Path): Bool = {
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
