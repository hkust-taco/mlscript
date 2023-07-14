package mlscript.utils

import shorthands._
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
