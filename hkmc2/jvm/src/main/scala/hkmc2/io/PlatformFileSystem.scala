package hkmc2
package io

import hkmc2.utils.*, shorthands.*

private[io] class JavaFileSystem extends FileSystem:
  def read(path: Path): String = os.read(unwrap(path))

  def write(path: Path, content: String): Unit = os.write.over(unwrap(path), content)

  def exists(path: Path): Bool = os.exists(unwrap(path))
  
  def getLastChangedTimestamp(path: Path): Long = os.mtime(unwrap(path))
  
  private def unwrap(path: Path): os.Path = path match
    case path: WrappedPath => path.underlying
    case _ => lastWords(s"The given path is not compatible with the current platform (JVM).")

object PlatformFileSystem:
  val default: FileSystem = new JavaFileSystem
