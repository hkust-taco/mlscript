package hkmc2.io

import mlscript.utils._, shorthands._
import collection.mutable.Map as MutMap
import scala.scalajs.js, js.annotation.JSExport, js.JSConverters.*

/**
 * In-memory file system for testing and web compiler. Stores files as a map
 * from path strings to content strings. Note that separators are not normalized.
 */
class InMemoryFileSystem(initialFiles: Map[String, String]) extends FileSystem:
  private val files: MutMap[String, String] = MutMap.from(initialFiles)
  
  def read(path: Path): String =
    files.getOrElse(path.toString, throw new FileSystem.FileNotFoundException(path))
  
  def write(path: Path, content: String): Unit =
    print(s"Writing to $path")
    files(path.toString) = content
  
  def exists(path: Path): Bool = files.contains(path.toString)
  
  @JSExport("write")
  def write(path: Str, content: Str): Unit =
    print(s"I'm writing to $path")
    files(path) = content
  
  @JSExport("read")
  def read(path: Str): Str =
    files.getOrElse(path, throw new FileSystem.FileNotFoundException(Path(path)))
  
  @JSExport("list")
  def list: js.Array[Str] = allFiles.keys.toJSArray
  
  /** Get all files (for debugging) */
  def allFiles: Map[String, String] = files.toMap
