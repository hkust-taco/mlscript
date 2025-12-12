package hkmc2.io

import mlscript.utils._, shorthands._
import collection.mutable.Map as MutMap
import scala.scalajs.js, js.annotation.JSExport, js.JSConverters.*
import scala.scalajs.js.annotation.JSExportTopLevel

/**
 * In-memory file system for testing and web compiler. Stores files as a map
 * from path strings to content strings. Note that separators are not normalized.
 */
class InMemoryFileSystem(initialFiles: Map[String, String]) extends FileSystem:
  // We assume that all paths are normalized here.
  private val files: MutMap[String, String] = MutMap.from(initialFiles)
  
  def read(path: Path): String = read(path.toString)
  
  def write(path: Path, content: String): Unit =
    write(path.toString, content)
  
  def exists(path: Path): Bool = files.contains(path.toString)
  
  @JSExport("write")
  def write(path: Str, content: Str): Unit =
    files(path) = content
  
  @JSExport("read")
  def read(path: Str): Str =
    files.getOrElse(path, throw new FileSystem.FileNotFoundException(Path(path)))
  
  @JSExport("list")
  def list: js.Array[Str] = allFiles.keys.toJSArray
  
  /** Get all files (for debugging) */
  def allFiles: Map[String, String] = files.toMap

object InMemoryFileSystem:
  /** Create an empty in-memory file system. */
  @JSExportTopLevel("InMemoryFileSystem")
  def apply(files: js.Array[js.Tuple2[Str, Str]]): InMemoryFileSystem =
    new InMemoryFileSystem(files.map(t => t._1 -> t._2).toMap)
