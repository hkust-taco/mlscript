package hkmc2.io

import hkmc2.utils.*, shorthands.*
import collection.mutable.Map as MutMap
import scala.scalajs.js, js.annotation.JSExport, js.JSConverters.*
import scala.scalajs.js.annotation.JSExportTopLevel

/**
 * In-memory file system for testing and web compiler. Stores files as a map
 * from normalized path strings to content strings.
 */
class InMemoryFileSystem(initialFiles: Map[String, String]) extends FileSystem:
  private val files: MutMap[String, (Int, String)] = MutMap.from:
    initialFiles.map { case (k, v) => (Path(k).toString, (0, v)) }
  
  def read(path: Path): String = read(path.toString)
  
  def write(path: Path, content: String): Unit =
    write(path.toString, content)
  
  def exists(path: Path): Bool = files.contains(path.toString)
  
  def getLastChangedTimestamp(path: Path): Long =
    files.get(path.toString) match
      case Some((ts, _)) => ts.toLong
      case None => throw new FileSystem.FileNotFoundException(path)
  
  @JSExport("write")
  def write(path: Str, content: Str): Unit =
    files.updateWith(Path(path).toString):
      case Some((ts, _)) => Some((ts + 1, content))
      case None => Some((0, content))
  
  @JSExport("read")
  def read(path: Str): Str =
    val normalizedPath = Path(path)
    files.getOrElse(normalizedPath.toString,
      throw new FileSystem.FileNotFoundException(normalizedPath))._2
  
  @JSExport("list")
  def list: js.Array[Str] = allFiles.keys.toJSArray
  
  /** Get all files (for debugging) */
  def allFiles: Map[String, String] = files.view.mapValues(_._2).toMap

object InMemoryFileSystem:
  /** Create an empty in-memory file system. */
  @JSExportTopLevel("InMemoryFileSystem")
  def apply(files: js.Array[js.Tuple2[Str, Str]]): InMemoryFileSystem =
    new InMemoryFileSystem(files.map(t => t._1 -> t._2).toMap)
