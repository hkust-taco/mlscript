package hkmc2.io

import mlscript.utils._, shorthands._
import collection.mutable.Map as MutMap

/**
 * In-memory file system for testing and web compiler. Stores files as a map
 * from path strings to content strings. Note that separators are not normalized.
 */
class InMemoryFileSystem(initialFiles: Map[String, String]) extends FileSystem:
  private val files: MutMap[String, String] = MutMap.from(initialFiles)
  
  def read(path: Path): String =
    files.getOrElse(path.toString, throw new FileSystem.FileNotFoundException(path))
  
  def write(path: Path, content: String): Unit =
    files(path.toString) = content
  
  def exists(path: Path): Bool = files.contains(path.toString)
  
  /** Add a file to the virtual file system (for testing) */
  def addFile(path: String, content: String): Unit =
    files(path) = content
  
  /** Get all files (for debugging) */
  def allFiles: Map[String, String] = files.toMap
