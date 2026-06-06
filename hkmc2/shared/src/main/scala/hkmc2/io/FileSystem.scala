package hkmc2
package io

import hkmc2.utils.*, shorthands.*

/**
 * Abstract file system operations.
 * 
 * These are file system operations that can be directly called by the compiler.
 * More high-level file system operations, such as getting all files under a
 * folder or recursively walking through a specified path, should be handled by
 * the caller of the compiler.
 */
trait FileSystem:
  /** Read entire file as string. */
  def read(path: Path): String
  
  /** Write string to file, overwriting if exists. */
  def write(path: Path, content: String): Unit
  
  /** Check if a file exists at the given path. */
  def exists(path: Path): Bool
  
  /**
    * Get the last changed timestamp of the file at the given path. The meaning
    * of the timestamp is platform-dependent. The caller should ensure that the
    * file exists before calling this method.
    */
  def getLastChangedTimestamp(path: Path): Long
  
object FileSystem:
  /** Get the platform default file system by delegating to the platform. */
  def default: FileSystem = PlatformFileSystem.default
  
  class FileNotFoundException(path: Path) extends Exception:
    override def getMessage(): String = s"File not found: ${path.toString}"
