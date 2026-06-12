package hkmc2
package io

import hkmc2.utils.*, shorthands.*

/**
 * Cross-platform path abstraction.
 * Represents a file system path without performing any I/O.
 */
abstract class Path:
  /** Convert to platform-specific string representation */
  def toString: String
  
  /** Get the last segment of the path (file or directory name) */
  def last: String
  
  /** Get the base name without extension */
  def baseName: String
  
  /** Get the file extension (without dot) */
  def ext: String
  
  /** Navigate to parent directory */
  def up: Path
  
  /** Join with a relative path */
  def /(relPath: RelPath): Path
  
  /** Join with a single path fragment */
  def /(fragment: Str): Path
  
  /** Calculate relative path from this to target */
  def relativeTo(base: Path): Opt[RelPath]
  
  /** Get segments as a list */
  def segments: Ls[String]
  
  /** Check if this is an absolute path */
  def isAbsolute: Bool

object Path:
  /** Create path from string - delegates to platform-specific implementation */
  def apply(str: String): Path = PathFactory.fromString(str)
  
  /** Platform-specific path separator */
  def separator: String = PathFactory.separator

/**
 * Represents a relative path
 */
abstract class RelPath:
  def toString: String
  def segments: Ls[String]
  def /(other: RelPath): RelPath

object RelPath:
  /** Create relative path from string - delegates to platform-specific implementation */
  def apply(str: String): RelPath = PathFactory.relPathFromString(str)
  
  /** Represents parent directory (..) */
  val up: RelPath = PathFactory.relPathUp
