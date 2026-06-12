package hkmc2
package io

import hkmc2.utils.*, shorthands.*

/**
 * JVM implementation of [[Path]] that wraps [[os.Path]].
 */
private[io] case class WrappedPath(private[io] val underlying: os.Path) extends Path:
  override def toString: String = underlying.toString

  def last: String = underlying.last

  def baseName: String = underlying.baseName

  def ext: String = underlying.ext

  def up: Path = new WrappedPath(underlying / os.up)

  def /(relPath: RelPath): Path =
    new WrappedPath(underlying / relPath.asInstanceOf[WrappedRelPath].underlying)
  
  def /(fragment: Str): Path =
    new WrappedPath(underlying / fragment)

  def relativeTo(base: Path): Opt[RelPath] =
    try S(new WrappedRelPath(underlying.relativeTo(base.asInstanceOf[WrappedPath].underlying)))
    catch case _: Exception => N

  def segments: Ls[String] = underlying.segments.toList

  def isAbsolute: Bool = underlying.startsWith(os.root)

/**
 * JVM implementation of [[RelPath]] that wraps [[os.RelPath]].
 */
private[io] class WrappedRelPath(private[io] val underlying: os.RelPath) extends RelPath:
  override def toString: String = underlying.toString

  def segments: Ls[String] = underlying.segments.toList

  def /(other: RelPath): RelPath =
    new WrappedRelPath(underlying / other.asInstanceOf[WrappedRelPath].underlying)

/**
 * Platform-specific factory for creating Path instances
 */
private[io] object PathFactory:
  def fromString(str: String) = new WrappedPath(os.Path(str))
  def separator: String = "/"
  def relPathFromString(str: String) = new WrappedRelPath(os.RelPath(str))
  def relPathUp = new WrappedRelPath(os.up)

/**
 * JVM-specific utilities for Path conversion
 */
object PlatformPath:
  /** Convert os.Path to io.Path */
  def fromOsPath(osPath: os.Path): Path = new WrappedPath(osPath)

  /** Convert os.RelPath to io.RelPath */
  def fromOsRelPath(osRelPath: os.RelPath): RelPath = new WrappedRelPath(osRelPath)

  /** Implicit conversion from os.Path to io.Path (import to use) */
  given Conversion[os.Path, Path] = fromOsPath

  /** Implicit conversion from os.RelPath to io.RelPath (import to use) */
  given Conversion[os.RelPath, RelPath] = fromOsRelPath
