package hkmc2.io

import scala.scalajs.js
import hkmc2.utils.*, shorthands.*
import VirtualPath.sep

/**
 * Pure JavaScript implementation of Path without using Node.js path module
 */
private[io] case class VirtualPath(val pathString: String) extends Path:
  private def normalizePath(path: String): String =
    if path.isEmpty then path
    else
      // Split by separator and filter out empty segments
      val segments = path.split(sep).filter(_.nonEmpty)
      val isAbs = path.startsWith(sep)

      // Resolve . and .. segments
      val normalized = segments.foldLeft(List.empty[String]): (acc, seg) =>
        seg match
          case "." => acc  // Current directory, skip it
          case ".." =>
            // Parent directory, pop the last segment if possible
            if acc.isEmpty || acc.last == ".." then acc :+ seg
            else acc.dropRight(1)
          case _ => acc :+ seg
      
      if isAbs then sep + normalized.mkString(sep)
      else if normalized.isEmpty then "."
      else normalized.mkString(sep)
  
  override def toString: String = pathString
  
  def last: String =
    val idx = pathString.lastIndexOf(sep)
    if idx < 0 then pathString
    else pathString.substring(idx + 1)
  
  def baseName: String =
    val filename = last
    val dotIdx = filename.lastIndexOf('.')
    if dotIdx <= 0 then filename  // .hidden files or no extension
    else filename.substring(0, dotIdx)
  
  def ext: String =
    val filename = last
    val dotIdx = filename.lastIndexOf('.')
    if dotIdx <= 0 then ""  // .hidden files or no extension
    else filename.substring(dotIdx + 1)
  
  def up: Path =
    val idx = pathString.lastIndexOf(sep)
    if idx < 0 then new VirtualPath(".")
    else if idx == 0 then new VirtualPath(sep)  // root case
    else new VirtualPath(pathString.substring(0, idx))
  
  def /(relPath: RelPath): Path =
    val combined = if pathString.endsWith(sep) then
      pathString + relPath.toString
    else
      pathString + sep + relPath.toString
    new VirtualPath(normalizePath(combined))
  
  def /(fragment: String): Path =
    val combined = if pathString.endsWith(sep) then
      pathString + fragment
    else
      pathString + sep + fragment
    new VirtualPath(normalizePath(combined))
  
  def relativeTo(base: Path): Opt[RelPath] =
    try
      val baseSegs = base.segments
      val targetSegs = segments
      
      // Find common prefix
      var i = 0
      while i < baseSegs.length && i < targetSegs.length && baseSegs(i) == targetSegs(i) do
        i += 1
      
      // Build relative path
      val upCount = baseSegs.length - i
      val ups = List.fill(upCount)("..")
      val downs = targetSegs.drop(i)
      
      val relSegs = ups ++ downs
      if relSegs.isEmpty then S(new VirtualRelPath("."))
      else S(new VirtualRelPath(relSegs.mkString(sep)))
    catch case _: Exception => N
  
  def segments: Ls[String] =
    pathString.split(sep).toList.filter(_.nonEmpty)
  
  def isAbsolute: Bool = pathString.startsWith(sep)

private[io] object VirtualPath:
  val sep = "/"

/**
 * Pure JavaScript implementation of RelPath without using Node.js path module
 */
private[io] class VirtualRelPath(val pathString: String) extends RelPath:
  override def toString: String = pathString
  
  def segments: Ls[String] =
    pathString.split(sep).toList.filter(_.nonEmpty)
  
  def /(other: RelPath): RelPath =
    val combined = if pathString.endsWith(sep) then
      pathString + other.toString
    else
      pathString + sep + other.toString
    new VirtualRelPath(combined)
