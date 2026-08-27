package hkmc2.io

import scala.scalajs.js
import hkmc2.utils.*, shorthands.*
import VirtualPath.sep

/**
 * Pure JavaScript implementation of Path without using Node.js path module.
 *
 * Paths are normalized on construction, and compared by their normalized form.
 * This is not merely cosmetic: paths are used as keys, both of the compilation-unit cache in
 * `CompilerCtx` and of the file system (`InMemoryFileSystem`, which documents that it assumes
 * normalized paths). Two spellings of the same file must therefore be the same value, or the
 * same source file gets two cached elaborations — and so two distinct sets of symbols — while
 * reads through the non-canonical spelling fail to find the file at all.
 * The JVM implementation gets this from `os.Path`, which is normalized by construction.
 */
private[io] final class VirtualPath(rawPathString: String) extends Path:
  
  val pathString: String = VirtualPath.normalize(rawPathString)
  
  override def equals(that: Any): Bool = that match
    case that: VirtualPath => pathString == that.pathString
    case _ => false
  
  override def hashCode: Int = pathString.hashCode
  
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
    // * The constructor normalizes, so the naive concatenation is enough here.
    new VirtualPath(pathString + sep + relPath.toString)
  
  def /(fragment: String): Path =
    new VirtualPath(pathString + sep + fragment)
  
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
  
  /** Remove `.` segments and redundant separators, and resolve `..` where a segment precedes it.
    * Leading `..` in a relative path cannot be resolved without knowing the current directory,
    * so they are kept as-is. Idempotent. */
  def normalize(path: String): String =
    if path.isEmpty then path
    else
      // Split by separator and filter out empty segments
      val segments = path.split(sep).filter(_.nonEmpty)
      val isAbs = path.startsWith(sep)
      
      // Resolve . and .. segments
      val normalizedRev = segments.foldLeft(List.empty[String]): (acc, seg) =>
        seg match
          case "." => acc  // Current directory, skip it
          case ".." =>
            // Parent directory, pop the last segment if possible
            // (`acc` is in reverse order, so the last segment added is its head)
            acc match
              case Nil =>
                // Absolute paths cannot escape above their root. Keeping the `..` would make
                // `/../a` a different cache key from the same POSIX location spelled `/a`.
                if isAbs then acc else seg :: Nil
              case ".." :: _ => seg :: acc
              case _ :: tl => tl
          case _ => seg :: acc
      
      val normalized = normalizedRev.reverse
      
      if isAbs then sep + normalized.mkString(sep)
      else if normalized.isEmpty then "."
      else normalized.mkString(sep)

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
