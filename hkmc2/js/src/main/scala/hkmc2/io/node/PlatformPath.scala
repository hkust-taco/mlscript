package hkmc2
package io
package node

import scala.scalajs.js
import scala.scalajs.js.annotation._

import mlscript.utils._, shorthands._

@js.native
trait ParsedPath extends js.Object:
  val base: String = js.native
  val name: String = js.native
  val ext: String = js.native

/**
 * Node.js path module facade
 */
@js.native
@JSImport("path", JSImport.Namespace)
object NodePath extends js.Object:
  def sep: String = js.native
  def parse(path: String): ParsedPath = js.native
  def relative(from: String, to: String): String = js.native
  def join(paths: String*): String = js.native
  def isAbsolute(path: String): Boolean = js.native
  def dirname(path: String): String = js.native

/**
 * JavaScript implementation of Path using Node.js path module
 */
private[io] class NodePath(val pathString: String) extends Path:
  private lazy val parsed = NodePath.parse(pathString)
  
  override def toString: String = pathString
  
  def last: String = parsed.base
  
  def baseName: String = parsed.name
  
  def ext: String =
    if parsed.ext.startsWith(".") then parsed.ext.substring(1)
    else parsed.ext
  
  def up: Path = new NodePath(NodePath.dirname(pathString))
  
  def /(relPath: RelPath): Path =
    new NodePath(NodePath.join(pathString, relPath.toString))
  
  def /(fragment: String): Path =
    new NodePath(pathString + NodePath.sep + fragment)
  
  def relativeTo(base: Path): Opt[RelPath] =
    try S(new NodeRelPath(NodePath.relative(base.toString, pathString)))
    catch case _: Exception => N
  
  def segments: Ls[String] =
    pathString.split(NodePath.sep).toList.filter(_.nonEmpty)
  
  def isAbsolute: Bool = NodePath.isAbsolute(pathString)

/**
 * JavaScript implementation of RelPath using Node.js path module
 */
private[io] class NodeRelPath(val pathString: String) extends RelPath:
  override def toString: String = pathString
  
  def segments: Ls[String] =
    pathString.split(NodePath.sep).toList.filter(_.nonEmpty)
  
  def /(other: RelPath): RelPath =
    new NodeRelPath(NodePath.join(pathString, other.toString))

/**
 * Platform-specific factory for creating Path instances
 */
private[io] object PathFactory:
  def fromString(str: String) = new NodePath(str)
  def separator: String = NodePath.sep
  def relPathFromString(str: String) = new NodeRelPath(str)
  def relPathUp = new NodeRelPath("..")
