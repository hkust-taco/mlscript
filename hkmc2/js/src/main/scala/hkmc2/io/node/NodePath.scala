package hkmc2
package io
package node

import scala.scalajs.js
import scala.scalajs.js.annotation._

import hkmc2.utils.*, shorthands.*

/**
 * JavaScript implementation of Path using Node.js path module
 */
private[io] case class NodePath(val pathString: String) extends Path:
  private lazy val parsed = path.parse(pathString)
  
  override def toString: String = pathString
  
  def last: String = parsed.base
  
  def baseName: String = parsed.name
  
  def ext: String =
    if parsed.ext.startsWith(".") then parsed.ext.substring(1)
    else parsed.ext
  
  def up: Path = new NodePath(path.dirname(pathString))
  
  def /(relPath: RelPath): Path =
    new NodePath(path.join(pathString, relPath.toString))
  
  def /(fragment: String): Path =
    new NodePath(pathString + path.sep + fragment)
  
  def relativeTo(base: Path): Opt[RelPath] =
    try S(new NodeRelPath(path.relative(base.toString, pathString)))
    catch case _: Exception => N
  
  def segments: Ls[String] =
    pathString.split(path.sep).toList.filter(_.nonEmpty)
  
  def isAbsolute: Bool = path.isAbsolute(pathString)

/**
 * JavaScript implementation of RelPath using Node.js path module
 */
private[io] class NodeRelPath(val pathString: String) extends RelPath:
  override def toString: String = pathString
  
  def segments: Ls[String] =
    pathString.split(path.sep).toList.filter(_.nonEmpty)
  
  def /(other: RelPath): RelPath =
    new NodeRelPath(path.join(pathString, other.toString))
