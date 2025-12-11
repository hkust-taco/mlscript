package hkmc2
package io

import scala.scalajs.js
import scala.scalajs.js.annotation._

import mlscript.utils._, shorthands._

/**
 * Node.js fs module facade
 */
@js.native
@JSImport("fs", JSImport.Namespace)
private object NodeFs extends js.Object:
  def readFileSync(path: String, encoding: String): String = js.native
  def writeFileSync(path: String, data: String): Unit = js.native
  def existsSync(path: String): Boolean = js.native

/**
 * JavaScript implementation of [[FileSystem]] using Node.js fs module.
 */
private class NodeFileSystem extends FileSystem:
  def read(path: Path): String =
    NodeFs.readFileSync(path.toString, "utf8")
  
  def write(path: Path, content: String): Unit =
    NodeFs.writeFileSync(path.toString, content)
  
  def exists(path: Path): Bool =
    NodeFs.existsSync(path.toString)

private[io] object PlatformFileSystem:
  def default: FileSystem = new NodeFileSystem
