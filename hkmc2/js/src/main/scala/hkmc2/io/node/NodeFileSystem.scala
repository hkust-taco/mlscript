package hkmc2
package io
package node

import scala.scalajs.js
import scala.scalajs.js.annotation._

import hkmc2.utils.*, shorthands.*

/**
 * JavaScript implementation of [[FileSystem]] using Node.js fs module.
 */
private[io] class NodeFileSystem extends FileSystem:
  def read(path: Path): String =
    fs.readFileSync(path.toString, "utf8")
  
  def write(path: Path, content: String): Unit =
    fs.writeFileSync(path.toString, content)
  
  def exists(path: Path): Bool =
    fs.existsSync(path.toString)
  
  def getLastChangedTimestamp(path: Path): Long =
    fs.lstatSync(path.toString).mtime.getTime().toLong
