package hkmc2
package io

import mlscript.utils.shorthands._
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel

@js.native
trait JSFileSystem extends js.Object:
  def read(path: String): String = js.native
  def write(path: String, content: String): Unit = js.native
  def exists(path: String): Boolean = js.native
  def getLastChangedTimestamp(path: String): Double = js.native

@JSExportTopLevel("DummyFileSystem")
class DummyFileSystem(fs: JSFileSystem) extends FileSystem:
  def read(path: Path): String =
    fs.read(path.toString)

  def write(path: Path, content: String): Unit =
    fs.write(path.toString, content)

  def exists(path: Path): Bool =
    fs.exists(path.toString)

  def getLastChangedTimestamp(path: Path): Long =
    fs.getLastChangedTimestamp(path.toString).toLong
