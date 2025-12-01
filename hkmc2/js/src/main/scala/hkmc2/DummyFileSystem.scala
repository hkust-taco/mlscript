package hkmc2

import scala.scalajs.js.annotation.*
import scala.scalajs.js, js.JSConverters.*
import mlscript.utils.*, shorthands.*
import io.*

/**
  * Provide a wrapper for virtual file system implemented in JavaScript.
  *
  * @param module the JavaScript objct representing the file system
  */
@JSExportTopLevel("DummyFileSystem")
class DummyFileSystem(module: js.Dynamic) extends io.FileSystem:
  /** Read entire file as string. */
  def read(path: Path): String =
    module.read(path.toString).asInstanceOf[String]
  
  /** Write string to file, overwriting if exists. */
  def write(path: Path, content: String): Unit =
    module.write(path.toString, content)
  
  /** Check if a file exists at the given path. */
  def exists(path: Path): Bool =
    module.exists(path.toString).asInstanceOf[Bool]
