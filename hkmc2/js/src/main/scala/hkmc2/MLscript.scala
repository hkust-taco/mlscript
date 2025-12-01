package hkmc2

import scala.util.Try
import scala.scalajs.js.annotation.*
import org.scalajs.dom
import org.scalajs.dom.document
import mlscript.utils._
import mlscript.utils.shorthands._
import scala.util.matching.Regex
import scala.scalajs.js
import scala.collection.immutable

import io.*
import scala.collection.mutable.{ArrayBuffer, Buffer}

@JSExportTopLevel("MLscript")
class MLscript:
  private val fs = InMemoryFileSystem:
    Map("/Prelude.mls" -> generated.MLscript.preludeFile)
  
  private given Config = Config.default.copy(rewriteWhileLoops = false)
  
  private given FileSystem = fs
  
  private val compiler = MLsCompiler(Path("/Prelude.mls"), newOutputBlock)
  
  private val outputBlocks = Buffer.empty[Array[String]]
  
  private def newOutputBlock(start: (Str => Unit) => Unit): Unit =
    val lines = ArrayBuffer.empty[String]
    start(lines.append)
    outputBlocks += lines.toArray
  
  @JSExport
  def compile(content: Str): Unit =
    val filePath = "/main.mls"
    fs.addFile(filePath, content)
    println(s"All files (before compilation): ${fs.allFiles.keys.mkString(", ")}")
    compiler.compileModule(Path(filePath))
    println(s"All files (after compilation): ${fs.allFiles.keys.mkString(", ")}")
    println(s"Output blocks:")
    for lines <- outputBlocks do
      println(lines.mkString("\n"))
    println("Compiled JavaScript:")
    println(fs.read(Path("/main.mjs")))
