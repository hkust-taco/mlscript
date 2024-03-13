package mlscript.compiler

import scala.collection.mutable.ArrayBuffer

class TreeDebug(output: String => Unit) extends RainbowDebug(false):
  private val lines = ArrayBuffer[String]()
  private var indentation: Int = 0 

  override inline def writeLine(line: String): Unit = 
    output("║"*indentation ++ line)
    lines += line
  
  override def indent(): Unit = 
    indentation += 1
  override def outdent(): Unit = 
    indentation -= 1

  def getLines: List[String] = lines.toList
