package mlscript.compiler.debug

import scala.collection.mutable.ArrayBuffer

class TreeDebug(output: String => Unit) extends RainbowDebug(false):
  private val lines = ArrayBuffer[String]()

  override inline def writeLine(line: String): Unit = 
    output(line)
    lines += line

  def getLines: List[String] = lines.toList
