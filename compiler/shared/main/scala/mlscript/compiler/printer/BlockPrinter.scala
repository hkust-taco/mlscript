package mlscript.compiler.printer

import scala.collection.mutable.{ArrayBuffer, Stack, StringBuilder}

class BlockPrinter:
  import BlockPrinter.Indentation

  private val indent = Indentation()
  private val lines = ArrayBuffer[String]()
  private val currentLine = StringBuilder()
  private val scopes = Stack[Option[String]]()

  def endLine(): Unit = if currentLine.isEmpty then () else {
    lines += indent(currentLine.toString)
    currentLine.clear()
  }

  def enter(): Unit =
    endLine()
    indent.increase()
    scopes.push(None)

  def enter(begin: String, end: String): Unit =
    currentLine ++= begin
    endLine()
    indent.increase()
    scopes.push(Some(end))

  def leave(): Unit =
    endLine() // ↵
    indent.decrease()
    scopes.pop().foreach { currentLine ++= _ }
    endLine() // ↵

  def print(content: String): Unit = currentLine ++= content

  def toLines: List[String] =
    endLine()
    lines.toList

  override def toString(): String = lines.mkString("\n")

object BlockPrinter:
  class Indentation(mark: String = "  "):
    private var indent = 0
    private var spaces = ArrayBuffer[String]("")
    def increase(): Unit =
      indent += 1
      spaces += spaces.last + mark
    def decrease(): Unit = indent -= 1
    def apply(content: String): String = spaces(indent) + content
