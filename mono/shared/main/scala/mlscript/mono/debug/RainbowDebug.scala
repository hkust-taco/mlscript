package mlscript.mono

import scala.collection.mutable.ArrayBuffer
import scala.collection.immutable.StringOps

class RainbowDebug extends Debug:
  private val colors = {
    val buffer = ArrayBuffer[String]()
    buffer += Console.RED
    buffer += Console.YELLOW
    buffer += Console.GREEN
    buffer += Console.CYAN
    buffer += Console.BLUE
    buffer += Console.MAGENTA
    buffer.toArray
  }
  private def currentColor = colors(indent % colors.size)
  private def beginMark = currentColor + "┌" + Console.RESET
  private def endMark = currentColor + "└" + Console.RESET
  private var indent = 0

  def trace[T](name: String, pre: String)
              (thunk: => T)
              (post: T => String): T = {

    printPrologue(name, pre)
    // if (pre.contains("\n"))
    //   val leadingLength = name.length + 1 // one space
    //   val leadingSpaces = " " * leadingLength
    //   (pre.linesIterator.toList match {
    //     case list @ (_ :: _ :: _) => RainbowDebug.box(list)
    //     case other => other
    //   }) match {
    //     case head :: tail =>
    //       log(s"$beginMark $name ${Console.UNDERLINED}$head${Console.RESET}")
    //       indent += 1
    //       tail.foreach { line =>
    //         log(s"$leadingSpaces${Console.UNDERLINED}$line${Console.RESET}")
    //       }
    //       indent -= 1
    //     case Nil => ()
    //   }
    // else
    //   log(s"$beginMark $name ${Console.UNDERLINED}$pre${Console.RESET}")
    indent += 1
    val res =
      try thunk
      finally indent -= 1
    if (post eq Debug.noPostTrace) {
      log(s"$endMark $name")
    } else {
      val result = post(res)
      printEpilogue(name, result)
    }
    res
  }

  private def printPrologue(name: String, content: String): Unit =
    val leadingLength = name.length + 1
    val leadingSpaces = " " * leadingLength
    (content.linesIterator.toList match {
      case list @ (_ :: _ :: _) => RainbowDebug.box(list)
      case other => other
    }) match {
      case Nil => ()
      case head :: Nil =>
        log(s"$beginMark $name ${Console.UNDERLINED}$head${Console.RESET}")
      case list =>
        log(s"$beginMark $name")
        indent += 1
        list.foreach { line => log(line) }
        indent -= 1
    }

  private def printEpilogue(name: String, content: String): Unit =
    val leadingLength = name.length + 3
    val leadingSpaces = " " * leadingLength
    (content.linesIterator.toList match {
      case list @ (_ :: _ :: _) => RainbowDebug.box(list)
      case other => other
    }) match {
      case Nil => ()
      case head :: Nil =>
        log(s"$endMark $name ${Console.UNDERLINED}$head${Console.RESET}")
      case items =>
        log(s"$endMark $name")
        items.foreach { line => log(s"  $line") }
    }

  inline def log(msg: => String): Unit =
    import scala.collection.mutable.StringBuilder
    val indentBuilder = StringBuilder()
    for i <- 0 until indent do
      indentBuilder ++= colors(i % colors.size) + "│ " + Console.RESET
    println("[mono] " + indentBuilder.toString + msg)

object RainbowDebug:
  def box(lines: List[String]): List[String] =
    val maxWidth = lines.iterator.map(_.length).max
    val gutterWidth = scala.math.log10(lines.length).ceil.toInt
    val newLines = ArrayBuffer[String]()
    newLines += "┌" + "─" * (gutterWidth + 2) + "┬" + "─" * (maxWidth + 2) + "┐"
    lines.iterator.zipWithIndex.foreach { (line, index) =>
      newLines += ("│ " + (index + 1) + " │ " + line.padTo(maxWidth, ' ') + " │")
    }
    newLines += "└" + "─" * (gutterWidth + 2) + "┴" + "─" * (maxWidth + 2) + "┘"
    newLines.toList