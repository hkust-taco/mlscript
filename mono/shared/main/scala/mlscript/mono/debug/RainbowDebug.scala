package mlscript.mono

import scala.collection.mutable.ArrayBuffer

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
    if (pre.contains("\n"))
      val leadingLength = name.length + 1 // one space
      val leadingSpaces = " " * leadingLength
      pre.split("\n").toList match {
        case head :: tail =>
          log(s"$beginMark $name ${Console.UNDERLINED}$head${Console.RESET}")
          indent += 1
          tail.foreach { line =>
            log(s"$leadingSpaces${Console.UNDERLINED}$line${Console.RESET}")
          }
          indent -= 1
        case Nil =>
      }
    else
      log(s"$beginMark $name ${Console.UNDERLINED}$pre${Console.RESET}")
    indent += 1
    val res =
      try thunk
      finally indent -= 1
    if (post eq Debug.noPostTrace) {
      log(s"$endMark $name")
    } else {
      val result = post(res)
      val leadingLength = name.length + 3 // one space
      val leadingSpaces = " " * leadingLength
      result.split("\n").toList match {
        case head :: tail =>
          log(s"$endMark $name ${Console.UNDERLINED}$head${Console.RESET}")
          tail.foreach { line =>
            log(s"$leadingSpaces${Console.UNDERLINED}$line${Console.RESET}")
          }
        case Nil =>
      }
    }
    res
  }

  inline def log(msg: => String): Unit =
    import scala.collection.mutable.StringBuilder
    val indentBuilder = StringBuilder()
    for i <- 0 until indent do
      indentBuilder ++= colors(i % colors.size) + "│ " + Console.RESET
    println("[mono] " + indentBuilder.toString + msg)