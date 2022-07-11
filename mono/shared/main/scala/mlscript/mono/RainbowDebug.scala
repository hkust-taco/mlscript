package mlscript.mono

import scala.collection.mutable.ArrayBuffer

class RainbowDebug:
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
  private val noPostTrace: Any => String = _ => ""
  private var indent = 0

  def trace[T](name: String, pre: String)
              (thunk: => T)
              (post: T => String = noPostTrace): T = {
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
    val epilogue = if post eq noPostTrace
      then " "
      else s" ${Console.UNDERLINED}${post(res)}${Console.RESET}"
    log(s"$endMark $name$epilogue")
    res
  }

  inline def log(msg: => String): Unit =
    import scala.collection.mutable.StringBuilder
    val indentBuilder = StringBuilder()
    for i <- 0 until indent do
      indentBuilder ++= colors(i % colors.size) + "│ " + Console.RESET
    println("[mono] " + indentBuilder.toString + msg)