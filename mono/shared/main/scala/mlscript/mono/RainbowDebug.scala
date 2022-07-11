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
  private def currentColor = colors((indent + 1) % colors.size)
  private def beginMark = currentColor + "┌" + Console.RESET
  private def endMark = currentColor + "└" + Console.RESET
  private val noPostTrace: Any => String = _ => ""
  private var indent = 0

  def trace[T](pre: String)(thunk: => T)(post: T => String = noPostTrace): T = {
    log(pre)
    indent += 1
    val res =
      try thunk
      finally indent -= 1
    if (!(post eq noPostTrace)) log(post(res))
    res
  }

  inline def log(msg: => String): Unit =
    import scala.collection.mutable.StringBuilder
    val indentBuilder = StringBuilder()
    for i <- 0 to indent do indentBuilder ++= colors(i % colors.size) + "│ " + Console.RESET
    println("[mono] " + indentBuilder.toString + msg)