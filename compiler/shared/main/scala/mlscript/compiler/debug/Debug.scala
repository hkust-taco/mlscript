package mlscript.compiler.debug

abstract class Debug:
  def trace[T](name: String, pre: Any*)
              (thunk: => T)
              (post: T => Any = Debug.noPostTrace): T
  def log(msg: => String): Unit
  def writeLine(line: String): Unit

object Debug:
  val noPostTrace: Any => Any = _ => ""
