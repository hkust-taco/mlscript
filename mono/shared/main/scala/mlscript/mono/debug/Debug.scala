package mlscript.mono

abstract class Debug:
  def trace[T](name: String, pre: String)
              (thunk: => T)
              (post: T => String = Debug.noPostTrace): T
  inline def log(msg: => String): Unit

object Debug:
  val noPostTrace: Any => String = _ => ""