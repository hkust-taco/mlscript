package mlscript.compiler.debug

object DummyDebug extends Debug:
  def trace[T](name: String, pre: Any*)
              (thunk: => T)
              (post: T => Any = Debug.noPostTrace): T = thunk
  inline def log(msg: => String): Unit = ()
  def writeLine(line: String): Unit = ()
