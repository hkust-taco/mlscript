package mlscript.mono

class DummyDebug extends Debug:
  def trace[T](name: String, pre: String)
              (thunk: => T)
              (post: T => String = Debug.noPostTrace): T = thunk
  inline def log(msg: => String): Unit = ()