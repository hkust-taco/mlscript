package hkmc2.bbml

import mlscript.utils.*, shorthands.*

abstract class TraceLogger:
  def doTrace: Bool = true
  
  protected val noPostTrace: Any => String = _ => ""
  
  protected var indent = 0
  def trace[T](pre: => String, post: T => String = noPostTrace)(thunk: => T): T = {
    log(pre)
    indent += 1
    val res = try thunk finally indent -= 1
    if post isnt noPostTrace then log(post(res))
    res
  }
  @inline def traceNot[T](pre: => String)(thunk: => T)(post: T => String = noPostTrace): T =
    thunk
  
  def emitDbg(str: String): Unit = scala.Predef.println(str)
  
  // Shadow Predef functions with debugging-flag-enabled ones:
  
  def log(msg: => Any): Unit = if doTrace then emitDbg("| " * indent + msg)

