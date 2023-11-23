package mlscript.pretyper

import mlscript.utils._, shorthands._

trait Traceable {
  // Override this to change the base indentation level.
  def baseIndent: Int = 0

  protected val debugLevel: Opt[Int] = N // The number of verbose.
  protected var indent = baseIndent

  def trace[T](pre: => String)(thunk: => T)(post: T => String = Traceable.noPostTrace): T = {
    println(pre)
    indent += 1
    val res = try thunk finally indent -= 1
    if (post isnt Traceable.noPostTrace) println(post(res))
    res
  }

  @inline def traceNot[T](pre: => String)(thunk: => T)(post: T => String = Traceable.noPostTrace): T =
    thunk
  
  def emitDbg(str: String): Unit = scala.Predef.println(str)
  
  @inline
  protected def println(msg: => Any): Unit = println(msg, 0)
  
  @inline 
  protected def println(msg: => Any, level: Int): Unit =
    if (debugLevel exists (_ >= level)) printLineByLine(msg)

  @inline
  private def printLineByLine(msg: => Any): Unit =
    msg.toString.linesIterator.foreach { line => emitDbg("| " * indent + line) }
}

object Traceable {
  val noPostTrace: Any => String = _ => ""
}
