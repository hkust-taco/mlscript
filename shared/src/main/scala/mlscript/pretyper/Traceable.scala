package mlscript.pretyper

import mlscript.Diagnostic
import mlscript.utils._, shorthands._

trait Traceable {
  /** The set of topics to debug. Empty set indicates all topics. */
  protected val debugTopics: Opt[Set[Str]] = N
  protected var indent = 0
  private var currentTopic: Opt[Str] = N

  def emitString(str: String): Unit = scala.Predef.println(str)
  
  @inline private def printLineByLine(x: => Any): Unit =
    x.toString.linesIterator.foreach { line => emitString("| " * indent + line) }

  def trace[T](pre: => String)(thunk: => T)(post: T => String = Traceable.noPostTrace): T = {
    println(pre)
    indent += 1
    val res = try thunk finally indent -= 1
    if (post isnt Traceable.noPostTrace) println(post(res))
    res
  }

  def traceWithTopic[T](currentTopic: Str)(thunk: => T): T = {
    this.currentTopic = S(currentTopic)
    val res = thunk
    this.currentTopic = N
    res
  }

  @inline def traceNot[T](pre: => String)(thunk: => T)(post: T => String = Traceable.noPostTrace): T =
    thunk
  
  @inline protected def println(x: => Any): Unit =
    debugTopics match {
      case S(someTopics) if someTopics.isEmpty || currentTopic.fold(false)(someTopics) => printLineByLine(x)
      case N | S(_) => ()
    }
}

object Traceable {
  val noPostTrace: Any => String = _ => ""
}
