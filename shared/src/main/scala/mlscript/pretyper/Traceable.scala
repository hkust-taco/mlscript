package mlscript.pretyper

import mlscript.Diagnostic
import mlscript.utils._, shorthands._

trait Traceable {
  /** The set of topics to debug. Empty set indicates all topics. */
  protected val debugTopics: Opt[Set[Str]] = N
  protected var indent = 0
  private var topic: Opt[Str] = N

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

  def traceWithTopic[T](topic: Str)(thunk: => T): T = {
    this.topic = S(topic)
    val res = thunk
    this.topic = N
    res
  }

  @inline def traceNot[T](pre: => String)(thunk: => T)(post: T => String = Traceable.noPostTrace): T =
    thunk
  
  @inline protected def println(x: => Any): Unit =
    topic match {
      case N => if (debugTopics.isDefined) printLineByLine(x)
      case S(topic) => if (debugTopics.fold(false)(ts => ts.isEmpty || ts.contains(topic))) printLineByLine(x)
    }
}

object Traceable {
  val noPostTrace: Any => String = _ => ""
}
