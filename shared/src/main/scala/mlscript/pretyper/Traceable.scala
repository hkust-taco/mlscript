package mlscript.pretyper

import mlscript.Diagnostic
import mlscript.utils._, shorthands._

trait Traceable {
  /**
    * The set of topics to debug. Explanation of possible values.
    * - `N`: Show nothing.
    * - `S(Set.empty)`: Show everything.
    * - `S(someTopics)`: Show only the topics in `someTopics`.
    * Override this function to enable debugging.
    */
  protected def debugTopicFilters: Opt[Set[Str]] = N
  private var debugIndent = 0
  private var currentDebugTopics: Opt[Str] = N

  private def matchTopicFilters: Boolean =
    debugTopicFilters match {
      case S(topics) if topics.isEmpty => true
      case S(topics) => currentDebugTopics.fold(false)(topics)
      case N => false
    }

  /** Override this function to redirect debug messages. */
  protected def emitString(str: Str): Unit = scala.Predef.println(str)
  
  @inline private def printLineByLine(x: => Any): Unit =
    x.toString.linesIterator.foreach { line => emitString("| " * debugIndent + line) }

  protected def trace[T](pre: => Str)(thunk: => T)(post: T => Str = Traceable.noPostTrace): T = {
    println(pre)
    debugIndent += 1
    val res = try thunk finally debugIndent -= 1
    if (post isnt Traceable.noPostTrace) println(post(res))
    res
  }

  protected def traceWithTopic[T](currentDebugTopics: Str)(thunk: => T): T = {
    this.currentDebugTopics = S(currentDebugTopics)
    val res = thunk
    this.currentDebugTopics = N
    res
  }

  @inline def traceNot[T](pre: => Str)(thunk: => T)(post: T => Str = Traceable.noPostTrace): T =
    thunk
  
  @inline protected def println(x: => Any): Unit =
    if (matchTopicFilters) printLineByLine(x)
}

object Traceable {
  val noPostTrace: Any => Str = _ => ""
}
