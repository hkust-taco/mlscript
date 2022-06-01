package mlscript

import scala.util.chaining._
import mlscript.utils._, shorthands._


sealed abstract class Diagnostic(val theMsg: String) extends Exception(theMsg) {
  val allMsgs: Ls[Message -> Opt[Loc]]
}

// TODO add error kind or diagnostic kind field
final case class CompilationError(mainMsg: Str, allMsgs: Ls[Message -> Opt[Loc]]) extends Diagnostic(mainMsg)
object CompilationError {
  def apply(msgs: Ls[Message -> Opt[Loc]]): CompilationError =
    CompilationError(msgs.head._1.show.toString, msgs)
}

final case class Warning(mainMsg: Str, allMsgs: Ls[Message -> Opt[Loc]]) extends Diagnostic(mainMsg)
object Warning {
  def apply(msgs: Ls[Message -> Opt[Loc]]): Warning =
    Warning(msgs.head._1.show.toString, msgs)
}


final case class Loc(spanStart: Int, spanEnd: Int, origin: Origin) {
  assert(spanStart >= 0)
  assert(spanEnd >= spanStart)
  def covers(that: Loc): Bool = that.origin === this.origin && (
    that.spanStart >= this.spanStart && that.spanEnd <= this.spanEnd
  )
  def touches(that: Loc): Bool = that.origin === this.origin && (
    that.spanStart >= this.spanStart && that.spanStart <= this.spanEnd
    || that.spanEnd <= this.spanEnd && that.spanEnd >= this.spanStart
  )
  def right: Loc = copy(spanStart = spanEnd)
  def left: Loc = copy(spanEnd = spanStart)
}

final case class Origin(fileName: Str, startLineNum: Int, fph: FastParseHelpers) {
  override def toString = s"$fileName:+$startLineNum"
}

