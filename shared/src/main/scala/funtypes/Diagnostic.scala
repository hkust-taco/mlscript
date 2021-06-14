package funtypes

import scala.util.chaining._
import funtypes.utils._, shorthands._


sealed abstract class Diagnostic(theMsg: String) extends Exception(theMsg) {
  val allMsgs: Ls[Message -> Opt[Loc]]
}

final case class TypeError(mainMsg: Str, allMsgs: Ls[Message -> Opt[Loc]]) extends Diagnostic(mainMsg)
object TypeError {
  def apply(msgs: Ls[Message -> Opt[Loc]]): TypeError =
    TypeError(msgs.head._1.show.toString, msgs)
}

final case class Warning(mainMsg: Str, allMsgs: Ls[Message -> Opt[Loc]]) extends Diagnostic(mainMsg)
object Warning {
  def apply(msgs: Ls[Message -> Opt[Loc]]): Warning =
    Warning(msgs.head._1.show.toString, msgs)
}


final case class Loc(spanStart: Int, spanEnd: Int, origin: Origin) {
  assert(spanStart >= 0)
  assert(spanEnd >= spanStart)
  def isWithin(that: Loc): Bool = that.origin === this.origin && (
    that.spanStart >= this.spanStart && that.spanEnd <= this.spanEnd
  )
  def touches(that: Loc): Bool = that.origin === this.origin && (
    that.spanStart >= this.spanStart && that.spanStart <= this.spanEnd
    || that.spanEnd <= this.spanEnd && that.spanEnd >= this.spanStart
  )
}

final case class Origin(fileName: Str, startLineNum: Int, fph: FastParseHelpers) {
  override def toString = s"$fileName:+$startLineNum"
}

