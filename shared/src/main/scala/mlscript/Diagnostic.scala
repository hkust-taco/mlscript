package mlscript

import scala.util.chaining._
import mlscript.utils._, shorthands._

import Diagnostic._

sealed abstract class Diagnostic(val theMsg: String) extends Exception(theMsg) {
  val allMsgs: Ls[Message -> Opt[Loc]]
  val kind: Kind
  val source: Source
}
object Diagnostic {
  
  sealed abstract class Kind
  case object Error   extends Kind
  case object Warning extends Kind
  
  sealed abstract class Source
  case object Lexing      extends Source
  case object Parsing     extends Source
  case object PreTyping   extends Source
  case object Desugaring  extends Source
  case object Typing      extends Source
  case object Compilation extends Source
  case object Runtime     extends Source
  
}

final case class ErrorReport(mainMsg: Str, allMsgs: Ls[Message -> Opt[Loc]], source: Source) extends Diagnostic(mainMsg) {
  val kind: Kind = Error
}
object ErrorReport {
  def apply(msgs: Ls[Message -> Opt[Loc]], newDefs: Bool, source: Source = Typing): ErrorReport =
    ErrorReport(msgs.head._1.show(newDefs), msgs, source)
}

final case class WarningReport(mainMsg: Str, allMsgs: Ls[Message -> Opt[Loc]], source: Source) extends Diagnostic(mainMsg) {
  val kind: Kind = Warning
}
object WarningReport {
  def apply(msgs: Ls[Message -> Opt[Loc]], newDefs: Bool, source: Source = Typing): WarningReport =
    WarningReport(msgs.head._1.show(newDefs), msgs, source)
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
  def ++(that: Loc): Loc = {
    require(this.origin is that.origin)
    Loc(this.spanStart min that.spanStart, this.spanEnd max that.spanEnd, origin)
  }
  def ++(that: Opt[Loc]): Loc = that.fold(this)(this ++ _)
  def right: Loc = copy(spanStart = spanEnd)
  def left: Loc = copy(spanEnd = spanStart)
}
object Loc {
  def apply(xs: IterableOnce[Located]): Opt[Loc] =
    xs.iterator.foldLeft(none[Loc])((acc, l) => acc.fold(l.toLoc)(_ ++ l.toLoc |> some))
}

final case class Origin(fileName: Str, startLineNum: Int, fph: FastParseHelpers) {
  override def toString = s"$fileName:+$startLineNum"
}

