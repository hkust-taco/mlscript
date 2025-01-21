package hkmc2

import scala.util.chaining._
import mlscript.utils._, shorthands._

import Diagnostic._

sealed abstract class Diagnostic(val theMsg: String) extends Exception(theMsg):
  val allMsgs: Ls[Message -> Opt[Loc]]
  val kind: Kind
  val source: Source
  val mkExtraInfo: () => Opt[Any]
object Diagnostic:
  
  enum Kind:
    case Error
    case Warning
    case Internal
  
  enum Source:
    case Lexing
    case Parsing
    case Typing
    case Compilation
    case Runtime
  

final case class ErrorReport(
    mainMsg: Str,
    allMsgs: Ls[Message -> Opt[Loc]],
    mkExtraInfo: () => Opt[Any],
    source: Source,
) extends Diagnostic(mainMsg):
  val kind: Kind = Kind.Error
object ErrorReport:
  def apply(msgs: Ls[Message -> Opt[Loc]], extraInfo: => Opt[Any] = N, source: Source = Source.Typing): ErrorReport =
    ErrorReport(msgs.head._1.show, msgs, () => extraInfo, source)

final case class WarningReport(
    mainMsg: Str,
    allMsgs: Ls[Message -> Opt[Loc]],
    mkExtraInfo: () => Opt[Any],
    source: Source,
) extends Diagnostic(mainMsg):
  val kind: Kind = Kind.Warning
object WarningReport:
  def apply(msgs: Ls[Message -> Opt[Loc]], extraInfo: => Opt[Any] = N, source: Source = Source.Typing): WarningReport =
    WarningReport(msgs.head._1.show, msgs, () => extraInfo, source)

final case class InternalError(mainMsg: Str, allMsgs: Ls[Message -> Opt[Loc]], source: Source) extends Diagnostic(mainMsg):
  val kind: Kind = Kind.Internal
  val mkExtraInfo: () => Opt[Any] = () => N
object InternalError:
  def apply(msgs: Ls[Message -> Opt[Loc]], source: Source = Source.Typing): InternalError =
    InternalError(msgs.head._1.show, msgs, source)


final case class Loc(spanStart: Int, spanEnd: Int, origin: Origin):
  assert(spanStart >= 0)
  assert(spanEnd >= spanStart)
  def covers(that: Loc): Bool = that.origin === this.origin && (
    that.spanStart >= this.spanStart && that.spanEnd <= this.spanEnd
  )
  def touches(that: Loc): Bool = that.origin === this.origin && (
    that.spanStart >= this.spanStart && that.spanStart <= this.spanEnd
    || that.spanEnd <= this.spanEnd && that.spanEnd >= this.spanStart
  )
  def ++(that: Loc): Loc =
    require(this.origin is that.origin)
    Loc(this.spanStart min that.spanStart, this.spanEnd max that.spanEnd, origin)
  def ++(that: Opt[Loc]): Loc = that.fold(this)(this ++ _)
  def right: Loc = copy(spanStart = spanEnd)
  def left: Loc = copy(spanEnd = spanStart)
object Loc:
  def apply(xs: IterableOnce[Located]): Opt[Loc] =
    xs.iterator.foldLeft(none[Loc])((acc, l) => acc.fold(l.toLoc)(_ ++ l.toLoc |> some))

final case class Origin(fileName: Str, startLineNum: Int, fph: FastParseHelpers):
  override def toString = s"$fileName:+$startLineNum"

