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
  case object Typing      extends Source
  case object Compilation extends Source
  case object Runtime     extends Source
  
  def report(diag: Diagnostic, output: Str => Unit, blockLineNum: Int, showRelativeLineNums: Bool): Unit = {
    val sctx = Message.mkCtx(diag.allMsgs.iterator.map(_._1), "?")
    val headStr =
      diag match {
        case ErrorReport(msg, loco, src) =>
          src match {
            case Diagnostic.Lexing =>
              s"╔══[LEXICAL ERROR] "
            case Diagnostic.Parsing =>
              s"╔══[PARSE ERROR] "
            case _ => // TODO customize too
              s"╔══[ERROR] "
          }
        case WarningReport(msg, loco, src) =>
          s"╔══[WARNING] "
      }
    val lastMsgNum = diag.allMsgs.size - 1
    var globalLineNum = blockLineNum  // solely used for reporting useful test failure messages
    diag.allMsgs.zipWithIndex.foreach { case ((msg, loco), msgNum) =>
      val isLast = msgNum =:= lastMsgNum
      val msgStr = msg.showIn(sctx)
      if (msgNum =:= 0) output(headStr + msgStr)
      else output(s"${if (isLast && loco.isEmpty) "╙──" else "╟──"} ${msgStr}")
      if (loco.isEmpty && diag.allMsgs.size =:= 1) output("╙──")
      loco.foreach { loc =>
        val (startLineNum, startLineStr, startLineCol) =
          loc.origin.fph.getLineColAt(loc.spanStart)
        if (globalLineNum =:= 0) globalLineNum += startLineNum - 1
        val (endLineNum, endLineStr, endLineCol) =
          loc.origin.fph.getLineColAt(loc.spanEnd)
        var l = startLineNum
        var c = startLineCol
        while (l <= endLineNum) {
          val globalLineNum = loc.origin.startLineNum + l - 1
          val relativeLineNum = globalLineNum - blockLineNum + 1
          val shownLineNum =
            if (showRelativeLineNums && relativeLineNum > 0) s"l.+$relativeLineNum"
            else "l." + globalLineNum
          val prepre = "║  "
          val pre = s"$shownLineNum: "
          val curLine = loc.origin.fph.lines(l - 1)
          output(prepre + pre + "\t" + curLine)
          val tickBuilder = new StringBuilder()
          tickBuilder ++= (
            (if (isLast && l =:= endLineNum) "╙──" else prepre)
            + " " * pre.length + "\t" + " " * (c - 1))
          val lastCol = if (l =:= endLineNum) endLineCol else curLine.length + 1
          while (c < lastCol) { tickBuilder += ('^'); c += 1 }
          if (c =:= startLineCol) tickBuilder += ('^')
          output(tickBuilder.toString)
          c = 1
          l += 1
        }
      }
    }
    if (diag.allMsgs.isEmpty) output("╙──")
  }
}

final case class ErrorReport(mainMsg: Str, allMsgs: Ls[Message -> Opt[Loc]], source: Source) extends Diagnostic(mainMsg) {
  val kind: Kind = Error
}
object ErrorReport {
  def apply(msgs: Ls[Message -> Opt[Loc]], source: Source = Typing): ErrorReport =
    ErrorReport(msgs.head._1.show, msgs, source)
}

final case class WarningReport(mainMsg: Str, allMsgs: Ls[Message -> Opt[Loc]], source: Source) extends Diagnostic(mainMsg) {
  val kind: Kind = Warning
}
object WarningReport {
  def apply(msgs: Ls[Message -> Opt[Loc]], source: Source = Typing): WarningReport =
    WarningReport(msgs.head._1.show, msgs, source)
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

