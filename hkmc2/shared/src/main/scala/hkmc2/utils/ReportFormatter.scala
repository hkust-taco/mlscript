package hkmc2

import collection.mutable

import hkmc2.utils.*, shorthands.*


/**
  * Formats diagnostic reports using box drawing characters and/or ANSI colors.
  *
  * @param output The output function (e.g., `System.out.println`).
  * @param colorize Whether to colorize the output using ANSI colors.
  * @param wrap Optionally wraps each `Raise` call, e.g., with `synchronized`.
  */
class ReportFormatter(
  output: Str => Unit,
  val colorize: Bool,
  val wrap: Opt[(=> Unit) => Unit] = N
):
  val MaxLineCount = 5
  
  /** Output main text. */
  private def text(str: Str) =
    output(if colorize then fansi.Color.Red(str).toString else str)
  
  /** Output title text. */
  private def title(str: Str) =
    output(if colorize then fansi.Color.LightRed(str).toString else str)
  
  val badLines = mutable.Buffer.empty[Int]
  
  /** Create a `Raise` dedicated to reporting diagnostics for `file`. */
  def mkRaise(file: io.Path): Raise =
    // This shows the parent directory of a file and its name.
    val relPath = file.relativeTo(file.up.up).map(_.toString).getOrElse(file.toString)
    d =>
      def mk =
        title(s"/!!!\\ Error in $relPath /!!!\\")
        apply(0, d :: Nil, showRelativeLineNums = false)
      wrap.fold(mk)(_(mk))
  
  /** Report errors and warnings. */
  def apply(blockLineNum: Int, diags: Ls[Diagnostic], showRelativeLineNums: Bool): Unit =
    diags.foreach { diag =>
      val sctx = Message.mkCtx(diag.allMsgs.iterator.map(_._1), "?")
      val onlyOneLine = diag.allMsgs.size =:= 1 && diag.allMsgs.head._2.isEmpty
      val headStr =
        val headChar = if onlyOneLine then '═' else '╔'
        diag match
        case ErrorReport(msg, loco, mkei, src) =>
          src match
            case Diagnostic.Source.Lexing =>
              s"$headChar══[LEXICAL ERROR] "
            case Diagnostic.Source.Parsing =>
              s"$headChar══[PARSE ERROR] "
            case Diagnostic.Source.Compilation =>
              s"$headChar══[COMPILATION ERROR] "
            case Diagnostic.Source.Runtime =>
              s"$headChar══[RUNTIME ERROR] "
            case Diagnostic.Source.Typing =>
              s"$headChar══[TYPE ERROR] "
        case WarningReport(msg, loco, mkei, src) =>
          s"$headChar══[WARNING] "
        case InternalError(msg, loco, mkei, src) =>
          s"$headChar══[INTERNAL ERROR] "
      val lastMsgNum = diag.allMsgs.size - 1
      var globalLineNum = blockLineNum
      diag.allMsgs.zipWithIndex.foreach { case ((msg, loco), msgNum) =>
        val isLastMsg = msgNum =:= lastMsgNum
        val msgStr = msg.showIn(using sctx)
        if msgNum =:= 0 then text(headStr + msgStr)
        else if loco.isEmpty && diag.allMsgs.size =:= 1 then
          if !onlyOneLine then text("╙──")
        else text(s"${if isLastMsg && loco.isEmpty then "╙──" else "╟──"} ${msgStr}")
        loco.foreach { loc =>
          val (startLineNum, startLineStr, startLineCol) =
            loc.origin.fph.getLineColAt(loc.spanStart)
          badLines += startLineNum
          if globalLineNum =:= 0 then globalLineNum += startLineNum - 1
          val (endLineNum, endLineStr, endLineCol) =
            loc.origin.fph.getLineColAt(loc.spanEnd)
          var l = startLineNum
          var c = startLineCol
          var lineCount = 0
          while l <= endLineNum && lineCount < MaxLineCount do
            val isLastLineOfLoc = l === endLineNum || lineCount === MaxLineCount - 1
            lineCount += 1
            val globalLineNum = loc.origin.startLineNum + l - 1
            val relativeLineNum = globalLineNum - blockLineNum + 1
            val shownLineNum =
              if showRelativeLineNums && relativeLineNum > 0 then s"l.+$relativeLineNum"
              else "l." + globalLineNum
            val prepre = "║  "
            val pre = s"$shownLineNum: "
            val curLine = if lineCount < MaxLineCount
              then loc.origin.fph.lines(l - 1)
              else "... (more lines omitted) ..."
            text(prepre + pre + "\t" + curLine)
            val tickBuilder = new StringBuilder()
            tickBuilder ++= (
              (if isLastMsg && isLastLineOfLoc then "╙──" else prepre)
              + " " * pre.length + "\t" + " " * (c - 1))
            val lastCol = if l =:= endLineNum then endLineCol else curLine.length + 1
            while c < lastCol do { tickBuilder += ('^'); c += 1 }
            if c =:= startLineCol then tickBuilder += ('^')
            text(tickBuilder.toString.stripTrailing)
            c = 1
            l += 1
        }
      }
      if diag.allMsgs.isEmpty then text("╙──")
      
      // if (!mode.fixme) {
      //   if (!allowTypeErrors
      //       && !mode.expectTypeErrors && diag.isInstanceOf[ErrorReport] && diag.source =:= Diagnostic.Typing)
      //     { text("TEST CASE FAILURE: There was an unexpected type error"); failures += globalLineNum }
      //   if (!allowParseErrors
      //       && !mode.expectParseErrors && diag.isInstanceOf[ErrorReport] && (diag.source =:= Diagnostic.Lexing || diag.source =:= Diagnostic.Parsing))
      //     { text("TEST CASE FAILURE: There was an unexpected parse error"); failures += globalLineNum }
      //   if (!allowTypeErrors && !allowParseErrors
      //       && !mode.expectWarnings && diag.isInstanceOf[WarningReport])
      //     { text("TEST CASE FAILURE: There was an unexpected warning"); failures += globalLineNum }
      // }
      
      ()
    }

