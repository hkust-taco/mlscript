package hkmc2

import mlscript.utils.*, shorthands.*


class ReportFormatter(output: Str => Unit):
  
  // report errors and warnings
  def apply(blockLineNum: Int, diags: Ls[Diagnostic], showRelativeLineNums: Bool): Unit =
    diags.foreach { diag =>
      val sctx = Message.mkCtx(diag.allMsgs.iterator.map(_._1), "?")
      val onlyOneLine = diag.allMsgs.size =:= 1 && diag.allMsgs.head._2.isEmpty
      val headStr =
        val headChar = if onlyOneLine then '═' else '╔'
        diag match
        case ErrorReport(msg, loco, src) =>
          src match
            case Diagnostic.Source.Lexing =>
              s"$headChar══[LEXICAL ERROR] "
            case Diagnostic.Source.Parsing =>
              s"$headChar══[PARSE ERROR] "
            case Diagnostic.Source.Compilation =>
              s"$headChar══[COMPILATION ERROR] "
            case Diagnostic.Source.Runtime =>
              s"$headChar══[RUNTIME ERROR] "
            case _ => // TODO customize too
              s"$headChar══[ERROR] "
        case WarningReport(msg, loco, src) =>
          s"$headChar══[WARNING] "
        case InternalError(msg, loco, src) =>
          s"$headChar══[INTERNAL ERROR] "
      val lastMsgNum = diag.allMsgs.size - 1
      var globalLineNum = blockLineNum
      diag.allMsgs.zipWithIndex.foreach { case ((msg, loco), msgNum) =>
        val isLast = msgNum =:= lastMsgNum
        val msgStr = msg.showIn(sctx)
        if msgNum =:= 0 then output(headStr + msgStr)
        else if loco.isEmpty && diag.allMsgs.size =:= 1 then
          if !onlyOneLine then output("╙──")
        else output(s"${if isLast && loco.isEmpty then "╙──" else "╟──"} ${msgStr}")
        loco.foreach { loc =>
          val (startLineNum, startLineStr, startLineCol) =
            loc.origin.fph.getLineColAt(loc.spanStart)
          if globalLineNum =:= 0 then globalLineNum += startLineNum - 1
          val (endLineNum, endLineStr, endLineCol) =
            loc.origin.fph.getLineColAt(loc.spanEnd)
          var l = startLineNum
          var c = startLineCol
          while l <= endLineNum do
            val globalLineNum = loc.origin.startLineNum + l - 1
            val relativeLineNum = globalLineNum - blockLineNum + 1
            val shownLineNum =
              if showRelativeLineNums && relativeLineNum > 0 then s"l.+$relativeLineNum"
              else "l." + globalLineNum
            val prepre = "║  "
            val pre = s"$shownLineNum: "
            val curLine = loc.origin.fph.lines(l - 1)
            output(prepre + pre + "\t" + curLine)
            val tickBuilder = new StringBuilder()
            tickBuilder ++= (
              (if isLast && l =:= endLineNum then "╙──" else prepre)
              + " " * pre.length + "\t" + " " * (c - 1))
            val lastCol = if l =:= endLineNum then endLineCol else curLine.length + 1
            while c < lastCol do { tickBuilder += ('^'); c += 1 }
            if c =:= startLineCol then tickBuilder += ('^')
            output(tickBuilder.toString)
            c = 1
            l += 1
        }
      }
      if diag.allMsgs.isEmpty then output("╙──")
      
      // if (!mode.fixme) {
      //   if (!allowTypeErrors
      //       && !mode.expectTypeErrors && diag.isInstanceOf[ErrorReport] && diag.source =:= Diagnostic.Typing)
      //     { output("TEST CASE FAILURE: There was an unexpected type error"); failures += globalLineNum }
      //   if (!allowParseErrors
      //       && !mode.expectParseErrors && diag.isInstanceOf[ErrorReport] && (diag.source =:= Diagnostic.Lexing || diag.source =:= Diagnostic.Parsing))
      //     { output("TEST CASE FAILURE: There was an unexpected parse error"); failures += globalLineNum }
      //   if (!allowTypeErrors && !allowParseErrors
      //       && !mode.expectWarnings && diag.isInstanceOf[WarningReport])
      //     { output("TEST CASE FAILURE: There was an unexpected warning"); failures += globalLineNum }
      // }
      
      ()
    }

