import scala.util.Try
import scala.scalajs.js.annotation.JSExportTopLevel
import org.scalajs.dom
import org.scalajs.dom.document
import org.scalajs.dom.raw.{Event, TextEvent, UIEvent, HTMLTextAreaElement}
import mlscript.utils._
import mlscript._
import mlscript.utils.shorthands._
import scala.util.matching.Regex
import scala.scalajs.js
import scala.collection.immutable

object Main {
  def main(args: Array[String]): Unit = {
    val source = document.querySelector("#mlscript-input")
    update(source.textContent)
    source.addEventListener("input", typecheck)
  }
  @JSExportTopLevel("typecheck")
  def typecheck(e: dom.UIEvent): Unit = {
    e.target match {
      case elt: dom.HTMLTextAreaElement =>
        update(elt.value)
    }
  }
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  def update(str: String): Unit = {
    // println(s"Input: $str")
    val target = document.querySelector("#mlscript-output")
    
    
    def underline(fragment: Str): Str =
      s"<u style=\"text-decoration: #E74C3C dashed underline\">$fragment</u>"
    
    var totalTypeErrors = 0
    var totalWarnings = 0
    var outputMarker = ""
    val blockLineNum = 0
    val showRelativeLineNums = false
    
    def report(diag: Diagnostic): Str = {
      var sb = new collection.mutable.StringBuilder
      def output(s: Str): Unit = {
        sb ++= outputMarker
        sb ++= s
        sb ++= htmlLineBreak
        ()
      }
      val sctx = Message.mkCtx(diag.allMsgs.iterator.map(_._1), newDefs=true, "?")
      val headStr = diag match {
        case ErrorReport(msg, loco, src) =>
          totalTypeErrors += 1
          s"╔══ <strong style=\"color: #E74C3C\">[ERROR]</strong> "
        case WarningReport(msg, loco, src) =>
          totalWarnings += 1
          s"╔══ <strong style=\"color: #F39C12\">[WARNING]</strong> "
      }
      val lastMsgNum = diag.allMsgs.size - 1
      var globalLineNum =
        blockLineNum // solely used for reporting useful test failure messages
      diag.allMsgs.zipWithIndex.foreach { case ((msg, loco), msgNum) =>
        val isLast = msgNum =:= lastMsgNum
        val msgStr = msg.showIn(sctx)
        if (msgNum =:= 0)
          output(headStr + msgStr)
        else
          output(s"${if (isLast && loco.isEmpty) "╙──" else "╟──"} ${msgStr}")
        if (loco.isEmpty && diag.allMsgs.size =:= 1) output("╙──")
        loco.foreach { loc =>
          val (startLineNum, startLineStr, startLineCol) =
            loc.origin.fph.getLineColAt(loc.spanStart)
          if (globalLineNum =:= 0) globalLineNum += startLineNum - 1
          val (endLineNum, endLineStr, endLineCol) =
            loc.origin.fph.getLineColAt(loc.spanEnd)
          var l = startLineNum
          var c = startLineCol // c starts from 1
          while (l <= endLineNum) {
            val globalLineNum = loc.origin.startLineNum + l - 1
            val relativeLineNum = globalLineNum - blockLineNum + 1
            val shownLineNum =
              if (showRelativeLineNums && relativeLineNum > 0)
                s"l.+$relativeLineNum"
              else "l." + globalLineNum
            val prepre = "║  "
            val pre = s"$shownLineNum: " // Looks like l.\d+
            val curLine = loc.origin.fph.lines(l - 1)
            val lastCol =
              if (l =:= endLineNum) endLineCol else curLine.length + 1
            val front = curLine.slice(0, c - 1)
            val middle = underline(curLine.slice(c - 1, lastCol - 1))
            val back = curLine.slice(lastCol - 1, curLine.length)
            output(s"$prepre$pre\t$front$middle$back")
            c = 1
            l += 1
            if (isLast) output("╙──")
          }
        }
      }
      if (diag.allMsgs.isEmpty) output("╙──")
      sb.toString
    }
    
    val tryRes = try {
      import fastparse._
      import fastparse.Parsed.{Success, Failure}
      import mlscript.{NewParser, ErrorReport, Origin}
      val lines = str.splitSane('\n').toIndexedSeq
      val processedBlock = lines.mkString
      val fph = new mlscript.FastParseHelpers(str, lines)
      val origin = Origin("<input>", 1, fph)
      val lexer = new NewLexer(origin, throw _, dbg = false)
      val tokens = lexer.bracketedTokens
      val parser = new NewParser(origin, tokens, newDefs = true, throw _, dbg = false, N) {
        def doPrintDbg(msg: => Str): Unit = if (dbg) println(msg)
      }
      parser.parseAll(parser.typingUnit) match {
        case tu =>
          val pgrm = Pgrm(tu.entities)
          println(s"Parsed: $pgrm")
          
          val typer = new mlscript.Typer(
            dbg = false,
            verbose = false,
            explainErrors = false,
            newDefs = true,
          )
          
          import typer._

          implicit val raise: Raise = throw _
          implicit var ctx: Ctx = Ctx.init
          implicit val extrCtx: Opt[typer.ExtrCtx] = N

          val vars: Map[Str, typer.SimpleType] = Map.empty
          val tpd = typer.typeTypingUnit(tu, N)(ctx.nest, raise, vars)
          
          object SimplifyPipeline extends typer.SimplifyPipeline {
            def debugOutput(msg: => Str): Unit =
              // if (mode.dbgSimplif) output(msg)
              println(msg)
          }
          val sim = SimplifyPipeline(tpd, S(true))(ctx)
          
          val exp = typer.expandType(sim)(ctx)
          
          val expStr = exp.showIn(0)(ShowCtx.mk(exp :: Nil, newDefs = true)).stripSuffix("\n")
            .replaceAll("  ", "&nbsp;&nbsp;")
            .replaceAll("\n", "<br/>")

          // TODO format HTML better
          val typingStr = """<div><table width="100%">
                            |  <tr>
                            |    <td colspan="2"><h4><i>Typing Results:</i></h4></td>
                            |  </tr>
                            |""".stripMargin +
                         s"""<tr>
                            |  ${s"<td colspan=\"2\">${expStr}</td>"}
                            |</tr>
                            |""".stripMargin

          val backend = new JSWebBackend()
          val (lines, resNames) = backend(pgrm)
          val code = lines.mkString("\n")

          // TODO: add a toggle button to show js code
          // val jsStr = ("\n\n=====================JavaScript Code=====================\n" + code)
          //   .stripSuffix("\n")
          //   .replaceAll("  ", "&nbsp;&nbsp;")
          //   .replaceAll("\n", "<br/>")

          val exe = executeCode(code) match {
            case Left(err) => err
            case Right(lines) => generateResultTable(resNames.zip(lines))
          }

          val resStr = ("""<tr>
                          |  <td colspan="2"><h4><i>Execution Results:</i></h4></td>
                          |</tr>
                          |""".stripMargin + exe + "</table>")
          
          typingStr + resStr
      }
    } catch {
      // case err: ErrorReport =>
      case err: Diagnostic =>
        report(err)
      case err: Throwable =>
        s"""
      <font color="Red">
      Unexpected error: ${err}${
          err.printStackTrace
          // err.getStackTrace().map(s"$htmlLineBreak$htmlWhiteSpace$htmlWhiteSpace at " + _).mkString
          ""
        }</font>"""
    }
    
    target.innerHTML = tryRes
  }

  // Execute the generated code.
  // We extract this function because there is some boilerplate code.
  // It returns a tuple of three items:
  // 1. results of definitions;
  // 2. results of expressions;
  // 3. error message (if has).
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  private def executeCode(code: Str): Either[Str, Ls[Str]] = {
    try {
      R(js.eval(code).asInstanceOf[js.Array[Str]].toList)
    } catch {
      case e: Throwable =>
        val errorBuilder = new StringBuilder()
        errorBuilder ++= "<font color=\"red\">Runtime error occurred:</font>"
        errorBuilder ++= htmlLineBreak + e.getMessage
        errorBuilder ++= htmlLineBreak
        errorBuilder ++= htmlLineBreak
        L(errorBuilder.toString)
    }
  }

  private def generateResultTable(res: Ls[(Str, Str)]): Str = {
    val htmlBuilder = new StringBuilder
    htmlBuilder ++= """<tr>
                      |  <td>Name</td>
                      |  <td>Value</td>
                      |</tr>
                      |""".stripMargin

    res.foreach(value => {
      htmlBuilder ++= s"""<tr>
                         |  <td class="name">${value._1.replaceAll("  ", "&nbsp;&nbsp;").replaceAll("\n", "<br/>")}</td>
                         |  ${s"<td>${value._2.replaceAll("  ", "&nbsp;&nbsp;").replaceAll("\n", "<br/>")}</td>"}
                         |</tr>
                         |""".stripMargin
    })

    htmlBuilder.toString
  }
  
  private val htmlLineBreak = "<br />"
  private val htmlWhiteSpace = "&nbsp;"
}

