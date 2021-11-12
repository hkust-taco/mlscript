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
  def typecheck(e: UIEvent): Unit = {
    e.target match {
      case elt: HTMLTextAreaElement =>
        update(elt.value)
    }
  }
  def update(str: String): Unit = {
    // println(s"Input: $str")
    val target = document.querySelector("#mlscript-output")
    val tryRes = Try[Str] {
      import fastparse._
      import fastparse.Parsed.{Success, Failure}
      import mlscript.{MLParser, TypeError, Origin}
      val lines = str.splitSane('\n').toIndexedSeq
      val processedBlock = MLParser.addTopLevelSeparators(lines).mkString
      val fph = new mlscript.FastParseHelpers(str, lines)
      val parser = new MLParser(Origin("<input>", 0, fph))
      parse(processedBlock, parser.pgrm(_), verboseFailures = false) match {
        case f: Failure =>
          val Failure(err, index, extra) = f
          val (lineNum, lineStr, _) = fph.getLineColAt(index)
          "Parse error: " + extra.trace().msg +
            s" at line $lineNum:<BLOCKQUOTE>$lineStr</BLOCKQUOTE>"
        case Success(pgrm, index) =>
          println(s"Parsed: $pgrm")
          val (typeCheckResult, errorResult) = checkingProgramType(pgrm)
          errorResult match {
            case Some(typeCheckResult) => typeCheckResult
            case None => {
              val backend = new JSBackend()
              val lines = backend(pgrm)
              // I know this is very hacky but using `asIntanceOf` is painful.
              // TODO: pretty print JavaScript values in a less hacky way.
              // Maybe I can add a global function for reporting results.
              val code = s"""(() => {
                |  let [defs, exprs] = (() => {
                |    ${lines.mkString("\n")}
                |  })();
                |  for (const key of Object.keys(defs)) {
                |    defs[key] = prettyPrint(defs[key]);
                |  }
                |  exprs = exprs.map(prettyPrint);
                |  return { defs, exprs };
                |  function prettyPrint(value) {
                |    switch (typeof value) {
                |      case "function":
                |        return value.toString();
                |      default:
                |        return JSON.stringify(value, undefined, 2);
                |    }
                |  }
                |})()""".stripMargin
              // Collect evaluation results.
              var defResults = new collection.mutable.HashMap[Str, Str]
              var exprResults: Ls[Str] = Nil
              val sb = new StringBuilder
              try {
                val results = js.eval(code).asInstanceOf[js.Dictionary[js.Any]]
                results.get("defs") match {
                  case S(defs) =>
                    defs.asInstanceOf[js.Dictionary[Str]] foreach {
                      case (key, value) => defResults += key -> value
                    }
                }
                results.get("exprs") match {
                  case S(exprs) =>
                    exprResults = exprs.asInstanceOf[js.Array[Str]].toList
                }
              } catch {
                case e: Throwable =>
                  sb ++= "<font color=\"red\">Runtime error occurred.</font>"
                  sb ++= htmlLineBreak + e.getMessage
              }
              // Iterate type and assemble something like:
              // `val <name>: <type> = <value>`
              typeCheckResult foreach { case (name, ty) =>
                val res = name match {
                  case S(name) => defResults get name
                  case N =>
                    exprResults match {
                      case head :: next => {
                        exprResults = next
                        S(head)
                      }
                      case immutable.Nil => N
                    }
                }
                sb ++= s"""<b>
                  |  <font color="#93a1a1">val </font>
                  |  <font color="LightGreen">${name getOrElse "res"}</font>: 
                  |  <font color="LightBlue">$ty</font>
                  |</b> = ${res getOrElse "<font color=\"gray\">no value</font>"}
                  |$htmlLineBreak""".stripMargin
              }
              sb.toString
            }
          }
      }
    }

    target.innerHTML = tryRes.fold[Str](
      err =>
        s"""
      <font color="Red">
      Unexpected error: ${err}${
          err.printStackTrace
          err
        }</font>""",
      identity
    )
  }

  private val htmlLineBreak = "<br />"
  private val htmlWhiteSpace = "&nbsp;"
  private val splitLeadingSpaces: Regex = "^( +)(.+)$".r

  private def replaceLeadingSpaces(line: Str): Str =
    splitLeadingSpaces.findFirstMatchIn(line) match {
      case S(result) => htmlWhiteSpace * result.group(1).size + result.group(2)
      case N         => line
    }

  def checkingProgramType(pgrm: Pgrm): Ls[Option[Str] -> Str] -> Option[Str] = {
    val typer = new mlscript.Typer(
      dbg = false,
      verbose = false,
      explainErrors = false
    )

    import typer._

    val res = new collection.mutable.StringBuilder
    val results = new collection.mutable.ArrayBuffer[Option[Str] -> Str]
    val stopAtFirstError = true
    var errorOccurred = false

    def getType(ty: typer.TypeScheme): Type = {
      val wty = ty.instantiate(0).widenVar
      println(s"Typed as: $wty")
      println(s" where: ${wty.showBounds}")
      val cty = typer.canonicalizeType(wty)
      println(s"Canon: ${cty}")
      println(s" where: ${cty.showBounds}")
      val sim = typer.simplifyType(cty)
      println(s"Type after simplification: ${sim}")
      println(s" where: ${sim.showBounds}")
      val reca = typer.canonicalizeType(sim)
      println(s"Recanon: ${reca}")
      println(s" where: ${reca.showBounds}")
      val resim = typer.simplifyType(reca)
      println(s"Resimplified: ${resim}")
      println(s" where: ${resim.showBounds}")
      val exp = typer.expandType(resim)
      exp
    }
    def formatError(culprit: Str, err: TypeError): Str = {
      s"""<b><font color="Red">
                Error in <font color="LightGreen">${culprit}</font>: ${err.mainMsg}
                ${err.allMsgs.tail
        .map(_._1.show.toString + "<br/>")
        .mkString("&nbsp;&nbsp;&nbsp;&nbsp;")}
                </font></b><br/>"""
    }
    def formatBinding(nme: Str, ty: TypeScheme): Str = {
      val exp = getType(ty)
      s"""<b>
              <font color="#93a1a1">val </font>
              <font color="LightGreen">${nme}</font>: 
              <font color="LightBlue">${exp.show}</font>
              </b><br/>"""
    }

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
      val sctx = Message.mkCtx(diag.allMsgs.iterator.map(_._1), "?")
      val headStr = diag match {
        case TypeError(msg, loco) =>
          totalTypeErrors += 1
          s"╔══ <strong style=\"color: #E74C3C\">[ERROR]</strong> "
        case Warning(msg, loco) =>
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
            val back = curLine.slice(lastCol - 1, curLine.size)
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

    implicit val raise: Raise = throw _
    implicit var ctx: Ctx =
      try processTypeDefs(pgrm.typeDefs)(Ctx.init, raise)
      catch {
        case err: TypeError =>
          res ++= formatError("class definitions", err)
          Ctx.init
      }

    var decls = pgrm.otherTops
    while (decls.nonEmpty) {
      val d = decls.head
      decls = decls.tail
      try d match {
        case d @ Def(isrec, nme, L(rhs)) =>
          val errProv = TypeProvenance(rhs.toLoc, "def definition")
          val ty = typeLetRhs(isrec, nme, rhs)
          ctx += nme -> ty
          println(s"Typed `${d.nme}` as: $ty")
          println(s" where: ${ty.instantiate(0).showBounds}")
          res ++= formatBinding(d.nme, ty)
          results append S(d.nme) -> getType(ty).show
        case d @ Def(isrec, nme, R(rhs)) =>
          val errProv = TypeProvenance(rhs.toLoc, "def signature")
          ??? // TODO
        case s: Statement =>
          val errProv =
            TypeProvenance(s.toLoc, "expression in statement position")
          val (diags, desug) = s.desugared
          // report(diags) // TODO!!
          typer.typeStatement(desug, allowPure = true) match {
            case R(binds) =>
              binds.foreach { case (nme, pty) =>
                ctx += nme -> pty
                res ++= formatBinding(nme, pty)
                results append S(nme) -> getType(pty).show
              }
            case L(pty) =>
              val exp = getType(pty)
              if (exp =/= Primitive("unit")) {
                val nme = "res"
                ctx += nme -> pty
                res ++= formatBinding(nme, pty)
                results append N -> getType(pty).show
              }
          }
      } catch {
        case err: TypeError =>
          if (stopAtFirstError) decls = Nil
          val culprit = d match {
            case Def(isrec, nme, rhs)       => "def " + nme
            case LetS(isrec, Var(nme), rhs) => "let " + nme
            case _: Statement               => "statement"
          }
          res ++= report(err)
          errorOccurred = true
      }
    }

    results.toList -> (if (errorOccurred) S(res.toString) else N)
  }

  private def underline(fragment: Str): Str =
    s"<u style=\"text-decoration: #E74C3C dashed underline\">$fragment</u>"
}
