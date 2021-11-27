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
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
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
          val (diags, (typeDefs, stmts)) = pgrm.desugared
          // report(diags) // TODO... currently the MLParser does not report any in desugaring so this is fine
          val (typeCheckResult, errorResult) = checkProgramType(pgrm)
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
                |      case "number":
                |      case "boolean":
                |      case "function":
                |        return value.toString();
                |      case "string":
                |        return '\"' + value + '\"';
                |      default:
                |        return value.constructor.name + " " + JSON.stringify(value, undefined, 2);
                |    }
                |  }
                |})()""".stripMargin
              println("Running code: " + code)
              // Collect evaluation results.
              var defResults = new collection.mutable.HashMap[Str, Str]
              var exprResults: Ls[Str] = Nil
              val sb = new StringBuilder
              try {
                val results = js.eval(code).asInstanceOf[js.Dictionary[js.Any]]
                results.get("defs").foreach { defs =>
                  defs.asInstanceOf[js.Dictionary[Str]] foreach {
                    case (key, value) => defResults += key -> value
                  }
                }
                results.get("exprs").foreach { exprs =>
                  exprResults = exprs.asInstanceOf[js.Array[Str]].toList
                }
              } catch {
                case e: Throwable =>
                  sb ++= "<font color=\"red\">Runtime error occurred:</font>"
                  sb ++= htmlLineBreak + e.getMessage
                  sb ++= htmlLineBreak
                  sb ++= htmlLineBreak
              }
              // Iterate type and assemble something like:
              // `val <name>: <type> = <value>`
              val nameShadowingCount = new collection.mutable.HashMap[Str, Int]
              typeCheckResult foreach { case (name, ty) =>
                val res = name match {
                  // This type definition is a `def`.
                  case S(name) =>
                    // If the name is shadowing another name,
                    // we have to construct the real name.
                    val realName = nameShadowingCount get name match {
                      // It is a shaowing name.
                      case Some(count) =>
                        nameShadowingCount += name -> (count + 1)
                        s"$name@$count"
                      // This is the first time we meet this name.
                      case None =>
                        nameShadowingCount += name -> 1
                        name
                    }
                    // Get the evaluation results.
                    defResults get realName
                  // This type definition is a expression. (No name)
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
          // err.getStackTrace().map(s"$htmlLineBreak$htmlWhiteSpace$htmlWhiteSpace at " + _).mkString
          ""
        }</font>""",
      identity
    )
  }

  private val htmlLineBreak = "<br />"
  private val htmlWhiteSpace = "&nbsp;"
  private val splitLeadingSpaces: Regex = "^( +)(.+)$".r

  def checkProgramType(pgrm: Pgrm): Ls[Option[Str] -> Str] -> Option[Str] = {
    val (diags, (typeDefs, stmts)) = pgrm.desugared

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
      val wty = ty.instantiate(0)
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
      val exp = typer.expandType(resim, true)
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
      try processTypeDefs(typeDefs)(Ctx.init, raise)
      catch {
        case err: TypeError =>
          res ++= formatError("class definitions", err)
          Ctx.init
      }
    var declared: Map[Str, typer.PolymorphicType] = Map.empty

    var decls = stmts
    while (decls.nonEmpty) {
      val d = decls.head
      decls = decls.tail
      try d match {
        case d @ Def(isrec, nme, L(rhs)) =>
          val ty_sch = typeLetRhs(isrec, nme, rhs)(ctx, raise)
          val inst = ty_sch.instantiate(0)
          println(s"Typed `$nme` as: $inst")
          println(s" where: ${inst.showBounds}")
          val exp = getType(ty_sch)
          ctx += nme -> ty_sch
          declared.get(nme).foreach { sign =>
            // ctx += nme -> sign  // override with less precise declared type?
            subsume(ty_sch, sign)(
              ctx,
              raise,
              TypeProvenance(d.toLoc, "def definition")
            )
          }
          res ++= formatBinding(d.nme, ty_sch)
          results append S(d.nme) -> (getType(ty_sch).show)
        case d @ Def(isrec, nme, R(PolyType(tps, rhs))) =>
          val errProv = TypeProvenance(rhs.toLoc, "def signature")
          val ty_sch = PolymorphicType(
            0,
            typeType(rhs)(
              ctx.nextLevel,
              raise,
              tps.map(tp => tp.name -> freshVar(noProv /*FIXME*/ )(1)).toMap
            )
          )
          ctx += nme -> ty_sch
          declared += nme -> ty_sch
          results append S(d.nme) -> getType(ty_sch).show
        case s: DesugaredStatement =>
          val errProv =
            TypeProvenance(s.toLoc, "expression in statement position")
          typer.typeStatement(s, allowPure = true) match {
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
            case Def(isrec, nme, rhs)  => "def " + nme
            case _: DesugaredStatement => "statement"
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
