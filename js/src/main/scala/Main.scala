import scala.util.Try
import scala.scalajs.js.annotation.JSExportTopLevel
import org.scalajs.dom
import org.scalajs.dom.document
import org.scalajs.dom.raw.{Event, TextEvent, UIEvent, HTMLTextAreaElement}
import mlscript.utils._
import mlscript._
import mlscript.utils.shorthands._
import scala.util.matching.Regex

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
    target.innerHTML = Try {
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
          val (typeCheckResult, hasError) = checkingProgramType(pgrm)
          if (hasError) { typeCheckResult }
          else {
            val backend = new JSBackend()
            typeCheckResult + backend
              .apply(pgrm)
              .map(replaceLeadingSpaces)
              .mkString(htmlLineBreak, htmlLineBreak, "")
          }
      }
    }.fold(
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

  def checkingProgramType(pgrm: Pgrm): Str -> Bool = {
    val typer = new mlscript.Typer(
      dbg = false,
      verbose = false,
      explainErrors = false
    )

    import typer._

    val res = new collection.mutable.StringBuilder
    val stopAtFirstError = true
    var errorOccurred = false

    def getType(ty: typer.TypeScheme): Type = {
      val wty = ty.instantiate(0).widenVar
      println(s"Typed as: $wty")
      println(s" where: ${wty.showBounds}")
      val com = typer.compactType(wty)
      println(s"Compact type before simplification: ${com}")
      val sim = typer.simplifyType(com)
      println(s"Compact type after simplification: ${sim}")
      val exp = typer.expandCompactType(sim)
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
        case d @ Def(isrec, nme, rhs) =>
          val errProv = TypeProvenance(rhs.toLoc, "let-bound value")
          val ty = typeLetRhs(isrec, nme, rhs)
          ctx += nme -> ty
          println(s"Typed `${d.nme}` as: $ty")
          println(s" where: ${ty.instantiate(0).showBounds}")
          res ++= formatBinding(d.nme, ty)
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
              }
            case L(pty) =>
              val exp = getType(pty)
              if (exp =/= Primitive("unit")) {
                val nme = "res"
                ctx += nme -> pty
                res ++= formatBinding(nme, pty)
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
          res ++= formatError(culprit, err)
          errorOccurred = true
      }
    }

    res.toString -> errorOccurred
  }
}
