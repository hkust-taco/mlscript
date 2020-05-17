import scala.util.Try
import scala.scalajs.js.annotation.JSExportTopLevel
import org.scalajs.dom
import org.scalajs.dom.document
import org.scalajs.dom.raw.{Event, TextEvent, UIEvent, HTMLTextAreaElement}

object Main {
  def main(args: Array[String]): Unit = {
    val source = document.querySelector("#simple-sub-input")
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
    val target = document.querySelector("#simple-sub-output")
    target.innerHTML = Try {
      import fastparse._
      import fastparse.Parsed.{Success, Failure}
      import simplesub.Parser.pgrm
      import simplesub.TypeError
      parse(str, pgrm(_), verboseFailures = false) match {
        case Failure(err, index, extra) =>
          // this line-parsing logic was copied from fastparse internals:
          val lineNumberLookup = fastparse.internal.Util.lineNumberLookup(str)
          val line = lineNumberLookup.indexWhere(_ > index) match {
            case -1 => lineNumberLookup.length - 1
            case n => math.max(0, n - 1)
          }
          val lines = str.split('\n')
          val lineStr = lines(line min lines.length - 1)
          "Parse error: " + extra.trace().msg +
            s" at line $line:<BLOCKQUOTE>$lineStr</BLOCKQUOTE>"
        case Success(p, index) =>
          // println(s"Parsed: $p")
          val typer = new simplesub.Typer(dbg = false) with simplesub.TypeSimplifier
          val tys = typer.inferTypesJS(p)
          (p.defs.zipWithIndex lazyZip tys).map {
            case ((d, i), Right(ty)) =>
              println(s"Typed `${d._2}` as: $ty")
              println(s" where: ${ty.instantiate(0).showBounds}")
              val com = typer.compactType(ty.instantiate(0))
              println(s"Compact type before simplification: ${com}")
              val sim = typer.simplifyType(com)
              println(s"Compact type after simplification: ${sim}")
              val exp = typer.expandCompactType(sim)
              s"""<b>
                  <font color="#93a1a1">val </font>
                  <font color="LightGreen">${d._2}</font>: 
                  <font color="LightBlue">${exp.show}</font>
                  </b>"""
            case ((d, i), Left(TypeError(msg))) =>
              s"""<b><font color="Red">
                  Type error in <font color="LightGreen">${d._2}</font>: $msg
                  </font></b>"""
          }.mkString("<br/>")
      }
    }.fold(err => s"""
      <font color="Red">
      Unexpected error: ${err}${
        err.printStackTrace
        err
      }</font>""", identity)
  }
}
