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
    target.innerHTML = {
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
          val typing = new simplesub.Typer
          try {
            val tys = typing.inferTypes(p)
            (p.defs lazyZip tys).map { case (d, ty) =>
              println(s"Typed `${d._2}` as: $ty")
              println(s" where: ${ty.instantiate(0).showBounds}")
              val exp = typing.expandPosType(ty.instantiate(0), true)
              println(s"Exanded type before simplification: ${exp.show}")
              val sim = exp.simplify
              s"""<b>
                  <font color="#93a1a1">val </font>
                  <font color="LightGreen">${d._2}</font>: 
                  <font color="LightBlue">${sim.show}</font>
                  </b>"""
            }.mkString("<br/>")
          } catch {
            case TypeError(msg) => "Type error: " + msg
          }
      }
    }
  }
}
