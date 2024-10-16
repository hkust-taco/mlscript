package hkmc2
package document

import mlscript.utils.*, shorthands.*
import utils.*


/* adapted from advanced compiler course project */

import java.io.{ StringWriter, Writer }

/**
 * A basic pretty-printing library, based on Lindig's strict version
 * of Wadler's adaptation of Hughes' pretty-printer.
 *
 * @author Michel Schinz
 * @author Lionel Parreaux
 */
abstract class Document {
  def ::(that: Document): Document = (this, that) match {
    case (DocNil, _) => that
    case (_, DocNil) => this
    case _           => DocCons(that, this)
  }
  def :/:(hd: Document): Document = hd :: DocBreak(force = false) :: this
  def :\\:(hd: Document): Document = hd :: DocBreak(force = true) :: this

  def stripBreaks: Document = this match
    case DocBreak(_) => DocNil
    case DocCons(DocText(""), t) => t.stripBreaks
    case DocCons(h, t) =>
      val res = h.stripBreaks
      if res is h then this else res :: t
    case _ => this

  /**
   * Format this document on `writer` and try to set line
   * breaks so that the result fits in `width` columns.
   */
  def format(width: Int, writer: Writer): Unit = {
    type FmtState = (Int, Boolean, Document) // indent, doBreak, doc

    def fits(w: Int, docs: List[Document]): Boolean = docs match {
      case _ if w < 0 =>
        false
      case Nil =>
        true
      case DocNil :: z =>
        fits(w, z)
      case DocCons(h, t) :: z =>
        fits(w, h :: t :: z) // List concat here, not doc
      case DocText(t) :: z =>
        fits(w - t.length(), z)
      case DocNest(ii, d) :: z =>
        fits(w, d :: z)
      case DocBreak(true) :: z =>
        false
      case DocBreak(false) :: z =>
        fits(w - 1, z)
      case DocGroup(d) :: z =>
        fits(w, d :: z)
    }

    def spaces(n: Int): Unit = {
      var rem = n
      while rem >= 16 do { writer write "                "; rem -= 16 }
      if rem >= 8 then { writer write "        "; rem -= 8 }
      if rem >= 4 then { writer write "    "; rem -= 4 }
      if rem >= 2 then { writer write "  "; rem -= 2 }
      if rem == 1 then { writer write " " }
    }

    def fmt(charsIntoLine: Int, state: List[FmtState]): Unit = {
      def write(indent: Int, text: String): Int = {
        val written = (if charsIntoLine == 0 then { spaces(indent); indent } else charsIntoLine) + text.length
        writer write text
        written
      }
      state match {
        case List() => ()
        case (_, _, DocNil) :: z =>
          fmt(charsIntoLine, z)
        case (i, b, DocCons(h, t)) :: z =>
          fmt(charsIntoLine, (i, b, h) :: (i, b, t) :: z)
        case (i, _, DocText(t)) :: z =>
          fmt(write(i, t), z)
        case (i, b, DocNest(ii, d)) :: z =>
          fmt(charsIntoLine, (i + ii, b, d) :: z)
        case (i, doBreak, DocBreak(force)) :: z if doBreak || force =>
          write(i, "\n")
          fmt(0, z)
        case (i, false, DocBreak(false)) :: z =>
          fmt(write(i, " "), z)
        case (i, b, DocGroup(d)) :: z =>
          val fitsFlat = fits(width - charsIntoLine, d :: (z map (_._3)))
          fmt(charsIntoLine, (i, !fitsFlat, d) :: z)
        case _ =>
          ()
      }
    }

    fmt(0, (0, false, DocGroup(this)) :: Nil)
  }

  def mkString(columns: Int): Str = {
    val w = new StringWriter()
    format(columns, w)
    w.toString
  }
  override def toString: Str = mkString(120)
}

object Document {
  /** The empty document */
  def empty: Document = DocNil

  /** A break, which will either be turned into a space or a line break */
  def break: Document = DocBreak(false)

  /** An unconditional break */
  def forceBreak: Document = DocBreak(true)

  /** A document consisting of some text literal; escapes \n characters, unlike DocText */
  def text(s: String): Document = {
    val docs = s.split("\\n", -1) map DocText // \n needs not be escaped here because it's a single-character string...
    docs.toSeq mkDocument forceBreak
  }

  /**
   * A group, whose components will either be printed with all breaks
   * rendered as spaces, or with all breaks rendered as line breaks.
   */
  def group(d: Document): Document = DocGroup(d)

  /** A nested document, which will be indented as specified. */
  def nest(i: Int, d: Document): Document = DocNest(i, d)

  val DEFAULT_NEST_COUNT = 2

}

private case object DocNil extends Document
private case class DocBreak(force: Boolean) extends Document
private case class DocText(txt: String) extends Document {
  if txt contains '\n' then
    System.err.println(s"Warning: DocText should not contain \\n characters; use DocBreak instead:\n\t$txt")
}
private case class DocGroup(doc: Document) extends Document
private case class DocNest(indent: Int, doc: Document) extends Document
private case class DocCons(hd: Document, tl: Document) extends Document
