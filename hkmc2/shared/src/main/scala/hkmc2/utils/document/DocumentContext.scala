package hkmc2
package document

import mlscript.utils.*, shorthands.*
import utils.*

import Document._

/**
 * Doc formatter using string interpolation.
 * Markers " #{ ", " #} " (including the space character) are used to express nesting
 * Marker " # " expresses document break, as well as "\n".
 *
 * For example:
 * {{{
 *   doc"class A { #{  # $decl #}  # }"
 * }}}
 * instead of:
 * {{{
 *   "class A {" :: Document.nest(2, DocBreak :: decl) :/: "}"
 * }}}
 */
class DocumentContext(ctx: StringContext) {

  object doc {
    def apply(docs: Document*): Document = {

      case object Nest extends Document
      case object UnNest extends Document
      case object Insert extends Document
      case class RawDocText(s: String) extends Document // avoids the "\n chars" warning of DocText

      assert(ctx.parts.size == docs.size + 1 && ctx.parts.size > 0)

      def interleave(arr: Seq[Document], interleaved: Document) =
        arr(0) +: arr.tail.map { List(interleaved, _) }.flatten

      def splitOn(mark: String, interleaved: Document) = (ds: Seq[Document]) => ds flatMap {
        case RawDocText(str) => interleave(str.split(mark, -1) map RawDocText, interleaved)
        case d               => Seq(d)
      }

      // Makes a sequence of the parts separated with Nest, UnNest and Insert (for positions where docs are to be inserted)
      val parts = (
        splitOn(" #\\{ ", Nest) andThen
        splitOn(" #\\} ", UnNest) andThen
        splitOn(" # ", DocBreak(false)) andThen
        splitOn("""\\n""", DocBreak(true)) // interpolated strings don't get special chars replaced (we escape \n for the regex)
      )(interleave(ctx.parts map RawDocText, Insert)) map {
          case RawDocText(s) => text(s) // 'text' escapes \n chars
          case d             => d
        }

      val diter = docs.iterator
      val allDocs = parts map { case Insert => diter.next() case d => d }

      // Processes the sequence, replacing Nest..UnNest couples by a nest(..) operation
      // the `nested` stack stores the blocks currently being nested (from innermost to outermost)
      def proc(xs: Seq[Document], nested: List[Document]): Document = xs match {
        case Nest +: rest => proc(rest, empty :: nested)
        case UnNest +: rest => nested.tail match {
          case Nil       => throw new IllegalArgumentException("Closing nesting marker closes nothing")
          case newNested => proc(rest, (newNested.head :: nest(DEFAULT_NEST_COUNT, nested.head)) :: newNested.tail)
        }
        case d +: rest                 => proc(rest, (nested.head :: d) :: nested.tail)
        case Seq() if nested.size == 1 => nested.head
        case Seq()                     => throw new IllegalArgumentException("Unmatched opening nesting marker")
      }
      proc(allDocs, List(empty))

    }
  }

}

