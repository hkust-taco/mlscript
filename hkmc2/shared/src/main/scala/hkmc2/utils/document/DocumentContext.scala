package hkmc2
package document

import collection.immutable.ArraySeq.unsafeWrapArray

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
    def apply(docs: Document*): Document =
      
      type DocPlus = Document | Nest.type | UnNest.type | BeginGroup.type | EndGroup.type | Insert.type | RawDocText
      case object Nest
      case object UnNest
      case object BeginGroup
      case object EndGroup
      case object Insert
      case class RawDocText(s: String) // avoids the "\n chars" warning of DocText

      assert(ctx.parts.size == docs.size + 1 && ctx.parts.size > 0)

      def interleave(docs: Seq[DocPlus], interleaved: DocPlus) =
        docs.head :: (docs.iterator.drop(1).map { List(interleaved, _) }.flatten.toList: Ls[DocPlus])
      
      def splitOn(mark: String, interleaved: DocPlus) = (ds: Ls[DocPlus]) => ds.flatMap:
        case RawDocText(str) => interleave(unsafeWrapArray(str.split(mark, -1)).map(RawDocText(_)), interleaved)
        case d               => Seq(d)
      
      // Makes a sequence of the parts separated with Nest, UnNest and Insert (for positions where docs are to be inserted)
      val parts = (
        splitOn(" #\\{ ", Nest) andThen
        splitOn(" #\\} ", UnNest) andThen
        splitOn("\\\\\\{", BeginGroup) andThen
        splitOn("\\\\\\}", EndGroup) andThen
        splitOn(" # ", DocBreak(false)) andThen
        splitOn("""\\n""", DocBreak(true)) // interpolated strings don't get special chars replaced (we escape \n for the regex)
      )(interleave(ctx.parts.map(RawDocText(_)), Insert)).map:
          case RawDocText(s) => text(s) // 'text' escapes \n chars
          case d             => d
      
      val diter = docs.iterator
      val allDocs = parts.map:
        case Insert => diter.next()
        case d => d
      
      // Processes the sequence, replacing Nest..UnNest couples by a nest(..) operation
      // the `nested` stack stores the blocks currently being nested (from innermost to outermost)
      def proc(xs: Seq[DocPlus], nested: List[Document]): Document = xs match
        case Nest +: rest => proc(rest, empty :: nested)
        case UnNest +: rest => nested.tail match
          case Nil       => throw new IllegalArgumentException("Closing nesting marker closes nothing")
          case newNested => proc(rest, (newNested.head :: nest(DEFAULT_NEST_COUNT, nested.head)) :: newNested.tail)
        case (d: Document) +: rest                 => proc(rest, (nested.head :: d) :: nested.tail)
        case Seq() if nested.size == 1 => nested.head
        case Seq()                     => throw new IllegalArgumentException("Unmatched opening nesting marker")
      
      proc(allDocs, List(empty))
      
  }
  
}

