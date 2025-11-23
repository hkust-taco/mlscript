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

object DocumentContext:
  case object Nest; type Nest = Nest.type
  case object UnNest; type UnNest = UnNest.type
  case object BeginGroup; type BeginGroup = BeginGroup.type
  case object EndGroup; type EndGroup = EndGroup.type
  case object Insert; type Insert = Insert.type
  case class RawDocText(s: String) // avoids the "\n chars" warning of DocText
import DocumentContext.*

class DocumentContext(ctx: StringContext) {
  
  object doc {
    def apply(docs: Document*): Document =
      
      type DocsMarkers = Document | Nest | UnNest | BeginGroup | EndGroup | RawDocText
      type DocsMarkersInsert = DocsMarkers | Insert
      
      assert(ctx.parts.size == docs.size + 1 && ctx.parts.size > 0)
      
      def interleave(docs: Seq[DocsMarkersInsert], interleaved: DocsMarkersInsert) =
        docs.head :: (docs.iterator.drop(1).map { List(interleaved, _) }.flatten.toList: Ls[DocsMarkersInsert])
      
      def splitOn(mark: String, interleaved: DocsMarkersInsert) = (ds: Ls[DocsMarkersInsert]) => ds.flatMap:
        case RawDocText(str) => interleave(unsafeWrapArray(str.split(mark, -1)).map(RawDocText(_)), interleaved)
        case d: DocsMarkersInsert     => Seq(d)
      
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
        case Insert      => diter.next()
        case d: DocsMarkers => d
      
      // Processes the sequence, replacing Nest..UnNest pairs by a nest(..) call
      // and BeginGroup..EndGroup pairs by a group(..) call
      var curDocs = allDocs
      def process(acc: Document, outer: Insert | Nest | BeginGroup): Document = curDocs match
        case Nil =>
          outer match
          case Insert      => acc
          case Nest        => throw IllegalArgumentException("Unmatched opening nest marker")
          case BeginGroup  => throw IllegalArgumentException("Unmatched opening group marker")
        case doc :: rest =>
          curDocs = rest
          doc match
          case Nest =>
            process(acc :: nest(process(empty, Nest)), outer)
          case UnNest =>
            outer match
            case Nest => acc
            case _    => throw IllegalArgumentException("Closing nest marker closes nothing")
          case BeginGroup =>
            process(acc :: group(process(empty, BeginGroup)), outer)
          case EndGroup =>
            outer match
            case BeginGroup => acc
            case _          => throw IllegalArgumentException("Closing group marker closes nothing")
          case doc: Document =>
            process(acc :: doc, outer)
          case RawDocText(str) =>
            process(acc :: text(str), outer)
      end process
      process(empty, Insert)
      
  }
  
}

