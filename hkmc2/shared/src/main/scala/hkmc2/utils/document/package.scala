package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import scala.language.implicitConversions

/**
 * A basic pretty-printing library that handles indentation and conditional line-breaking.
 *
 * The most convenient way to build a Document is with a combination of `doc"..."` string interpolation and use of [[DocBuilder]].
 * To use `doc` string interpolation, you have to import `document._`.
 *
 */
package object document {
  import Document._

  implicit def toDocumentContext(ctx: StringContext): DocumentContext = new DocumentContext(ctx)

  implicit def toDocument[T: Liftable](x: T): Document = implicitly[Liftable[T]].apply(x)

  implicit val docLift: Liftable[Document] = Liftable[Document](identity)

  implicit val intLift: Liftable[Int] = Liftable[Int](_.toString)

  implicit val strLift: Liftable[String] = Liftable[String](text)

  // /** Lifting document lists with line breaks in between is almost never what the user wants, and leads to errors */
  //  implicit def seqLift[T: Liftable]: Liftable[Seq[T]] = Liftable[Seq[T]] { ls =>
  //    val lift = implicitly[Liftable[T]].apply _
  //    (ls map lift).mkDocument()
  //  }

  implicit class LiftableSeqOps[A: Liftable](docs: Seq[A]) {
    def mkDocument(pre: Document, sep: Document, post: Document): Document = docs filter (_ != empty) match {
      case d +: ds => pre :: ((d: Document) +: ds.map(sep :: _)).foldLeft(empty)(_ :: _) :: post
      case _       => pre :: post
    }
    def mkDocument(sep: Document = empty): Document = mkDocument(empty, sep, empty)
  }

}

