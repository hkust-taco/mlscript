package hkmc2
package document

import mlscript.utils.*, shorthands.*
import utils.*

import scala.collection._
import Document._

/**
 * Use a [[DocBuilder]] to build [[Document]]s for large files. It works similarly to a [[StringBuilder]].
 */
case class DocBuilder(NEST_COUNT: Int = DEFAULT_NEST_COUNT) {

  protected val nestedDocs = mutable.Stack(Document.empty: Document)

  protected def thisret[T](x: T): this.type = this

  /** Appends a document to the builder */
  def +=(d: Document) = thisret {
    nestedDocs push (nestedDocs.pop :: d)
  }

  /** Append a document with a conditional break (breaks in a group are only rendered if the group does not fit on one line) */
  def +=\(d: Document) = thisret {
    this += (d :: break)
  }
  /** Append a document with an unconditional break (always insert newline) */
  def +=\\(d: Document) = thisret {
    this += (d :: forceBreak)
  }

  /** Inserts an unconditional break */
  def newLine = this += forceBreak

  /** Indents all documents appended during the execution of `f` */
  def nest(f: => Unit) = thisret {
    nestedDocs push empty
    f
    this += Document.nest(NEST_COUNT, nestedDocs.pop)
  }

  /**
   * Groups all documents appended during the execution of `f` (grouped documents will have all their conditional
   * linebreaks break together or not break at all)
   */
  def grouped(f: => Document) = thisret {
    this += group(f)
  }

  /** Inserts curly braces around documents appended by `f`, in Scala style */
  def braces(f: => Unit) = thisret {
    this +=\ "{"
    nest { f }
    this +=\ "}"
  }
  /** Inserts curly braces around documents appended by the function passed in argument, after appending document `pre` */
  def bracesAfter(pre: Document) = {
    this += pre :: " "
    braces _
  }

  /** Inserts a line comment */
  def comment(text: String) = this +=\\ ("// " + text)

  /** Converts the current builder to a proper [[Document]] */
  def toDoc = { require(nestedDocs.size == 1); nestedDocs.head }

}

