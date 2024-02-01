package mlscript

import scala.annotation.tailrec
import utils._, shorthands._

package object ucs {
  class VariableGenerator(prefix: Str) {
    private var nextIndex = 0

    def apply(): Var = {
      val thisIndex = nextIndex
      nextIndex += 1
      Var(s"$prefix$thisIndex")
    }

    def reset(): Unit = nextIndex = 0
  }

  type Lines = Ls[(Int, Str)]

  implicit class LinesOps(private val lines: Lines) extends AnyVal {
    /** Increase the indentation of all lines by one. */
    def indent: Lines = lines.map { case (n, line) => (n + 1, line) }

    /**
      * Prepend a new line and indent the remaining lines. When you want to add
      * a "title" to several lines and indent them, you should use this function.
      * 
      * Suppose we have the following `Lines` representing case branches.
      * ```
      * A -> 0
      * B -> 0
      * ```
      * We can prepend string `case x of` to lines and get the following result.
      * ```
      * case x of
      *   A -> 0
      *   B -> 0
      * ```
      */
    def ##:(prefix: Str): Lines = (0, prefix) :: lines.indent

    /**
      * If the first line does not have indentation and the remaining lines are
      * indented, prepend the given string to the first line. Otherwise, prepend
      * the given string to the first line and indent all remaining lines.
      *
      * When you want to amend the title of lines, you should use this function.
      */
    def #:(prefix: Str): Lines = {
      lines match {
        case (0, line) :: lines if lines.forall(_._1 > 0) => (0, s"$prefix $line") :: lines
        case lines => (0, prefix) :: lines.indent
      }
    }
    /**
      * If there is only one line, prepend the given string to the beginning of
      * this line. Otherwise, use the given string as the first line and indent
      * the remaining lines.
      * 
      * Similar to `##:`, except this function does not indent if there is only
      * one line.
      */
    def @:(prefix: Str): Lines = lines match {
      case (_, line) :: Nil => (0, prefix + " " + line) :: Nil
      case lines => (0, prefix) :: lines.indent
    }

    /** Make a multi-line string. */
    def toIndentedString: Str =
      lines.iterator.map { case (n, line) => "  " * n + line }.mkString("\n")
  }
}
