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
    def indent: Lines = {
      @tailrec
      def rec(acc: Lines, lines: Lines): Lines = lines match {
        case (n, line) :: tail => rec((n + 1, line) :: acc, tail)
        case Nil => acc.reverse
      }
      rec(Nil, lines)
    }
    def ##:(prefix: Str): Lines = (0, prefix) :: lines.indent
    def #:(prefix: Str): Lines = {
      lines match {
        case (0, line) :: lines if lines.forall(_._1 > 0) => (0, s"$prefix $line") :: lines
        case lines => (0, prefix) :: lines.indent
      }
    }
    def @:(prefix: Str): Lines = {
      lines match {
        case (_, line) :: Nil => (0, prefix + " " + line) :: Nil
        case lines => (0, prefix) :: lines.indent
      }
    }
    def toIndentedString: Str =
      lines.iterator.map { case (n, line) => "  " * n + line }.mkString("\n")
  }

  // TODO: Remove this exception. The desugarer should work in a non-fatal way.
  // We may call `lastWords` if unrecoverable errors are found.
  class DesugaringException(val messages: Ls[Message -> Opt[Loc]]) extends Throwable {
    def this(message: Message, location: Opt[Loc]) = this(message -> location :: Nil)
  }
}
