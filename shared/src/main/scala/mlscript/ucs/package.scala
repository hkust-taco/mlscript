package mlscript

import scala.annotation.tailrec

package object ucs {
  class VariableGenerator(prefix: String) {
    private var nextIndex = 0

    def apply(): Var = {
      val thisIndex = nextIndex
      nextIndex += 1
      Var(s"$prefix$thisIndex")
    }

    def reset(): Unit = nextIndex = 0
  }

  type Lines = List[(Int, String)]

  implicit class LinesOps(private val lines: Lines) extends AnyVal {
    def indent: Lines = {
      @tailrec
      def rec(acc: Lines, lines: Lines): Lines = lines match {
        case (n, line) :: tail => rec((n + 1, line) :: acc, tail)
        case Nil => acc.reverse
      }
      rec(Nil, lines)
    }
    def ##:(prefix: String): Lines = (0, prefix) :: lines.indent
    def #:(prefix: String): Lines = {
      lines match {
        case (0, line) :: lines if lines.forall(_._1 > 0) => (0, s"$prefix $line") :: lines
        case lines => (0, prefix) :: lines.indent
      }
    }
    def @:(prefix: String): Lines = {
      lines match {
        case (_, line) :: Nil => (0, prefix + " " + line) :: Nil
        case lines => (0, prefix) :: lines.indent
      }
    }
  }
}
