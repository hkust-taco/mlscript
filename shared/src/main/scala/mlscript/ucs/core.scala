package mlscript.ucs

import mlscript.{Lit, Located, Term, Var}
import mlscript.utils._, shorthands._

package object core {
  sealed abstract class Pattern extends Located {
    override def toString(): String = this match {
      case Pattern.Literal(literal) => literal.toString
      case Pattern.Name(Var(name)) => name
      case Pattern.Class(Var(name), N) => name
      case Pattern.Class(Var(name), S(parameters)) =>
        parameters.iterator.map(_.fold("_")(_.name)).mkString(s"$name(", ", ", ")")
      case Pattern.Tuple(fields) => fields.iterator.map(_.fold("_")(_.name)).mkString("(", ", ", ")")
      case Pattern.Record(Nil) => "{}"
      case Pattern.Record(entries) => entries.iterator.map { case (nme, als) => s"$nme: $als" }.mkString("{ ", ", ", " }")
    }
  }
  object Pattern {
    final case class Literal(literal: Lit) extends Pattern {
      override def children: Ls[Located] = literal :: Nil
    }
    final case class Name(nme: Var) extends Pattern {
      override def children: Ls[Located] = nme :: Nil
    }
    final case class Class(nme: Var, parameters: Opt[List[Opt[Var]]]) extends Pattern {
      override def children: Ls[Located] = nme :: parameters.fold(Ls.empty[Located])(_.flatten)
    }
    final case class Tuple(elements: List[Opt[Var]]) extends Pattern {
      override def children: Ls[Located] = elements.flatten
    }
    final case class Record(entries: List[(Var -> Var)]) extends Pattern {
      override def children: Ls[Located] = entries.iterator.flatMap { case (nme, als) => nme :: als :: Nil }.toList
    }
  }

  final case class Branch(scrutinee: Var, pattern: Pattern, continuation: Split)

  sealed abstract class Split {
    def ::(head: Branch): Split = Split.Cons(head, this)

    def ++(that: Split): Split = this match {
      case me: Split.Cons => me.copy(tail = me.tail ++ that)
      case me: Split.Let => me.copy(tail = me.tail ++ that)
      case _: Split.Else => this
      case Split.Nil => that
    }
  }

  object Split {
    final case class Cons(head: Branch, tail: Split) extends Split
    final case class Let(rec: Bool, name: Var, term: Term, tail: Split) extends Split
    final case class Else(default: Term) extends Split
    final case object Nil extends Split

    def just(term: Term): Split = Else(term)
  }

  @inline def printSplit(s: Split): Str = showSplit("if", s)

  def showSplit(prefix: Str, s: Split): Str = {
    // TODO: tailrec
    def split(s: Split, isFirst: Bool, isTopLevel: Bool): Lines = s match {
      case Split.Cons(head, tail) => (branch(head) match {
        case (n, line) :: tail => (n, (if (isTopLevel) "" else "") + s"$line") :: tail
        case Nil => Nil
      }) ::: split(tail, false, isTopLevel)
      case Split.Let(_, nme, rhs, tail) => (0, s"let $nme = $rhs") :: split(tail, false, isTopLevel)
      case Split.Else(term) => (if (isFirst) (0, s"then $term") else (0, s"else $term")) :: Nil
      case Split.Nil => Nil
    }
    def branch(b: Branch): Lines = {
      val Branch(scrutinee, pattern, continuation) = b
      s"$scrutinee is $pattern" #: split(continuation, true, false)
    }
    val lines = split(s, true, true)
    (if (prefix.isEmpty) lines else prefix #: lines)
      .iterator.map { case (n, line) => "  " * n + line }.mkString("\n")
  }
}