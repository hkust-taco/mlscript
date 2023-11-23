package mlscript.ucs

import mlscript.{Lit, Located, Term, Var}
import mlscript.utils._, shorthands._
import scala.annotation.tailrec
import scala.collection.immutable

package object syntax {
  sealed abstract class Pattern extends Located {
    override def toString(): String = this match {
      case AliasPattern(nme, pattern) => s"$nme @ $pattern"
      case LiteralPattern(literal) => literal.toString
      case NamePattern(nme) => nme.toString
      case ClassPattern(Var(name), N) => name
      case ClassPattern(Var(name), S(parameters)) =>
        parameters.iterator.map(_.fold("_")(_.toString)).mkString(s"$name(", ", ", ")")
      case TuplePattern(fields) => fields.iterator.map(_.fold("_")(_.toString)).mkString("(", ", ", ")")
      case RecordPattern(Nil) => "{}"
      case RecordPattern(entries) => entries.iterator.map { case (nme, als) => s"$nme: $als" }.mkString("{ ", ", ", " }")
    }
  }
  final case class AliasPattern(nme: Var, pattern: Pattern) extends Pattern {
    override def children: List[Located] = nme :: pattern :: Nil
  }
  final case class LiteralPattern(literal: Lit) extends Pattern {
    override def children: List[Located] = literal :: Nil
  }
  final case class NamePattern(nme: Var) extends Pattern {
    override def children: List[Located] = nme :: Nil
  }
  final case class ClassPattern(val nme: Var, val parameters: Opt[List[Opt[Pattern]]]) extends Pattern {
    override def children: List[Located] = nme :: parameters.fold(List.empty[Located])(_.flatten)
  }
  final case class TuplePattern(fields: List[Opt[Pattern]]) extends Pattern {
    override def children: List[Located] = fields.flatten
  }
  final case class RecordPattern(entries: List[(Var -> Pattern)]) extends Pattern {
    override def children: List[Located] = entries.iterator.flatMap { case (nme, als) => nme :: als :: Nil }.toList
  }

  sealed abstract class Split[+SomeBranch <: Branch] extends Located {
    def ++[OtherBranch >: SomeBranch <: Branch](that: Split[OtherBranch]): Split[OtherBranch] = this match {
      case Split.Cons(head, tail) => Split.Cons(head, tail ++ that)
      case Split.Let(rec, nme, rhs, tail) => Split.Let(rec, nme, rhs, tail ++ that)
      case Split.Else(_) => this
      case Split.Nil => that
    }
    def ::[OtherBranch >: SomeBranch <: Branch](head: OtherBranch): Split[OtherBranch] = Split.Cons(head, this)
  }
  object Split {
    import immutable.{Nil => LNil}
    final case class Cons[SomeBranch <: Branch](head: SomeBranch, tail: Split[SomeBranch]) extends Split[SomeBranch] {
      override def children: List[Located] = head :: tail :: LNil
    }
    final case class Let[SomeBranch <: Branch](rec: Bool, nme: Var, rhs: Term, tail: Split[SomeBranch]) extends Split[SomeBranch] {
      override def children: List[Located] = nme :: rhs :: tail :: LNil
    }
    final case class Else(term: Term) extends Split[Nothing] {
      override def children: List[Located] = term :: LNil
    }
    final case object Nil extends Split[Nothing] {
      override def children: List[Located] = LNil
    }

    def empty[SomeBranch <: Branch]: Split[SomeBranch] = Nil
    def single[SomeBranch <: Branch](branch: SomeBranch): Split[SomeBranch] = Cons(branch, Nil)
    def `then`(term: Term): Split[TermBranch] = Else(term)
    def default[SomeBranch <: Branch](term: Term): Split[SomeBranch] = Else(term)
    def from[SomeBranch <: Branch](branches: Iterable[SomeBranch]): Split[SomeBranch] =
      branches.foldRight(Nil: Split[SomeBranch])(Cons.apply)
  }

  sealed abstract class Branch extends Located

  sealed abstract class TermBranch extends Branch
  object TermBranch {
    final case class Boolean(test: Term, continuation: TermSplit) extends TermBranch {
      override def children: List[Located] = test :: continuation :: Nil
    }
    final case class Match(scrutinee: Term, continuation: PatternSplit) extends TermBranch {
      override def children: List[Located] = scrutinee :: continuation :: Nil
    }
    final case class Left(left: Term, continuation: OperatorSplit) extends TermBranch {
      override def children: List[Located] = left :: continuation :: Nil
    }
  }
  type TermSplit = Split[TermBranch]

  sealed abstract class OperatorBranch extends Branch {
    val operator: Var
  }
  object OperatorBranch {
    final case class Match(override val operator: Var, continuation: PatternSplit) extends OperatorBranch {
      override def children: List[Located] = operator :: continuation :: Nil
    }
    final case class Binary(override val operator: Var, continuation: TermSplit) extends OperatorBranch {
      override def children: List[Located] = operator :: continuation :: Nil
    }
  }
  type OperatorSplit = Split[OperatorBranch]

  final case class PatternBranch(val pattern: Pattern, val continuation: TermSplit) extends Branch {
    override def children: List[Located] = pattern :: continuation :: Nil
  }
  type PatternSplit = Split[PatternBranch]

  def printTermSplit(split: TermSplit): Str = {
    // TODO: tailrec
    def termSplit(split: TermSplit, isFirst: Bool, isTopLevel: Bool): Lines = split match {
      case Split.Cons(head, tail) => (termBranch(head) match {
        case (n, line) :: tail => (n, (if (isTopLevel) "" else "and ") + s"$line") :: tail
        case Nil => Nil
      }) ::: termSplit(tail, false, isTopLevel)
      case Split.Let(_, nme, rhs, tail) => (0, s"let $nme = $rhs") :: termSplit(tail, false, isTopLevel)
      case Split.Else(term) => (if (isFirst) (0, s"then $term") else (0, s"else $term")) :: Nil
      case Split.Nil => Nil
    }
    def termBranch(branch: TermBranch): Lines = branch match {
      case TermBranch.Boolean(test, continuation) => 
        s"$test" #: termSplit(continuation, true, false)
      case TermBranch.Match(scrutinee, continuation) =>
        s"$scrutinee is" #: patternSplit(continuation)
      case TermBranch.Left(left, continuation) =>
        s"$left" #: operatorSplit(continuation)
    }
    def patternSplit(split: PatternSplit): Lines = split match {
      case Split.Cons(head, tail) => patternBranch(head) ::: patternSplit(tail)
      case Split.Let(rec, nme, rhs, tail) => (0, s"let $nme = $rhs") :: patternSplit(tail)
      case Split.Else(term) => (0, s"else $term") :: Nil
      case Split.Nil => Nil
    }
    def operatorSplit(split: OperatorSplit): Lines = split match {
      case Split.Cons(head, tail) => operatorBranch(head) ::: operatorSplit(tail)
      case Split.Let(rec, nme, rhs, tail) => (0, s"let $nme = $rhs") :: operatorSplit(tail)
      case Split.Else(term) => (0, s"else $term") :: Nil
      case Split.Nil => Nil
    }
    def operatorBranch(branch: OperatorBranch): Lines =
      s"${branch.operator}" #: (branch match {
        case OperatorBranch.Match(_, continuation) => patternSplit(continuation)
        case OperatorBranch.Binary(_, continuation) => termSplit(continuation, true, false)
      })
    def patternBranch(branch: PatternBranch): Lines = {
      val PatternBranch(pattern, continuation) = branch
      termSplit(continuation, true, false) match {
        case (0, line) :: lines => (0, s"$pattern $line") :: lines
        case lines => (0, pattern.toString) :: lines
      }
    }
    ("if" #: termSplit(split, true, true)).iterator.map { case (n, line) => "  " * n + line }.mkString("\n")
  }
}
