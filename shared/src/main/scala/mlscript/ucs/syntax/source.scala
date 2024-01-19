package mlscript.ucs.syntax

import mlscript.{Lit, Located, Term, Var}
import mlscript.utils._, shorthands._
import scala.annotation.tailrec
import scala.collection.immutable

package object source {
  sealed abstract class Pattern extends Located {
    override def toString(): String = this match {
      case AliasPattern(nme, pattern) => s"${nme.name} @ $pattern"
      case LiteralPattern(literal) => literal.idStr
      case ConcretePattern(nme) => s"`${nme.name}`"
      case NamePattern(nme) => nme.name
      case EmptyPattern(_) => "•"
      case ClassPattern(Var(name), ps, rfd) => (if (rfd) "refined " else "") + (ps match {
        case N => name
        case S(parameters) => parameters.mkString(s"$name(", ", ", ")")
      })
      case TuplePattern(fields) => fields.mkString("(", ", ", ")")
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
  final case class ConcretePattern(nme: Var) extends Pattern {
    override def children: List[Located] = nme :: Nil
  }
  final case class NamePattern(nme: Var) extends Pattern {
    override def children: List[Located] = nme :: Nil
  }
  /**
    * Represents wildcard patterns or missing patterns which match everything.
    * Should be transformed from `Var("_")` or unrecognized terms.
    */
  final case class EmptyPattern(source: Term) extends Pattern {
    override def children: List[Located] = source :: Nil
  }
  final case class ClassPattern(nme: Var, parameters: Opt[List[Pattern]], refined: Bool) extends Pattern {
    override def children: List[Located] = nme :: parameters.getOrElse(Nil)
  }
  final case class TuplePattern(fields: List[Pattern]) extends Pattern {
    override def children: List[Located] = fields
  }
  final case class RecordPattern(entries: List[(Var -> Pattern)]) extends Pattern {
    override def children: List[Located] = entries.iterator.flatMap { case (nme, als) => nme :: als :: Nil }.toList
  }

  sealed abstract class Split[+SomeBranch <: Branch] extends Located {
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

  sealed abstract class TermBranch extends Branch {
    final def toSplit: TermSplit = Split.single(this)
  }
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
    final def toSplit: OperatorSplit = Split.single(this)
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
    final def toSplit: PatternSplit = Split.single(this)
  }
  type PatternSplit = Split[PatternBranch]
}
