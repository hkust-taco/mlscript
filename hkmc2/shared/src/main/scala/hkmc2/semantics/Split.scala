package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


sealed abstract class Split[+SomeBranch <: Branch] extends Located {
  def ::[OtherBranch >: SomeBranch <: Branch](head: OtherBranch): Split[OtherBranch] = Split.Cons(head, this)
}
object Split {
  final case class Cons[SomeBranch <: Branch](head: SomeBranch, tail: Split[SomeBranch]) extends Split[SomeBranch] {
    override def children: Ls[Located] = head :: tail :: Nil
  }
  final case class Let[SomeBranch <: Branch](rec: Bool, nme: VarSymbol, rhs: Term, tail: Split[SomeBranch]) extends Split[SomeBranch] {
    override def children: Ls[Located] = nme :: rhs :: tail :: Nil
  }
  final case class Else(term: Term) extends Split[Nothing] {
    override def children: Ls[Located] = term :: Nil
  }
  case object NoSplit extends Split[Nothing] {
    override def children: Ls[Located] = Nil
  }

  def empty[SomeBranch <: Branch]: Split[SomeBranch] = NoSplit
  def single[SomeBranch <: Branch](branch: SomeBranch): Split[SomeBranch] = Cons(branch, NoSplit)
  def `then`(term: Term): Split[TermBranch] = Else(term)
  def default[SomeBranch <: Branch](term: Term): Split[SomeBranch] = Else(term)
  def from[SomeBranch <: Branch](branches: Iterable[SomeBranch]): Split[SomeBranch] =
    branches.foldRight(NoSplit: Split[SomeBranch])(Cons.apply)
}

sealed abstract class Branch extends Located

sealed abstract class TermBranch extends Branch {
  final def toSplit: TermSplit = Split.single(this)
}
object TermBranch {
  final case class Boolean(test: Term, continuation: TermSplit) extends TermBranch {
    override def children: Ls[Located] = test :: continuation :: Nil
  }
  final case class Match(scrutinee: Term, continuation: PatternSplit) extends TermBranch {
    override def children: Ls[Located] = scrutinee :: continuation :: Nil
  }
  final case class Left(left: Term, continuation: OperatorSplit) extends TermBranch {
    override def children: Ls[Located] = left :: continuation :: Nil
  }
}
type TermSplit = Split[TermBranch]

sealed abstract class OperatorBranch extends Branch {
  val operator: VarSymbol
  final def toSplit: OperatorSplit = Split.single(this)
}
object OperatorBranch {
  final case class Match(override val operator: VarSymbol, continuation: PatternSplit) extends OperatorBranch {
    override def children: Ls[Located] = operator :: continuation :: Nil
  }
  final case class Binary(override val operator: VarSymbol, continuation: TermSplit) extends OperatorBranch {
    override def children: Ls[Located] = operator :: continuation :: Nil
  }
}
type OperatorSplit = Split[OperatorBranch]

final case class PatternBranch(val pattern: Pattern, val continuation: TermSplit) extends Branch {
  override def children: Ls[Located] = pattern :: continuation :: Nil
  final def toSplit: PatternSplit = Split.single(this)
}
type PatternSplit = Split[PatternBranch]



