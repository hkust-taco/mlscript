package hkmc2

import mlscript.utils._, shorthands._

import math.Ordered.orderingToOrdered


trait TypeLike {
  def showIn(prec: Int)(using ShowCtx): Str = ???
  lazy val typeVarsList: List[TypeVar] = this match {
    case uv: TypeVar => uv :: Nil
    // case Recursive(n, b) => n :: b.typeVarsList
    // case _ => childrenTypes.flatMap(_.typeVarsList)
  }
}

trait NullaryType extends TypeLike

trait Located {
  def children: List[Located]
  def toLoc: Opt[Loc] = ???
}

sealed abstract class SimpleTerm {
  val idStr: Str = this match {
    // case Var(name) => name
    case lit: Lit => lit.showDbg
  }
}

sealed abstract class Lit extends SimpleTerm {
  def showDbg: Str = ???
}

final case class IntLit(value: BigInt)            extends Lit
final case class DecLit(value: BigDecimal)        extends Lit
final case class StrLit(value: Str)               extends Lit
final case class UnitLit(undefinedOrNull: Bool)   extends Lit

/** If the identifier is an integer, we can still have a string name used as a name hint. */
final case class TypeVar(val identifier_name: EitherOrBoth[Int, Str]) extends NullaryType with TypeVarImpl {
  val identifier: Int \/ Str = identifier_name.reduce(left)(right)((x, y) => x)
  def nameHint: Opt[Str] = identifier_name.second
  override def toString: Str = identifier.fold("α" + _, identity)
}
trait TypeVarImpl extends Ordered[TypeVar] { self: TypeVar =>
  def name: Opt[Str] = identifier.toOption.orElse(nameHint)
  def compare(that: TypeVar): Int = {
    (this.identifier.fold((_, ""), (0, _))) compare (that.identifier.fold((_, ""), (0, _)))
  }
}

