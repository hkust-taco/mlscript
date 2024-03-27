package hkmc2

import mlscript.utils._, shorthands._

import math.Ordered.orderingToOrdered


type Raise = Diagnostic => Unit


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

