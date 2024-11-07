package hkmc2

import scala.util.boundary

import mlscript.utils._, shorthands._

import math.Ordered.orderingToOrdered


type Raise = Diagnostic => Unit
def raise(using r: Raise): Raise = r


trait TypeLike:
  def showIn(prec: Int)(using ShowCtx): Str = ???
  lazy val typeVarsList: List[TypeVar] = this match
    case uv: TypeVar => uv :: Nil
    // case Recursive(n, b) => n :: b.typeVarsList
    // case _ => childrenTypes.flatMap(_.typeVarsList)

trait NullaryType extends TypeLike

trait Located:
  def toLoc: Opt[Loc]

trait AutoLocated extends Located:
  protected def children: List[Located]
  
  private var loc: Opt[Loc] = N
  
  def withLoc(s: Int, e: Int, ori: Origin): this.type =
    withLoc(S(Loc(s, e, ori)))
  def withLoc(loco: Opt[Loc]): this.type =
    require(loc.isEmpty)
    loc = loco
    this
  def withLocOf(that: Located): this.type = withLoc(that.toLoc)
  def toLoc: Opt[Loc] = boundary:
    if loc.isEmpty then
      def subLocs = children.iterator.flatMap(_.toLoc.iterator)
      val spanStart =
        subLocs.map(_.spanStart).minOption.getOrElse(boundary.break(N))
      val spanEnd =
        subLocs.map(_.spanEnd).maxOption.getOrElse(boundary.break(N))
      val origins = subLocs.map(_.origin).toList.distinct
      assert(origins.size === 1, origins)
      val res = S(Loc(spanStart, spanEnd, origins.head))
      val _ = withLoc(res)
      res
    else loc
  def withoutLoc: this.type =
    loc = N
    this
  private[hkmc2] def getLoc: Opt[Loc] = ???
  

/** If the identifier is an integer, we can still have a string name used as a name hint. */
final case class TypeVar(val identifier_name: EitherOrBoth[Int, Str]) extends NullaryType with TypeVarImpl:
  val identifier: Int \/ Str = identifier_name.reduce(left)(right)((x, y) => x)
  def nameHint: Opt[Str] = identifier_name.second
  override def toString: Str = identifier.fold("α" + _, identity)
trait TypeVarImpl extends Ordered[TypeVar] { self: TypeVar =>
  def name: Opt[Str] = identifier.toOption.orElse(nameHint)
  def compare(that: TypeVar): Int =
    (this.identifier.fold((_, ""), (0, _))) compare (that.identifier.fold((_, ""), (0, _)))
}

