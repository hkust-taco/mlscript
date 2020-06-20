package funtypes

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import funtypes.utils._, shorthands._
import funtypes.Message._

abstract class TyperDatatypes extends TyperHelpers { self: Typer =>
  
  // The data types used for type inference:
  
  case class TypeProvenance(loco: Opt[Loc], desc: Str) {
    override def toString: Str = "‹"+loco.fold(desc)(desc+":"+_)+"›"
  }
  
  /** A type that potentially contains universally quantified type variables,
   *  and which can be isntantiated to a given level. */
  sealed abstract class TypeScheme {
    def instantiate(implicit lvl: Int): SimpleType
  }
  /** A type with universally quantified type variables
   *  (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(level: Int, body: SimpleType) extends TypeScheme {
    val prov: TypeProvenance = body.prov
    def instantiate(implicit lvl: Int) = freshenAbove(level, body)
  }
  /** A type without universally quantified type variables. */
  sealed abstract class SimpleType extends TypeScheme with SimpleTypeImpl {
    val prov: TypeProvenance
    def ctxProv: Opt[TypeProvenance] = N
    def level: Int
    def instantiate(implicit lvl: Int) = this
  }
  case class FunctionType(lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    lazy val level: Int = lhs.level max rhs.level
    override def toString = s"($lhs -> $rhs)"
  }
  case class RecordType(fields: List[(String, SimpleType)])(val prov: TypeProvenance) extends SimpleType {
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    override def toString = s"{${fields.map(f => s"${f._1}: ${f._2}").mkString(", ")}}"
  }
  case class TupleType(fields: List[Opt[Str] -> SimpleType])(val prov: TypeProvenance) extends SimpleType {
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    lazy val toRecord: RecordType =
      RecordType(
        fields.zipWithIndex.map { case ((_, t), i) => ("_"+(i+1), t) } ::: // TODO shadow dups?
        fields.collect { case (S(n), t) => (n, t) }
      )(prov)
    override def toString = s"(${fields.map(f => s"${f._1.fold("")(_+": ")}${f._2}").mkString(", ")})"
  }
  /** The sole purpose of ProxyType is to store additional type provenance info. */
  case class ProxyType(underlying: SimpleType)(val prov: TypeProvenance, override val ctxProv: Opt[TypeProvenance] = N)
      extends SimpleType {
    def level: Int = underlying.level
    
    override def toString = s"[$underlying]"
    // override def toString = s"$underlying[${prov.desc.take(5)}]"
    
    // TOOD override equals/hashCode? — could affect hash consing...
    // override def equals(that: Any): Bool = super.equals(that) || underlying.equals(that)
    // override def equals(that: Any): Bool = unwrapProxies.equals(that)
  }
  case class PrimType(id: SimpleTerm)(val prov: TypeProvenance) extends SimpleType {
    def widen: PrimType = id match {
      case _: IntLit => IntType
      case _: StrLit => StrType
      case _: DecLit => DecType
      case _ => this
    }
    def level: Int = 0
    override def toString = id.idStr
  }
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
   *  Invariant: Types appearing in the bounds never have a level higher than this variable's `level`. */
  final class TypeVariable(
      val level: Int,
      var lowerBounds: List[SimpleType],
      var upperBounds: List[SimpleType],
  )(val prov: TypeProvenance) extends SimpleType with CompactTypeOrVariable {
    private[funtypes] val uid: Int = { freshCount += 1; freshCount - 1 }
    private[funtypes] var recursiveFlag = false // used temporarily by `compactType`
    lazy val asTypeVar = new TypeVar("α", uid)
    override def toString: String = "α" + uid + "'" * level
    override def hashCode: Int = uid
  }
  private var freshCount = 0
  def freshVar(p: TypeProvenance)(implicit lvl: Int): TypeVariable =
    new TypeVariable(lvl, Nil, Nil)(p)
  def resetState(): Unit = {
    freshCount = 0
  }
  trait CompactTypeOrVariable
  type PolarVariable = (TypeVariable, Boolean)
  
}
