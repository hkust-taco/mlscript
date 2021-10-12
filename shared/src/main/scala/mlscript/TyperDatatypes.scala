package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

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
    def instantiate(implicit lvl: Int): SimpleType = freshenAbove(level, body)
    def rigidify(implicit lvl: Int): SimpleType = freshenAbove(level, body, rigidify = true)
  }
  
  /** A type without universally quantified type variables. */
  sealed abstract class SimpleType extends TypeScheme with SimpleTypeImpl {
    val prov: TypeProvenance
    def ctxProv: Opt[TypeProvenance] = N
    def level: Int
    def instantiate(implicit lvl: Int) = this
  }
  type ST = SimpleType
  
  sealed abstract class BaseType extends SimpleType
  
  case class FunctionType(lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends BaseType {
    lazy val level: Int = lhs.level max rhs.level
    override def toString = s"($lhs -> $rhs)"
  }
  
  // TODO remove or dedup with TypeRef...
  case class AppType(lhs: SimpleType, args: Ls[SimpleType])(val prov: TypeProvenance) extends BaseType {
    require(args.nonEmpty)
    lazy val level: Int = (lhs :: args).maxBy(_.level).level
    override def toString = s"($lhs${args.map(" " + _).mkString})"
  }
  
  case class RecordType(fields: List[(String, SimpleType)])(val prov: TypeProvenance) extends SimpleType {
    // TODO: assert no repeated fields
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    def toInter: SimpleType =
      fields.map(f => RecordType(f :: Nil)(prov)).foldLeft(TopType:SimpleType)(((l, r) => ComposedType(false, l, r)(noProv)))
    def mergeAllFields(fs: Iterable[Str -> SimpleType]): RecordType = {
      val res = mutable.SortedMap.empty[Str, SimpleType]
      fs.foreach(f => res.get(f._1) match {
        case N => res(f._1) = f._2
        case S(ty) => res(f._1) = ty & f._2
      })
      RecordType(res.toList)(prov)
    }
    def addFields(fs: Ls[Str -> SimpleType]): RecordType = {
      val shadowing = fs.iterator.map(_._1).toSet
      RecordType(fields.filterNot(f => shadowing(f._1)) ++ fs)(prov)
    }
    override def toString = s"{${fields.map(f => s"${f._1}: ${f._2}").mkString(", ")}}"
  }
  object RecordType {
    def mk(fields: List[(String, SimpleType)])(prov: TypeProvenance = noProv): SimpleType =
      if (fields.isEmpty) ExtrType(false)(prov) else RecordType(fields)(prov)
  }
  
  case class TupleType(fields: List[Opt[Str] -> SimpleType])(val prov: TypeProvenance) extends BaseType {
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    lazy val toRecord: RecordType =
      RecordType(
        fields.zipWithIndex.map { case ((_, t), i) => ("_"+(i+1), t) } ::: // TODO dedup fields!
        fields.collect { case (S(n), t) => (n, t) }
      )(prov)
    override def toString = s"(${fields.map(f => s"${f._1.fold("")(_+": ")}${f._2}").mkString(", ")})"
  }
  
  /** Polarity `pol` being `true` means Bot; `false` means Top. These are extrema of the subtyping lattice. */
  case class ExtrType(pol: Bool)(val prov: TypeProvenance) extends SimpleType {
    def level: Int = 0
    override def toString = if (pol) "⊥" else "⊤"
  }
  /** Polarity `pol` being `true` means union; `false` means intersection. */
  case class ComposedType(pol: Bool, lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Int = lhs.level max rhs.level
    override def toString = s"($lhs ${if (pol) "|" else "&"} $rhs)"
  }
  case class NegType(negated: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Int = negated.level
    override def toString = s"~(${negated})"
  }
  
  case class Without(base: SimpleType, names: Set[Str])(val prov: TypeProvenance) extends SimpleType {
    def level: Int = base.level
    override def toString = s"${base}\\${names.mkString("-")}"
  }
  
  case class WithType(base: SimpleType, reft: RecordType)(val prov: TypeProvenance) extends SimpleType {
    def level: Int = base.level max reft.level
    def isEmpty: Bool = this match {
      case WithType(TopType | RecordType(Nil), RecordType(Nil)) => true
      case _ => false
    }
    override def toString = s"${base} w/ ${reft}"
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
  
  case class TypeRef(defn: TypeDef, targs: Ls[SimpleType])(val prov: TypeProvenance, val ctx: Ctx) extends SimpleType {
    assert(targs.size === defn.tparams.size)
    def level: Int = targs.iterator.map(_.level).maxOption.getOrElse(0)
    def expand(implicit raise: Raise): SimpleType = {
      val body_ty = typeType(defn.body)(ctx, raise, defn.tparams.zip(targs).toMap)
      if (defn.kind === Als) body_ty
      else clsNameToNomTag(defn)(noProv/*TODO*/, ctx) & body_ty
    }
    override def toString =
      if (targs.isEmpty) defn.nme.name else s"${defn.nme.name}[${targs.mkString(",")}]"
  }
  
  case class PrimType(id: SimpleTerm, parents: Set[Var])(val prov: TypeProvenance) extends BaseType {
    def widenPrim: PrimType = id match { // FIXME rm
      case _: IntLit => IntType
      case _: StrLit => StrType
      case _: DecLit => DecType
      case _ => this
    }
    lazy val parentsST = parents.map(identity[SimpleTerm]) // TODO inefficient... improve
    def glb(that: PrimType): Opt[PrimType] =
      if (that.id === this.id) S(this)
      else if (that.parentsST.contains(this.id)) S(that)
      else if (this.parentsST.contains(that.id)) S(this)
      else N
    def lub(that: PrimType): Set[PrimType] = // TODO rm? it's unused
      if (that.id === this.id) Set.single(that)
      else if (that.parentsST.contains(this.id)) Set.single(this)
      else if (this.parentsST.contains(that.id)) Set.single(that)
      // else this.parentsST.union(that.parentsST)
      else Set(this, that)
    def level: Int = 0
    override def toString = id.idStr+s"<${parents.mkString(",")}>"
  }
  
  sealed trait Variable extends SimpleType
  
  /** Currently, we consider that a VarType may be extruded/freshened but yet still retain its identity.
   *    This is to support the use case of, for instance, a data definition D of type `forall 'a; 'a -> {}`
   *    which we actually want to type as `forall 'a; VarType(D, 'a -> {})`
   *    for simplicity (instead of `VarType(D, forall 'a; 'a -> {})`)
   *      Indeed, this avoids the need for impredicativity (which for now is not supported)
   *      and even if we supported impredicativity it would likely result in fewer variable instantiations
   *      down the line, while being just as general (at least, as long as we don't instantiate variables on reference).
  */
  final class VarIdentity(val lvl: Int, val v: Var)
  case class VarType(vi: VarIdentity, sign: SimpleType, isAlias: Bool)(val prov: TypeProvenance)
      extends BaseType with Variable {
    def level: Int = vi.lvl max sign.level
    override def toString = s"${vi.v}@${prov.loco.getOrElse(die).spanStart}"
  }
  
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
   *  Invariant: Types appearing in the bounds never have a level higher than this variable's `level`. */
  final class TypeVariable(
      val level: Int,
      var lowerBounds: List[SimpleType],
      var upperBounds: List[SimpleType],
  )(val prov: TypeProvenance) extends SimpleType with Variable with CompactTypeOrVariable {
    private[mlscript] val uid: Int = { freshCount += 1; freshCount - 1 }
    lazy val asTypeVar = new TypeVar("α", uid)
    override def toString: String = "α" + uid + "'" * level
    override def hashCode: Int = uid
  }
  type TV = TypeVariable
  private var freshCount = 0
  def freshVar(p: TypeProvenance)(implicit lvl: Int): TypeVariable =
    new TypeVariable(lvl, Nil, Nil)(p)
  def resetState(): Unit = {
    freshCount = 0
  }
  trait CompactTypeOrVariable
  type PolarVariable = (TypeVariable, Boolean)
  
}
