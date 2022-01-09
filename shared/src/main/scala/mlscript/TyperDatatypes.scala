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
    def & (that: TypeProvenance): TypeProvenance = this // arbitrary; maybe should do better
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
  
  class MethodType(level: Int, body: SimpleType, val parents: List[TypeName], val single: Bool)
      extends PolymorphicType(level, body) {
    def &(that: MethodType): MethodType = {
      require(this.level === that.level)
      MethodType(level, this.body & that.body, (this.parents ::: that.parents).distinct, false)
    }
    def +(that: MethodType): MethodType =
      if (this.parents === that.parents) that
      else MethodType(0, errType(noProv), (this.parents ::: that.parents).distinct)
    override def toString: Str = s"MethodType($level, $body, $parents)"
    def copyMT(level: Int = this.level, body: SimpleType = this.body, parents: List[TypeName] = this.parents): MethodType =
      MethodType(level, body, parents, this.single)
  }
  object MethodType {
    def apply(level: Int, body: SimpleType, parent: TypeName): MethodType = new MethodType(level, body, parent :: Nil, true)
    def apply(level: Int, body: SimpleType, parents: List[TypeName]): MethodType = new MethodType(level, body, parents, true)
    private def apply(level: Int, body: SimpleType, parents: List[TypeName], single: Bool): MethodType =
      new MethodType(level, body, parents, single)
    def unapply(mt: MethodType): S[(Int, SimpleType, List[TypeName])] = S((mt.level, mt.body, mt.parents))
  }

  class AbstractConstructor(val absMths: Set[Var])(body: SimpleType) extends PolymorphicType(0, body) {
    override def toString: Str = s"AbstractConstructor($absMths)"
  }
  object AbstractConstructor {
    def apply(absMths: Set[Var])(implicit prov: TypeProvenance): AbstractConstructor =
      new AbstractConstructor(absMths)(errType(prov))
    def unapply(ctor: AbstractConstructor): S[Set[Var]] = S(ctor.absMths)
  }
  
  /** A type without universally quantified type variables. */
  sealed abstract class SimpleType extends TypeScheme with SimpleTypeImpl {
    val prov: TypeProvenance
    def level: Int
    def instantiate(implicit lvl: Int) = this
    constructedTypes += 1
  }
  type ST = SimpleType
  
  sealed abstract class BaseTypeOrTag extends SimpleType
  sealed abstract class BaseType extends BaseTypeOrTag
  sealed abstract class MiscBaseType extends BaseType
  sealed trait Factorizable extends SimpleType
  
  case class FunctionType(lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends MiscBaseType {
    lazy val level: Int = lhs.level max rhs.level
    override def toString = s"($lhs -> $rhs)"
  }
  
  case class RecordType(fields: List[(Var, SimpleType)])(val prov: TypeProvenance) extends SimpleType {
    // TODO: assert no repeated fields
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    def toInter: SimpleType =
      fields.map(f => RecordType(f :: Nil)(prov)).foldLeft(TopType:SimpleType)(((l, r) => ComposedType(false, l, r)(noProv)))
    def mergeAllFields(fs: Iterable[Var -> SimpleType]): RecordType = {
      val res = mutable.SortedMap.empty[Var, SimpleType]
      fs.foreach(f => res.get(f._1) match {
        case N => res(f._1) = f._2
        case S(ty) => res(f._1) = ty & f._2
      })
      RecordType(res.toList)(prov)
    }
    def addFields(fs: Ls[Var -> SimpleType]): RecordType = {
      val shadowing = fs.iterator.map(_._1).toSet
      RecordType(fields.filterNot(f => shadowing(f._1)) ++ fs)(prov)
    }
    def sorted: RecordType = RecordType(fields.sortBy(_._1))(prov)
    override def toString = s"{${fields.map(f => s"${f._1}: ${f._2}").mkString(", ")}}"
  }
  object RecordType {
    def empty: RecordType = RecordType(Nil)(noProv)
    def mk(fields: List[(Var, SimpleType)])(prov: TypeProvenance = noProv): SimpleType =
      if (fields.isEmpty) ExtrType(false)(prov) else RecordType(fields)(prov)
  }
  
  case class TupleType(fields: List[Opt[Var] -> SimpleType])(val prov: TypeProvenance) extends MiscBaseType {
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    lazy val toRecord: RecordType =
      RecordType(
        fields.zipWithIndex.map { case ((_, t), i) => (Var("_"+(i+1)), t) } ::: // TODO dedup fields!
        fields.collect { case (S(n), t) => (n, t) }
      )(prov)
    override def toString = s"(${fields.map(f => s"${f._1.fold("")(_.name+": ")}${f._2}").mkString(", ")})"
    // override def toString = s"(${fields.map(f => s"${f._1.fold("")(_+": ")}${f._2},").mkString(" ")})"
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
  
  /** Represents a type `base` from which we have removed the fields in `names`. */
  case class Without(base: SimpleType, names: Set[Var])(val prov: TypeProvenance) extends MiscBaseType {
    def level: Int = base.level
    override def toString = s"${base}\\${names.mkString("-")}"
  }
  
  /** A proxy type is a derived type form storing some additional information,
   * but which can always be converted into an underlying simple type. */
  sealed abstract class ProxyType extends SimpleType {
    def level: Int = underlying.level
    def underlying: SimpleType
    override def toString = s"[$underlying]"
  }
  object ProxyType {
    def unapply(proxy: ProxyType): S[ST] =
      S(proxy.underlying)
  }
  
  /** The sole purpose of ProvType is to store additional type provenance info. */
  case class ProvType(underlying: SimpleType)(val prov: TypeProvenance) extends ProxyType {
    // override def toString = s"$underlying[${prov.desc.take(5)}]"
    
    // TOOD override equals/hashCode? — could affect hash consing...
    // override def equals(that: Any): Bool = super.equals(that) || underlying.equals(that)
    // override def equals(that: Any): Bool = unwrapProxies.equals(that)
  }
  
  /** A proxy type, `S with {x: T; ...}` is equivalent to `S\x\... & {x: T; ...}`. */
  case class WithType(base: SimpleType, rcd: RecordType)(val prov: TypeProvenance) extends ProxyType {
    lazy val underlying: ST =
      base.without(rcd.fields.iterator.map(_._1).toSet) & rcd
  }
  
  case class TypeRef(defn: TypeName, targs: Ls[SimpleType])(val prov: TypeProvenance) extends SimpleType {
    def level: Int = targs.iterator.map(_.level).maxOption.getOrElse(0)
    def expand(implicit ctx: Ctx): SimpleType = expandWith(paramTags = true)
    def expandWith(paramTags: Bool)(implicit ctx: Ctx): SimpleType = {
      val td = ctx.tyDefs(defn.name)
      require(targs.size === td.tparamsargs.size)
      lazy val tparamTags =
        if (paramTags) RecordType.mk(td.tparamsargs.map { case (tp, tv) =>
          tparamField(defn, tp) -> FunctionType(tv, tv)(noProv) }.toList)(noProv)
        else TopType
      subst(td.kind match {
        case Als => td.bodyTy
        case Cls => clsNameToNomTag(td)(noProv/*TODO*/, ctx) & td.bodyTy & tparamTags
        case Trt => trtNameToNomTag(td)(noProv/*TODO*/, ctx) & td.bodyTy & tparamTags
      }, (td.targs.lazyZip(targs) ++ td.tvars.map(tv => tv -> freshenAbove(0, tv)(tv.level))).toMap)
    }
    override def toString = {
      val displayName =
        if (primitiveTypes.contains(defn.name)) defn.name.capitalize else defn.name
      if (targs.isEmpty) displayName else s"$displayName[${targs.mkString(",")}]"
    }
  }
  
  sealed trait ObjectTag extends BaseTypeOrTag with Ordered[ObjectTag] {
    val id: SimpleTerm
    def compare(that: ObjectTag): Int = this.id compare that.id
  }
  
  case class ClassTag(id: SimpleTerm, parents: Set[Var])(val prov: TypeProvenance) extends BaseType with ObjectTag {
    lazy val parentsST = parents.map(identity[SimpleTerm]) // TODO inefficient... improve
    def glb(that: ClassTag): Opt[ClassTag] =
      if (that.id === this.id) S(this)
      else if (that.parentsST.contains(this.id)) S(that)
      else if (this.parentsST.contains(that.id)) S(this)
      else N
    def lub(that: ClassTag): Set[ClassTag] = // TODO rm? it's unused
      if (that.id === this.id) Set.single(that)
      else if (that.parentsST.contains(this.id)) Set.single(this)
      else if (this.parentsST.contains(that.id)) Set.single(that)
      // else this.parentsST.union(that.parentsST)
      else Set(this, that)
    def level: Int = 0
    override def toString = id.idStr+s"<${parents.mkString(",")}>"
  }
  
  case class TraitTag(id: SimpleTerm)(val prov: TypeProvenance) extends BaseTypeOrTag with ObjectTag with Factorizable {
    def level: Int = 0
    override def toString = id.idStr
  }
  
  /** `TypeBounds(lb, ub)` represents an unknown type between bounds `lb` and `ub`.
   * The only way to give something such a type is to make the type part of a def or method signature,
   * as it will be replaced by a fresh bounded type variable upon subsumption checking (cf rigidification). */
  case class TypeBounds(lb: SimpleType, ub: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Int = lb.level max ub.level
    override def toString = s"$lb..$ub"
  }
  object TypeBounds {
    def mk(lb: SimpleType, ub: SimpleType, prov: TypeProvenance = noProv)(implicit ctx: Ctx): SimpleType =
      if ((lb is ub) || lb === ub || lb <:< ub && ub <:< lb) lb else TypeBounds(lb, ub)(prov)
  }
  
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
   *  Invariant: Types appearing in the bounds never have a level higher than this variable's `level`. */
  final class TypeVariable(
      val level: Int,
      var lowerBounds: List[SimpleType],
      var upperBounds: List[SimpleType],
      val nameHint: Opt[Str] = N
  )(val prov: TypeProvenance) extends SimpleType with CompactTypeOrVariable with Ordered[TypeVariable] with Factorizable {
    private[mlscript] val uid: Int = { freshCount += 1; freshCount - 1 }
    lazy val asTypeVar = new TypeVar(L(uid), nameHint)
    def compare(that: TV): Int = this.uid compare that.uid
    override def toString: String = nameHint.getOrElse("α") + uid + "'" * level
    override def hashCode: Int = uid
  }
  type TV = TypeVariable
  private var freshCount = 0
  def freshVar(p: TypeProvenance, nameHint: Opt[Str] = N, lbs: Ls[ST] = Nil, ubs: Ls[ST] = Nil)
        (implicit lvl: Int): TypeVariable =
    new TypeVariable(lvl, lbs, ubs, nameHint)(p)
  def resetState(): Unit = {
    freshCount = 0
  }
  trait CompactTypeOrVariable
  type PolarVariable = (TypeVariable, Boolean)
  
  case class NegVar(tv: TV) extends ProxyType with Factorizable {
    lazy val underlying: SimpleType = tv.neg()
    val prov = noProv
  }
  case class NegTrait(tt: TraitTag) extends ProxyType with Factorizable {
    lazy val underlying: SimpleType = tt.neg()
    val prov = noProv
  }
  
}
