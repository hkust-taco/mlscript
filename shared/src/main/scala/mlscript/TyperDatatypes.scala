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
  
  case class TypeRef(defn: TypeDef, targs: Ls[SimpleType])
      (val prov: TypeProvenance, val ctx: Ctx) extends SimpleType {
    assert(targs.size === defn.tparams.size)
    def level: Int = targs.iterator.map(_.level).maxOption.getOrElse(0)
    def expand(implicit raise: Raise): SimpleType = expandWith(paramTags = true)
    def expandWith(paramTags: Bool)(implicit raise: Raise): SimpleType = {
      val body_ty = typeType(defn.body)(ctx, raise, vars = defn.tparams.map(_.name).zip(targs).toMap)
      lazy val tparamTags =
        if (paramTags) RecordType.mk(defn.tparams.lazyZip(targs).map((tp, tv) =>
          tparamField(defn.nme, tp) -> FunctionType(tv, tv)(noProv)).toList)(noProv)
        else TopType
      defn.kind match {
        case Als => body_ty
        case Cls => clsNameToNomTag(defn)(noProv/*TODO*/, ctx) & body_ty & tparamTags
        case Trt => trtNameToNomTag(defn)(noProv/*TODO*/, ctx) & body_ty & tparamTags
      }
    }
    override def toString = {
      val displayName =
        if (primitiveTypes.contains(defn.nme.name)) defn.nme.name.capitalize else defn.nme.name
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
    def mk(lb: SimpleType, ub: SimpleType, prov: TypeProvenance = noProv): SimpleType =
      if ((lb is ub) || lb === ub || lb <:< ub && ub <:< lb) lb else TypeBounds(lb, ub)(prov)
  }
  
  class Choice(possible: Array[Bool]) {
    private var correlated: List[Any/*TODO*/] = Nil
  }
  
  class ChoiceType
        (c: Choice, cases: Array[SimpleType], override val level: Int, var resolved: Opt[SimpleType])
        (val prov: TypeProvenance)
      extends ProxyType {
    
    // class ChoiceVariable ... // this can be referred to from the outside as ChoiceType#ChoiceVariable
    
    var unresolved: BoundedVariable = // TODO make this a proper ChoiceVariable subtype to special-case in type simplification and pretty-printing!
      new BoundedVariable(level, Nil, Nil, N)(prov) {
        override def addLowerBounds(bnd: SimpleType): Unit = {
          // TODO: try to exclude invalidated cases, updating the Choice's cases array
          //  When only one choice is left, update `resolved`;
          //    if no choices are left, raise an error.
          // TODO: find out a good thing to do in case the bound itself is a choice type
          //    – we probably want a way of correlating different choice types...
          // ...
          super.addLowerBounds(bnd)
        }
        override def addUpperBounds(bnd: SimpleType): Unit = {
          // ...
          super.addUpperBounds(bnd)
        }
      }
    
    def underlying: SimpleType = resolved.getOrElse(unresolved)
  }
  
  // TODO: when ready, remove this – rename TypeVariableImpl to TypeVariable; and correctly handle the different kinds of BoundedVariable everywhere
  type TypeVariable = BoundedVariable
  
  final class TypeVariableImpl (
      level: Int,
      lowerBounds: List[SimpleType],
      upperBounds: List[SimpleType],
      nameHint: Opt[Str] = N
  )(prov: TypeProvenance) extends BoundedVariable(level, lowerBounds, upperBounds, nameHint)(prov)
  
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
   *  Invariant: Types appearing in the bounds never have a level higher than this variable's `level`.
   *  Methods addLowerBounds and addUpperBounds should be the only entry point used to update
   *    a type variable's bounds. */
  sealed abstract class BoundedVariable(
      val level: Int,
      private var _lowerBounds: List[SimpleType],
      private var _upperBounds: List[SimpleType],
      val nameHint: Opt[Str]
  )(val prov: TypeProvenance) extends SimpleType with CompactTypeOrVariable with Ordered[BoundedVariable] with Factorizable {
    private[mlscript] val uid: Int = { freshCount += 1; freshCount - 1 }
    lazy val asTypeVar = new TypeVar(L(uid), nameHint)
    def compare(that: BoundedVariable): Int = this.uid compare that.uid
    def lowerBounds: List[SimpleType] = _lowerBounds
    def upperBounds: List[SimpleType] = _upperBounds
    def addLowerBounds(bnd: SimpleType): Unit = _lowerBounds ::= bnd
    def addUpperBounds(bnd: SimpleType): Unit = _upperBounds ::= bnd
    final def :>! (bnd: SimpleType): Unit = addLowerBounds(bnd)
    final def <:! (bnd: SimpleType): Unit = addUpperBounds(bnd)
    override def toString: String = nameHint.getOrElse("α") + uid + "'" * level
    override def hashCode: Int = uid
  }
  type TV = TypeVariable
  private var freshCount = 0
  def freshVar(p: TypeProvenance, nameHint: Opt[Str] = N, lbs: Ls[ST] = Nil, ubs: Ls[ST] = Nil)
        (implicit lvl: Int): TypeVariable =
    new TypeVariableImpl(lvl, lbs, ubs, nameHint)(p)
  /** Like `freshVar` but with a different parameter order... */
  def mkVar(lvl: Int, lbs: Ls[ST] = Nil, ubs: Ls[ST] = Nil, nameHint: Opt[Str] = N)
      (p: TypeProvenance): TypeVariableImpl =
    new TypeVariableImpl(lvl, lbs, ubs, nameHint)(p)
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
