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
  
  case class TypeProvenance(loco: Opt[Loc], desc: Str, originName: Opt[Str] = N, isType: Bool = false) {
    val isOrigin: Bool = originName.isDefined
    def & (that: TypeProvenance): TypeProvenance = this // arbitrary; maybe should do better
    override def toString: Str = (if (isOrigin) "o: " else "") + "‹"+loco.fold(desc)(desc+":"+_)+"›"
  }
  type TP = TypeProvenance

  sealed abstract class TypeInfo

  /** A type for abstract classes that is used to check and throw
   * errors if the abstract class is being instantiated */
  case class AbstractConstructor(absMths: Set[Var], isTraitWithMethods: Bool) extends TypeInfo
  
  /** A type that potentially contains universally quantified type variables,
    * and which can be isntantiated to a given level. */
  // sealed abstract class TypeScheme extends TypeInfo {
  //   def uninstantiatedBody: SimpleType
  //   def instantiate(implicit lvl: Int): SimpleType
  // }
  type TypeScheme = SimpleType
  
  /** A type with universally quantified type variables
   *  (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(polymLevel: Level, body: SimpleType) extends SimpleType { // TODO add own prov?
    require(polymLevel < MaxLevel, polymLevel)
    val prov: TypeProvenance = body.prov
    lazy val level = levelBelow(polymLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = body.levelBelow(ub min polymLevel)
    // def uninstantiatedBody: SimpleType
    // override 
    def instantiate(implicit lvl: Int): SimpleType = {
      // val res = freshenAbove(polymLevel, body)
      implicit val state: MutMap[TV, ST] = MutMap.empty
      val res = body.freshenAbove(polymLevel, rigidify = false)
      // println(s"INST  $this  ~>  $res")
      // println(s"  where  ${res.showBounds}")
      println(s"INST [${level}]   $this")
      println(s"  where  ${showBounds}")
      println(s"TO [${lvl}] ~>  $res")
      println(s"  where  ${res.showBounds}")
      res
    }
    // def rigidify(implicit lvl: Int): SimpleType = freshenAbove(level, body, rigidify = true)
    def rigidify(implicit lvl: Int): SimpleType = {
      implicit val state: MutMap[TV, ST] = MutMap.empty
      body.freshenAbove(level, rigidify = true)
    }
    override def toString = s"∀ $polymLevel. $body"
  }
  object PolymorphicType {
    def mk(polymLevel: Level, body: SimpleType): SimpleType = {
      require(polymLevel <= MaxLevel)
      if (polymLevel === MaxLevel) body
      else body match { // TODO see through proxies?
        case PolymorphicType(lvl, bod) => PolymorphicType(polymLevel min lvl, bod)
        case _ => PolymorphicType(polymLevel, body)
      }
    }
  }
  
  /** `body.get._1`: implicit `this` parameter
    * `body.get._2`: actual body of the method
    * `body` being `None` indicates an error:
    *   - when this MethodType is computed from `MethodSet#processInheritedMethods`,
    *     it means two or more parent classes defined or declared the method
    *     and the current class did not override it;
    *   - when this MethodType is obtained from the environment, it means the method is ambiguous,
    *     which happens when two or more unrelated classes define or declare a method with the same name.
    *     So note that in this case, it will have more than one parent.
    *   Note: This is some fairly brittle and error-prone logic, which would gain to be refactored.
    *     Especially aggravating is the fact that `toPT`/`bodyPT` return `errorType` when `body` is `None`,
    *     whereas this case should probably be checked and carefully considered in each call site.
    * `isInherited`: whether the method declaration comes from the intersection of multiple inherited declarations
   */
  case class MethodType(
    level: Int,
    body: Opt[(SimpleType, SimpleType)],
    parents: List[TypeName],
    isInherited: Bool,
  )(val prov: TypeProvenance) {
    def &(that: MethodType): MethodType = {
      require(this.level === that.level)
      MethodType(level, mergeOptions(this.body, that.body)((b1, b2) => (b1._1 & b2._1, b1._2 & b2._2)),
        (this.parents ::: that.parents).distinct, isInherited = true)(prov)
    }
    val toPT: PolymorphicType =
      body.fold(PolymorphicType(0, errType))(b => PolymorphicType(level, FunctionType(singleTup(b._1), b._2)(prov)))
    val bodyPT: PolymorphicType =
      body.fold(PolymorphicType(0, errType))(b => PolymorphicType(level, ProvType(b._2)(prov)))
  }
  
  /** A general type form (TODO: rename to AnyType). */
  sealed abstract class SimpleType extends TypeInfo with SimpleTypeImpl {
    val prov: TypeProvenance
    def level: Level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level
    // def freshenAbove(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): SimpleType
    def freshenAbove(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): SimpleType =
      self.freshenAbove(lim, this, rigidify)
    // def uninstantiatedBody: SimpleType = this
    // def instantiate(implicit lvl: Int) = this
    constructedTypes += 1
  }
  type ST = SimpleType
  
  sealed abstract class BaseTypeOrTag extends SimpleType
  sealed abstract class BaseType extends BaseTypeOrTag {
    def toRecord: RecordType = RecordType.empty
    // def freshenAbove(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): BaseType
    protected def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): BaseType
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): BaseType =
      freshenAboveImpl(lim, rigidify)
  }
  sealed abstract class MiscBaseType extends BaseType {
    // def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit lvl: Level): MiscBaseType = this match {
    //   case ArrayType(inner) => ArrayType(inner.freshenAbove(lim, rigidify))(prov)
    //   case TupleType(fields) => TupleType(fields.mapValues(_.freshenAbove(lim, rigidify)))(prov)
    // }
    protected def freshenAboveImplImpl(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): MiscBaseType
    override def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): MiscBaseType =
      freshenAboveImplImpl(lim, rigidify)
  }
  sealed trait Factorizable extends SimpleType
  
  case class FunctionType(lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends MiscBaseType {
    lazy val level: Level = levelBelow(MaxLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = lhs.levelBelow(ub) max rhs.levelBelow(ub)
    def freshenAboveImplImpl(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): FunctionType =
      FunctionType(lhs.freshenAbove(lim, rigidify), rhs.freshenAbove(lim, rigidify))(prov)
    override def toString = s"($lhs -> $rhs)"
  }
  case class Overload(alts: Ls[FunctionType])(val prov: TypeProvenance) extends MiscBaseType {
    require(alts.length > 1)
    def approximatePos = {
      val (lhss, rhss) = alts.map(ft => ft.lhs -> ft.rhs).unzip
      FunctionType(lhss.reduce(_ & _), rhss.reduce(_ | _))(prov)
    }
    lazy val level: Level = levelBelow(MaxLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      alts.iterator.map(_.levelBelow(ub)).max
    def freshenAboveImplImpl(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): Overload =
      Overload(alts.map(_.freshenAboveImplImpl(lim, rigidify)))(prov)
  }
  
  case class RecordType(fields: List[(Var, SimpleType)])(val prov: TypeProvenance) extends SimpleType {
    // TODO: assert no repeated fields
    lazy val level: Level = levelBelow(MaxLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = fields.iterator.map(_._2.levelBelow(ub)).maxOption.getOrElse(MinLevel)
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): RecordType =
      self.freshenAbove(lim, this, rigidify).asInstanceOf[RecordType]
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
  
  sealed abstract class ArrayBase extends MiscBaseType {
    def inner: SimpleType
  }
  
  case class ArrayType(val inner: SimpleType)(val prov: TypeProvenance) extends ArrayBase {
    def level: Level = inner.level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = inner.levelBelow(ub)
    def freshenAboveImplImpl(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): ArrayType =
      ArrayType(inner.freshenAbove(lim, rigidify))(prov)
    override def toString = s"Array[${inner}]"
  }
  
  case class TupleType(fields: List[Opt[Var] -> SimpleType])(val prov: TypeProvenance) extends ArrayBase {
    lazy val inner: SimpleType = fields.map(_._2).fold(ExtrType(true)(noProv))(_ | _)
    lazy val level: Level = levelBelow(MaxLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = fields.iterator.map(_._2.levelBelow(ub)).maxOption.getOrElse(MinLevel)
    def freshenAboveImplImpl(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): TupleType =
      TupleType(fields.mapValues(_.freshenAbove(lim, rigidify)))(prov)
    lazy val toArray: ArrayType = ArrayType(inner)(prov)  // upcast to array
    override lazy val toRecord: RecordType =
      RecordType(
        fields.zipWithIndex.map { case ((_, t), i) => (Var("_"+(i+1)), t) }
        // Note: In line with TypeScript, tuple field names are pure type system fictions,
        //    with no runtime existence. Therefore, they should not be included in the record type
        //    corresponding to this tuple type.
        //    i.e., no `::: fields.collect { case (S(n), t) => (n, t) }`
      )(prov)
    override def toString =
      s"(${fields.map(f => s"${f._1.fold("")(_.name+": ")}${f._2},").mkString(" ")})"
    // override def toString = s"(${fields.map(f => s"${f._1.fold("")(_+": ")}${f._2},").mkString(" ")})"
  }
  
  /** Polarity `pol` being `true` means Bot; `false` means Top. These are extrema of the subtyping lattice. */
  case class ExtrType(pol: Bool)(val prov: TypeProvenance) extends SimpleType {
    def level: Level = MinLevel
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = MinLevel
    override def toString = if (pol) "⊥" else "⊤"
  }
  /** Polarity `pol` being `true` means union; `false` means intersection. */
  case class ComposedType(pol: Bool, lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Level = levelBelow(MaxLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = lhs.levelBelow(ub) max rhs.levelBelow(ub)
    override def toString = s"($lhs ${if (pol) "|" else "&"} $rhs)"
  }
  case class NegType(negated: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Level = negated.level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = negated.levelBelow(ub)
    override def toString = s"~(${negated})"
  }
  
  /** Represents a type `base` from which we have removed the fields in `names`. */
  case class Without(base: SimpleType, names: SortedSet[Var])(val prov: TypeProvenance) extends MiscBaseType {
    def level: Int = base.level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = base.levelBelow(ub)
    def freshenAboveImplImpl(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): Without =
      Without(base.freshenAbove(lim, rigidify), names)(prov)
    override def toString = s"${base}\\${names.mkString("-")}"
  }
  
  /** A proxy type is a derived type form storing some additional information,
   * but which can always be converted into an underlying simple type. */
  sealed abstract class ProxyType extends SimpleType {
    def level: Level = underlying.level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = underlying.levelBelow(ub)
    def underlying: SimpleType
    override def toString = s"[$underlying]"
  }
  object ProxyType {
    def unapply(proxy: ProxyType): S[ST] =
      S(proxy.underlying)
  }
  
  /** The sole purpose of ProvType is to store additional type provenance info. */
  case class ProvType(underlying: SimpleType)(val prov: TypeProvenance) extends ProxyType {
    override def toString = s"$underlying"
    // override def toString = s"[$underlying]"
    // override def toString = s"$underlying[${prov.desc.take(5)}]"
    // override def toString = s"$underlying[${prov.toString.take(5)}]"
    // override def toString = s"$underlying@${prov}"
    // override def toString = showProvOver(true)(""+underlying)
    
    // TOOD override equals/hashCode? — could affect hash consing...
    // override def equals(that: Any): Bool = super.equals(that) || underlying.equals(that)
    // override def equals(that: Any): Bool = unwrapProxies.equals(that)
  }
  
  /** A proxy type, `S with {x: T; ...}` is equivalent to `S\x\... & {x: T; ...}`. */
  case class WithType(base: SimpleType, rcd: RecordType)(val prov: TypeProvenance) extends ProxyType {
    lazy val underlying: ST =
      base.without(rcd.fields.iterator.map(_._1).toSortedSet) & rcd
  }
  
  case class TypeRef(defn: TypeName, targs: Ls[SimpleType])(val prov: TypeProvenance) extends SimpleType {
    def level: Level = levelBelow(MaxLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = targs.iterator.map(_.levelBelow(ub)).maxOption.getOrElse(MinLevel)
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
      // }, (td.targs.lazyZip(targs) ++ td.tvars.map(tv => tv -> freshenAbove(0, tv)(tv.level))).toMap)
      // }, (td.targs.lazyZip(targs) ++ td.tvars.map(tv =>
      //   tv -> tv.freshenAbove(MinLevel, rigidify = false)(tv.level, MutMap.empty))).toMap)
      }, td.targs.lazyZip(targs).toMap)
    }
    override def toString = showProvOver(false) {
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
    def level: Level = MinLevel
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = MinLevel
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): this.type = this
    // override def freshenAbove(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): this.type = this
    override def toString = showProvOver(false)(id.idStr+s"<${parents.mkString(",")}>")
  }
  
  case class TraitTag(id: SimpleTerm)(val prov: TypeProvenance) extends BaseTypeOrTag with ObjectTag with Factorizable {
    def level: Level = MinLevel
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = MinLevel
    override def toString = id.idStr
  }
  
  /** `TypeBounds(lb, ub)` represents an unknown type between bounds `lb` and `ub`.
    * The only way to give something such a type is to make the type part of a def or method signature,
    * as it will be replaced by a fresh bounded type variable upon subsumption checking (cf rigidification). */
  case class TypeBounds(lb: SimpleType, ub: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Level = lb.level max ub.level
    def levelBelow(ubLvl: Level)(implicit cache: MutSet[TV]): Int = lb.levelBelow(ubLvl)(MutSet.empty) max ub.levelBelow(ubLvl)(MutSet.empty)
    override def toString = s"$lb..$ub"
  }
  object TypeBounds {
    def mk(lb: SimpleType, ub: SimpleType, prov: TypeProvenance = noProv)(implicit ctx: Ctx): SimpleType =
      if ((lb is ub) || lb === ub || lb <:< ub && ub <:< lb) lb else TypeBounds(lb, ub)(prov)
  }
  
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
    * Invariant: Types appearing in the bounds never have a level higher than this variable's `level`. */
  final class TypeVariable(
      val level: Level,
      var lowerBounds: List[SimpleType],
      var upperBounds: List[SimpleType],
      val nameHint: Opt[Str] = N
  )(val prov: TypeProvenance) extends SimpleType with CompactTypeOrVariable with Ordered[TypeVariable] with Factorizable {
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      if (cache(this)) MinLevel else {
        cache += this
        // (if (level <= ub) level else MinLevel) max
        //   (lowerBounds.iterator ++ upperBounds.iterator)
        //   .map(_.levelBelow(ub)).maxOption.getOrElse(MinLevel)
        if (level <= ub) level
        else
          (lowerBounds.iterator ++ upperBounds.iterator)
            .map(_.levelBelow(ub)).maxOption.getOrElse(MinLevel)
      }
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit lvl: Level, freshened: MutMap[TV, ST]): TV =
      self.freshenAbove(lim, this, rigidify).asInstanceOf[TV]
    private[mlscript] val uid: Int = { freshCount += 1; freshCount - 1 }
    lazy val asTypeVar = new TypeVar(L(uid), nameHint)
    def compare(that: TV): Int = this.uid compare that.uid
    override def toString: String = showProvOver(false)(nameHint.getOrElse("α") + uid + (if (level === MaxLevel) "^" else if (level > 5 ) "^" + level else "'" * level))
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
