package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer, LinkedHashMap}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

abstract class TyperDatatypes extends TyperHelpers { Typer: Typer =>
  def recordTypeVars: Bool = false
  
  type TN = TypeName
  val TN: TypeName.type = TypeName
  
  
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
  
  
  case class VarSymbol(ty: ST, definingVar: Var) extends TypeInfo
  
  
  /** Some type information which may not yet be available. */
  sealed abstract class LazyTypeInfo extends TypeInfo {
    def complete()(implicit raise: Raise): NuMember
    def kind: DeclKind
    def name: Str
  }
  
  /** A LazyTypeInfo whose typing has been completed. */
  case class CompletedTypeInfo(member: NuMember) extends LazyTypeInfo {
    def complete()(implicit raise: Raise): NuMember = member
    def kind: DeclKind = member.kind
    val name: Str = member.name
  }
  
  /** Initialized lazy type information, to be computed soon. */
  class DelayedTypeInfo(val decl: NuDecl, val outerVars: Map[Str, SimpleType])
          (implicit val ctx: Ctx, val raise: Raise) extends LazyTypeInfo with DelayedTypeInfoImpl
  object DelayedTypeInfo {
    def unapply(dti: DelayedTypeInfo): S[NuDecl] =
      S(dti.decl)
  }
  
  /** A type with universally quantified type variables
    * (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(polymLevel: Level, body: SimpleType) // TODO add own type provenance for consistency
      extends SimpleType with PolymorphicTypeImpl {
    require(polymLevel < MaxLevel, polymLevel)
    val prov: TypeProvenance = body.prov
    lazy val level = levelBelow(polymLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = body.levelBelow(ub min polymLevel)
    override def toString = s"‹∀ $polymLevel. $body›"
  }
  object PolymorphicType {
    def mk(polymLevel: Level, body: SimpleType): SimpleType = {
      require(polymLevel <= MaxLevel)
      if (polymLevel === MaxLevel || body.level <= polymLevel) body
      else body.unwrapProvs match { // Q: unwrap other proxies?
        case PolymorphicType(lvl, bod) => PolymorphicType.mk(polymLevel min lvl, bod)
        
        // * Not very helpful (also seems to result in breaking some recursive types... not sure why):
        // case tv @ AssignedVariable(ty) =>
        //   PolymorphicType(polymLevel, ty)
        // case tv: TV if tv.level > polymLevel && tv.assignedTo.isEmpty =>
        //   PolymorphicType(polymLevel, tv.lowerBounds.foldLeft(BotType: ST)(_ | _))
        
        case _ => PolymorphicType(polymLevel, body)
      }
    }
  }
  object SplittablePolyFun {
    def unapply(pt: PolymorphicType)(implicit ctx: Ctx, raise: Raise, shadows: Shadows): Opt[ST] =
      if (distributeForalls) pt.splitFunction
      else N
  }
  
  /** A list of constraints. */
  type Constrs = List[ST -> ST]
  
  case class ConstrainedType(constraints: Constrs, body: ST) extends SimpleType { // TODO add own prov?
    val prov: TypeProvenance = body.prov
    lazy val level =
      children(false).iterator.map(_.level).max
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      children(false).iterator.map(_.levelBelow(ub)).max
    override def toString: Str =
      s"{$body where: ${constraints.map {
        case (lb, ub) => s"$lb <: $ub"
      }.mkString(", ")}}"
  }
  object ConstrainedType {
    def mk(constraints: Constrs, body: ST): ST =
      if (constraints.isEmpty) body
      else ConstrainedType(constraints, body)
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
    level: Level,
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
      body.fold(PolymorphicType(MinLevel, errType))(b => PolymorphicType(level, FunctionType(singleTup(b._1), b._2)(prov)))
    val bodyPT: PolymorphicType =
      body.fold(PolymorphicType(MinLevel, errType))(b => PolymorphicType(level, ProvType(b._2)(prov)))
  }
  
  sealed abstract class TypeLike extends TypeLikeImpl {
    def unwrapProvs: TypeLike
  }
  type TL = TypeLike
  
  abstract class OtherTypeLike extends TypeLike { this: TypedTypingUnit =>
    def self: TypedTypingUnit = this
    def unwrapProvs: TypeLike = this
  }
  object OtherTypeLike {
    def unapply(ot: OtherTypeLike): S[TypedTypingUnit] = S(ot.self)
  }
  
  /** A general type form (TODO: rename to AnyType). */
  sealed abstract class SimpleType extends TypeLike with SimpleTypeImpl {
    val prov: TypeProvenance
    def level: Level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level
    def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): SimpleType =
      Typer.freshenAbove(lim, this, rigidify)
    constructedTypes += 1
  }
  type ST = SimpleType
  
  sealed abstract class BaseTypeOrTag extends SimpleType
  sealed abstract class BaseType extends BaseTypeOrTag {
    def compareEquiv(that: BaseType): Int = (this, that) match {
      case (a: TypeTag, b: TypeTag) => a.compare(b)
      case (a: TypeTag, _) => -1
      case (_, b: TypeTag) => 1
      case (_: FunctionType, _: FunctionType) => 0
      case (_: FunctionType, _) => -1
      case (_, _: FunctionType) => 1
      case (_: ArrayType, _: ArrayType) => 0
      case (_: ArrayType, _) => -1
      case (_, _: ArrayType) => 1
      case (_: TupleType, _: TupleType) => 0
      case (_: TupleType, _) => -1
      case (_, _: TupleType) => 1
      case (_: Without, _: Without) => 0
      case (_: Without, _) => -1
      case (_, _: Without) => 1
      case (_: Overload, _: Overload) => 0
      case (_: Overload, _) => -1
      case (_, _: Overload) => 1
      case (_: SpliceType, _: SpliceType) => 0
    }
    def toRecord: RecordType = RecordType.empty
    protected def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): BaseType
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): BaseType =
      freshenAboveImpl(lim, rigidify)
  }
  sealed abstract class MiscBaseType extends BaseType {
    override def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): MiscBaseType
  }
  sealed trait Factorizable extends SimpleType
  
  type FT = FunctionType
  
  case class FunctionType(lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends MiscBaseType {
    lazy val level: Int = lhs.level max rhs.level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = lhs.levelBelow(ub) max rhs.levelBelow(ub)
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): FunctionType =
      FunctionType(lhs.freshenAbove(lim, rigidify), rhs.freshenAbove(lim, rigidify))(prov)
    override def toString = s"(${lhs match {
      case TupleType((N, FieldType(N, f: TupleType)) :: Nil) => "[" + f.showInner + "]"
      case TupleType((N, f) :: Nil) => f.toString
      case lhs => lhs
    }} -> $rhs)"
  }
  
  case class Overload(alts: Ls[FunctionType])(val prov: TypeProvenance) extends MiscBaseType {
    require(alts.lengthIs > 0)
    def mapAlts(lf: ST => ST)(rf: ST => ST): Overload =
      Overload(alts.map(ft => FunctionType(lf(ft.lhs), rf(ft.rhs))(ft.prov)))(prov)
    def mapAltsPol(pol: Opt[Bool])(f: (Opt[Bool], SimpleType) => SimpleType): Overload =
      Overload(alts.map(ft => FunctionType(f(pol.map(!_), ft.lhs), f(pol, ft.rhs))(ft.prov)))(prov)
    def mapAltsPol(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType): Overload =
      Overload(alts.map(ft => FunctionType(f(pol.contravar, ft.lhs), f(pol, ft.rhs))(ft.prov)))(prov)
    def approximatePos: FunctionType = {
      val (lhss, rhss) = alts.map(ft => ft.lhs -> ft.rhs).unzip
      FunctionType(lhss.reduce(_ | _), rhss.reduce(_ | _))(prov)
      // * Note: technically the following is another valid (but probably less useful)
      // * approximation of the same function type:
      // FunctionType(lhss.reduce(_ & _), rhss.reduce(_ & _))(prov)
    }
    lazy val level: Level = levelBelow(MaxLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      alts.iterator.map(_.levelBelow(ub)).max
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): Overload =
      Overload(alts.map(_.freshenAboveImpl(lim, rigidify)))(prov)
  }
  object Overload {
    def mk(alts: Ls[FunctionType])(prov: TypeProvenance): ST = alts match {
      case Nil => mkProxy(TopType, prov)
      case ft :: Nil => mkProxy(ft, prov)
      case alts => Overload(alts)(prov)
    }
  }
  
  case class RecordType(fields: List[(Var, FieldType)])(val prov: TypeProvenance) extends SimpleType {
    // TODO: assert no repeated fields
    lazy val level: Level = levelBelow(MaxLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = fields.iterator.map(_._2.levelBelow(ub)).maxOption.getOrElse(MinLevel)
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): RecordType =
      Typer.mapPol(this, N, false)((_, x) => x.freshenAbove(lim, rigidify))
    def toInter: SimpleType =
      fields.map(f => RecordType(f :: Nil)(prov)).foldLeft(TopType: ST)(((l, r) => ComposedType(false, l, r)(noProv)))
    def mergeAllFields(fs: Iterable[Var -> FieldType]): RecordType = {
      val res = mutable.SortedMap.empty[Var, FieldType]
      fs.foreach(f => res.get(f._1) match {
        case N => res(f._1) = f._2
        case S(ty) => res(f._1) = ty && f._2
      })
      RecordType(res.toList)(prov)
    }
    def addFields(fs: Ls[Var -> FieldType]): RecordType = {
      val shadowing = fs.iterator.map(_._1).toSet
      RecordType(fields.filterNot(f => shadowing(f._1)) ++ fs)(prov)
    }
    def sorted: RecordType = RecordType(fields.sortBy(_._1))(prov)
    override def toString = s"{${fields.map(f => s"${f._1.name}: ${f._2}").mkString(", ")}}"
  }
  object RecordType {
    def empty: RecordType = RecordType(Nil)(noProv)
    def mk(fields: List[(Var, FieldType)])(prov: TypeProvenance = noProv): SimpleType =
      if (fields.isEmpty) ExtrType(false)(prov) else RecordType(fields)(prov)
  }
  
  sealed abstract class ArrayBase extends MiscBaseType {
    def inner: FieldType
  }
  
  case class ArrayType(val inner: FieldType)(val prov: TypeProvenance) extends ArrayBase {
    def level: Level = inner.level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = inner.levelBelow(ub)
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): ArrayType =
      ArrayType(inner.freshenAbove(lim, rigidify))(prov)
    override def toString = s"Array‹$inner›"
  }
  
  case class TupleType(fields: List[Opt[Var] -> FieldType])(val prov: TypeProvenance) extends ArrayBase {
    lazy val inner: FieldType = fields.map(_._2).reduceLeftOption(_ || _).getOrElse(BotType.toUpper(noProv))
    lazy val level: Level = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = fields.iterator.map(_._2.levelBelow(ub)).maxOption.getOrElse(MinLevel)
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): TupleType =
      TupleType(fields.mapValues(_.freshenAbove(lim, rigidify)))(prov)
    lazy val toArray: ArrayType = ArrayType(inner)(prov)  // upcast to array
    override lazy val toRecord: RecordType =
      RecordType(
        fields.zipWithIndex.map { case ((_, t), i) => (Var(i.toString), t) }
        // Note: In line with TypeScript, tuple field names are pure type system fictions,
        //    with no runtime existence. Therefore, they should not be included in the record type
        //    corresponding to this tuple type.
        //    i.e., no `::: fields.collect { case (S(n), t) => (n, t) }`
      )(prov)
    def showInner: Str =
      fields.map(f => s"${f._1.fold("")(_.name+": ")}${f._2},").mkString(" ")
    override def toString = s"($showInner)"
    // override def toString = s"(${fields.map(f => s"${f._1.fold("")(_+": ")}${f._2},").mkString(" ")})"
  }

  case class SpliceType(elems: Ls[Either[SimpleType, FieldType]])(val prov: TypeProvenance) extends ArrayBase {
    require(elems.nonEmpty) // ? – since `max` is used below...
    lazy val level: Int = elems.map{ case L(l) => l.level case R(r) => r.level }.max
    
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV,ST]): MiscBaseType =
      SpliceType(elems.map{ case L(l) => L(l.freshenAbove(lim, rigidify)) case R(r) => R(r.freshenAbove(lim, rigidify)) })(prov)
    
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      elems.map{ case L(l) => l.levelBelow(ub) case R(r) => r.levelBelow(ub) }.max
    
    lazy val inner: FieldType = elems.map {
      case L(l) => l match { case a: ArrayBase => a.inner case _ => ??? }
      case R(r) => r
    }.reduceLeft(_ || _)

    def updateElems(f: SimpleType => SimpleType, g: SimpleType => SimpleType, 
      h: SimpleType => SimpleType,newProv: TypeProvenance = prov): SpliceType =
      SpliceType(elems.map{case L(l) => L(f(l)) case R(r) => R(r.update(g, h))})(newProv)
  }
  
  /** Polarity `pol` being `true` means Bot; `false` means Top. These are extrema of the subtyping lattice. */
  case class ExtrType(pol: Bool)(val prov: TypeProvenance) extends SimpleType {
    def level: Level = MinLevel
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = MinLevel
    override def toString = if (pol) "⊥" else "⊤"
  }
  
  /** Represents a type variable skolem that was extruded outsdie its polym level.
    * The goal is to retain precise information to produce good errors,
    * but still have this be functionally equivalent to `ExtrType(pol)`. */
  case class Extruded(pol: Bool, underlying: SkolemTag)(val prov: TypeProvenance, val reason: Ls[Ls[ST]]) extends AbstractTag with TypeVarOrRigidVar {
    val level: Level = MinLevel
    val id = underlying.id
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = 0
    override def toString = if (pol) s"⊥(${underlying})" else s"⊤(${underlying})"
  }
  
  /** Polarity `pol` being `true` means union; `false` means intersection. */
  case class ComposedType(pol: Bool, lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Level = lhs.level max rhs.level
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
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): Without =
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
    // override def toString = s"$underlying@${prov.loco.fold("?")(l => l.spanStart+"–"+l.spanEnd)}"
    // override def toString = showProvOver(true)(""+underlying)
    
    // TOOD override equals/hashCode? — could affect hash consing...
    // override def equals(that: Any): Bool = super.equals(that) || underlying.equals(that)
    // override def equals(that: Any): Bool = unwrapProxies.equals(that)
  }
  
  /** A proxy type, `S with {x: T; ...}` is equivalent to `S\x\... & {x: T; ...}`. */
  case class WithType(base: SimpleType, rcd: RecordType)(val prov: TypeProvenance) extends ProxyType {
    lazy val underlying: ST =
      base.without(rcd.fields.iterator.map(_._1).toSortedSet) & rcd
    override def toString = s"${base} w/ ${rcd}"
  }
  
  type TR = TypeRef
  val TR: TypeRef.type = TypeRef
  case class TypeRef(defn: TypeName, targs: Ls[SimpleType])(val prov: TypeProvenance) extends SimpleType with TypeRefImpl {
    def level: Level = targs.iterator.map(_.level).maxOption.getOrElse(MinLevel)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = targs.iterator.map(_.levelBelow(ub)).maxOption.getOrElse(MinLevel)
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): TypeRef =
      TypeRef(defn, targs.map(_.freshenAbove(lim, rigidify)))(prov)
    override def toString = showProvOver(false) {
      val displayName =
        if (primitiveTypes.contains(defn.name)) defn.name.capitalize else defn.name
      if (targs.isEmpty) displayName else s"$displayName[${targs.mkString(",")}]"
    }
  }
  
  sealed trait TypeTag extends BaseTypeOrTag with Ordered[TypeTag] {
    val id: IdentifiedTerm
    def compare(that: TypeTag): Int = (this, that) match {
      case (obj1: ObjectTag, obj2: ObjectTag) => obj1.id compare obj2.id
      case (SkolemTag(id1), SkolemTag(id2)) => id1 compare id2
      case (Extruded(_, id1), Extruded(_, id2)) => id1 compare id2
      case (_: ObjectTag, _: SkolemTag | _: Extruded) => -1
      case (_: SkolemTag | _: Extruded, _: ObjectTag) => 1
      case (_: SkolemTag, _: Extruded) => -1
      case (_: Extruded, _: SkolemTag) => 1
    }
  }
  
  case class ClassTag(id: SimpleTerm, parents: Set[TypeName])(val prov: TypeProvenance)
      extends BaseType with TypeTag with ObjectTag {
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
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): this.type = this
  }
  
  sealed trait TypeVarOrRigidVar extends SimpleType
  
  sealed trait ObjectTag extends TypeTag {
    val id: SimpleTerm
    val parents: Set[TypeName]
    lazy val parentsST = parents.iterator.map(tn => Var(tn.name)).toSet[IdentifiedTerm]
    override def toString = "#" + showProvOver(false)(id.idStr+s"<${parents.map(_.name).mkString(",")}>")
  }
  
  sealed abstract class AbstractTag extends BaseTypeOrTag with TypeTag with Factorizable
  
  case class TraitTag(id: Var, parents: Set[TypeName])(val prov: TypeProvenance) extends AbstractTag with ObjectTag {
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = MinLevel
    def level: Level = MinLevel
  }
  
  case class SkolemTag(id: TV)(val prov: TypeProvenance) extends AbstractTag with TypeVarOrRigidVar {
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      id.levelBelow(ub)
    val level: Level = id.level
    override def toString = {
      val str = id.mkStr
      // (if (id.idStr.startsWith("'")) "‘"+id.idStr.tail else id.idStr) + showLevel(level)
      "‘"+(if (str.startsWith("'")) str.tail else str) + (if (str.last==='\'') "_" else "") + showLevel(level)
    }
  }
  
  /** `TypeBounds(lb, ub)` represents an unknown type between bounds `lb` and `ub`.
    * The only way to give something such a type is to make the type part of a def or method signature,
    * as it will be replaced by a fresh bounded type variable upon subsumption checking (cf rigidification). */
  case class TypeBounds(lb: SimpleType, ub: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Level = lb.level max ub.level
    def levelBelow(ubLvl: Level)(implicit cache: MutSet[TV]): Int = lb.levelBelow(ubLvl) max ub.levelBelow(ubLvl)
    override def toString = s"$lb..$ub"
  }
  object TypeBounds {
    final def mkSimple(lb: SimpleType, ub: SimpleType, prov: TypeProvenance = noProv): SimpleType = (lb, ub) match {
      case (TypeBounds(lb, _), ub) => mkSimple(lb, ub, prov)
      case (lb, TypeBounds(_, ub)) => mkSimple(lb, ub, prov)
      case _ => TypeBounds(lb, ub)(prov)
    }
    final def mk(lb: SimpleType, ub: SimpleType, prov: TypeProvenance = noProv)(implicit ctx: Ctx): SimpleType =
      if ((lb is ub)
        || lb === ub
        || !lb.mentionsTypeBounds && !ub.mentionsTypeBounds && lb <:< ub && ub <:< lb
      ) lb else (lb, ub) match {
        case _ => mkSimple(lb, ub, prov)
      }
    /** A version of `mk` that does not check for subtyping,
      * to be used in type simplification code which modifies subtype bounds on the fly
      * (in particular, the `transform` function may replace TV bounds `TypeBound` bundles,
      * and creating these `TypeBound`s should NOT rely on the bounds still being there at the time
      * the bundle is constructed). */
    final def mkSafe(lb: SimpleType, ub: SimpleType, prov: TypeProvenance = noProv)(implicit ctx: Ctx): SimpleType =
      if ((lb is ub)
        || lb === ub
      ) lb else (lb, ub) match {
        case _ => mkSimple(lb, ub, prov)
      }
  }
  
  case class FieldType(lb: Option[SimpleType], ub: SimpleType)(val prov: TypeProvenance) {
    def level: Int = lb.map(_.level).getOrElse(ub.level) max ub.level
    def levelBelow(ubLvl: Level)(implicit cache: MutSet[TV]): Level =
      lb.fold(MinLevel)(_.levelBelow(ubLvl)) max ub.levelBelow(ubLvl)
    def <:< (that: FieldType)(implicit ctx: Ctx, cache: MutMap[ST -> ST, Bool] = MutMap.empty): Bool =
      (that.lb.getOrElse(BotType) <:< this.lb.getOrElse(BotType)) && (this.ub <:< that.ub)
    def && (that: FieldType, prov: TypeProvenance = noProv): FieldType =
      FieldType(lb.fold(that.lb)(l => Some(that.lb.fold(l)(l | _))), ub & that.ub)(prov)
    def || (that: FieldType, prov: TypeProvenance = noProv): FieldType =
      FieldType(for {l <- lb; r <- that.lb} yield (l & r), ub | that.ub)(prov)
    def update(lb: SimpleType => SimpleType, ub: SimpleType => SimpleType): FieldType =
      FieldType(this.lb.map(lb), ub(this.ub))(prov)
    def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): FieldType =
      update(_.freshenAbove(lim, rigidify), _.freshenAbove(lim, rigidify))
    override def toString =
      lb.fold(s"$ub")(lb => s"mut ${if (lb === BotType) "" else lb}..$ub")
  }
  object FieldType {
    def mk(vi: VarianceInfo, lb: ST, ub: ST)(prov: TP): FieldType = vi match {
      case VarianceInfo(true, true) => FieldType(N, TopType)(prov)
      case VarianceInfo(true, false) => FieldType(N, ub)(prov)
      case VarianceInfo(false, true) => FieldType(S(lb), TopType)(prov)
      case VarianceInfo(false, false) => FieldType(S(lb), ub)(prov)
    }
  }
  
  val createdTypeVars: Buffer[TV] = Buffer.empty
  
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
    * Invariant: Types appearing in the bounds never have a level higher than this variable's `level`. */
  final class TypeVariable(
      val level: Level,
      var _lowerBounds: List[SimpleType],
      var _upperBounds: List[SimpleType],
      originalTV: Opt[TV],
      val nameHint: Opt[Str] = N,
      val recPlaceholder: Bool = false
    )(val prov: TypeProvenance)
    extends SimpleType
      with TypeVarOrRigidVar
      with Ordered[TypeVariable]
      with Factorizable
      with IdentifiedTerm
  {
    require(level <= MaxLevel)
    
    if (recordTypeVars) createdTypeVars += this
    
    // var assignedTo: Opt[ST] = N
    private var _assignedTo: Opt[ST] = N
    def assignedTo: Opt[ST] = _assignedTo
    def assignedTo_=(value: Opt[ST]): Unit = {
      require(value.forall(_.level <= level))
      _assignedTo = value
    }

    val tsc: LinkedHashMap[TupleSetConstraints, Set[Int]] = LinkedHashMap.empty
    
    // * Bounds should always be disregarded when `equatedTo` is defined, as they are then irrelevant:
    def lowerBounds: List[SimpleType] = { require(assignedTo.isEmpty, this); _lowerBounds }
    def upperBounds: List[SimpleType] = { require(assignedTo.isEmpty, this); _upperBounds }
    def lowerBounds_=(bs: Ls[ST]): Unit = { require(assignedTo.isEmpty, this); _lowerBounds = bs }
    def upperBounds_=(bs: Ls[ST]): Unit = { require(assignedTo.isEmpty, this); _upperBounds = bs }
    
    private val creationRun = currentConstrainingRun
    def original: TV =
      if (currentConstrainingRun === creationRun) originalTV.getOrElse(this)
      else this
    private lazy val trueOriginal: Opt[TV] =
      originalTV.flatMap(_.trueOriginal.orElse(originalTV))
    
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      if (level <= ub) level else {
        if (cache(this)) MinLevel else {
          cache += this
          assignedTo match {
            case S(ty) =>
              ty.levelBelow(ub)
            case N =>
              (lowerBounds.iterator ++ upperBounds.iterator)
                .map(_.levelBelow(ub)).maxOption.getOrElse(MinLevel)
          }
        }
      }
    private[mlscript] val uid: Int = freshUid
    lazy val asTypeVar = new TypeVar(L(uid), nameHint)
    lazy val (asPosExtrudedTypeVar, asNegExtrudedTypeVar) = {
      val nme = S(ExtrusionPrefix+nameHint.getOrElse("_").dropWhile(_ === '\''))
      (new TypeVar(L(freshUid), nme), new TypeVar(L(freshUid), nme))
    }
    def compare(that: TV): Int = this.uid compare that.uid
    override def toString: String =
      (trueOriginal match {
        case S(to) =>
          assert(to.nameHint === nameHint, (to.nameHint, nameHint))
          to.mkStr + "_" + uid + showLevel(level)
        case N =>
          showProvOver(false)(mkStr + showLevel(level))
      }) + (if (assignedTo.isDefined) "#" else "")
    private[mlscript] def mkStr = nameHint.getOrElse("α") + uid
    
    // * `omitIrrelevantVars` omits top-level as well as quantified variable occurrences
    final def isRecursive_$(omitIrrelevantVars: Bool)(implicit ctx: Ctx) : Bool =
      isPosRecursive_$(omitIrrelevantVars) || isNegRecursive_$(omitIrrelevantVars)
    // * Variables occurring strictly negatively in their own lower bound
    // * (resp. strictly positively in their own upper bound, ie contravariantly)
    // * are NOT recursive, as these occurrences only demonstrate "spurious" cycles
    // * which are easily removed.
    final def isPosRecursive_$(omitIrrelevantVars: Bool)(implicit ctx: Ctx) : Bool = lbRecOccs_$(omitIrrelevantVars) match {
      case S(N | S(true)) => true
      case _ => false
    }
    final def isNegRecursive_$(omitIrrelevantVars: Bool)(implicit ctx: Ctx) : Bool = ubRecOccs_$(omitIrrelevantVars) match {
      case S(N | S(false)) => true
      case _ => false
    }
    /** None: not recursive in this bound; Some(Some(pol)): polarly-recursive; Some(None): nonpolarly-recursive.
      * Note that if we have something like 'a :> Bot <: 'a -> Top, 'a is not truly recursive
      *   and its bounds can actually be inlined.
      * Also note that unfortunately, contrary to whta I previously thought,
      * it is not sound to ignore quantified variables during the getVarsPol search.
      * indeed, we can be in freaky situations like in `ListBuild.mls`
      * where we have `'a :> Ls[('x, forall 'a. 'a)]`! */
    private[mlscript] final def lbRecOccs_$(omitIrrelevantVars: Bool)(implicit ctx: Ctx): Opt[Opt[Bool]] = {
      // println("+", this, assignedTo getOrElse lowerBounds)
      // assignedTo.getOrElse(TupleType(lowerBounds.map(N -> _.toUpper(noProv)))(noProv)).getVarsPol(PolMap.pos, ignoreTopLevelOccs = true).get(this)
      val bs = assignedTo.fold(lowerBounds)(_ :: Nil)
      bs.foldLeft(BotType: ST)(_ | _).getVarsPol(PolMap.pos,
        ignoreTopLevelOccs = omitIrrelevantVars,
        // ignoreQuantifiedVars = omitIrrelevantVars,
        ignoreQuantifiedVars = false,
      ).get(this)
    }
    private[mlscript] final def ubRecOccs_$(omitIrrelevantVars: Bool)(implicit ctx: Ctx): Opt[Opt[Bool]] ={
      // println("-", this, assignedTo getOrElse upperBounds)
      // assignedTo.getOrElse(TupleType(upperBounds.map(N -> _.toUpper(noProv)))(noProv)).getVarsPol(PolMap.posAtNeg, ignoreTopLevelOccs = true).get(this)
      val bs = assignedTo.fold(upperBounds)(_ :: Nil)
      bs.foldLeft(TopType: ST)(_ & _).getVarsPol(PolMap.posAtNeg,
        ignoreTopLevelOccs = omitIrrelevantVars,
        // ignoreQuantifiedVars = omitIrrelevantVars,
        ignoreQuantifiedVars = false,
      ).get(this)
        // .tap(r => println(s"= $r"))
    }
  }
  type TV = TypeVariable
  private var freshCount = 0
  private def freshUid: Int = { freshCount += 1; freshCount - 1 }
  def freshVar(p: TypeProvenance, original: Opt[TV], nameHint: Opt[Str] = N, lbs: Ls[ST] = Nil, ubs: Ls[ST] = Nil, recPlaceholder: Bool = false)
        (implicit lvl: Int): TypeVariable =
    new TypeVariable(lvl, lbs, ubs, original, nameHint, recPlaceholder)(p)
  def resetState(): Unit = {
    freshCount = 0
  }
  
  type PolarVariable = (TypeVariable, Boolean)
  
  object AssignedVariable {
    def unapply(tv: TV): Opt[ST] = tv.assignedTo
  }
  
  case class NegVar(tv: TV) extends ProxyType with Factorizable {
    lazy val underlying: SimpleType = tv.neg()
    val prov = noProv
  }
  case class NegAbsTag(tt: AbstractTag) extends ProxyType with Factorizable {
    lazy val underlying: SimpleType = tt.neg()
    val prov = noProv
  }

  class TupleSetConstraints(var constraints: Ls[Ls[ST]], var tvs: Ls[(Bool, ST)]) {
    def updateImpl(index: Int, bound: ST)(implicit raise: Raise, ctx: Ctx) : Unit = {
      val u0 = constraints.flatMap { c =>
        TupleSetConstraints.lcg(tvs(index)._1, bound, c(index)).map(tvs.zip(c)++_)
      }
      val u = u0.map { x =>
        x.groupMap(_._1)(_._2).map { case (u@(p,_),l) =>
          (u,l.reduce((x,y) => ComposedType(!p,x,y)(noProv)))
        }
      }
      if (!u.isEmpty) {
        tvs.values.map(_.unwrapProxies).foreach {
          case tv: TV => tv.tsc += this -> Set.empty
          case _ => ()
        }
        tvs = u.flatMap(_.keys).distinct
        constraints = tvs.map(x => u.map(_.getOrElse(x,if (x._1) TopType else BotType))).transpose
        tvs.values.map(_.unwrapProxies).zipWithIndex.foreach {
          case (tv: TV, i) => tv.tsc.updateWith(this)(_.map(_ + i).orElse(S(Set(i))))
          case _ => ()
        }
      } else {
        constraints = Nil
      }
    }
    def updateOn(index: Int, bound: ST)(implicit raise: Raise, ctx: Ctx) : Unit = {
      updateImpl(index, bound)
      println(s"TSC update: $tvs in $constraints")
    }
  }
  object TupleSetConstraints {
    def lcgField(pol: Bool, first: FieldType, rest: FieldType)(implicit ctx: Ctx)
        : Opt[Ls[(Bool, ST) -> ST]] = {
      for {
        ubm <- lcg(pol, first.ub, rest.ub)
        lbm <- {
          if (first.lb.isEmpty && rest.lb.isEmpty)
            S(Nil)
          else
            lcg(!pol, first.lb.getOrElse(BotType), rest.lb.getOrElse(BotType))
        }
      } yield {
        ubm ++ lbm
      }
    }
    def lcg(pol: Bool, first: ST, rest: ST)(implicit ctx: Ctx)
        : Opt[Ls[(Bool, ST) -> ST]] = (first.unwrapProxies, rest.unwrapProxies) match {
      case (a, ExtrType(p)) if p =/= pol => S(Nil)
      case (a, ComposedType(p,l,r)) if p =/= pol =>
        for {
          lm <- lcg(pol,a,l)
          rm <- lcg(pol,a,r)
        } yield {
          lm ++ rm
        }
      case (a: TV, b: TV) if a.compare(b) === 0 => S(Nil)
      case (a: TV, b) => S(List((pol, first) -> rest))
      case (a, b: TV) => S(List((pol, first) -> rest))
      case (a: FT, b: FT) => lcgFunction(pol, a, b)
      case (a: ArrayType, b: ArrayType) => lcgField(pol, a.inner, b.inner)
      case (a: TupleType, b: TupleType) if a.fields.sizeCompare(b.fields) === 0 =>
        val fs = a.fields.map(_._2).zip(b.fields.map(_._2)).map(u => lcgField(pol, u._1, u._2))
        if (!fs.contains(N)) {
          S(fs.flatten.reduce(_++_))
        } else N
      case (a: TupleType, b: RecordType) if pol => lcg(pol, a.toRecord, b)
      case (a: RecordType, b: RecordType) =>
        val default = FieldType(N, if (pol) TopType else BotType)(noProv)
        if (b.fields.map(_._1).forall(a.fields.map(_._1).contains)) {
          val u = a.fields.map {
            case (v, f) => lcgField(pol, f, b.fields.find(_._1 === v).fold(default)(_._2))
          }
          if (!u.contains(N)) {
            S(u.flatten.reduce(_++_))
          } else N
        } else N
      case (a, b) if a === b => S(Nil)
      case (a, b) =>
        val dnf = DNF.mk(MaxLevel, Nil, if (pol) a & b.neg() else b & a.neg(), true)
        if (dnf.isBot)
          S(Nil)
        else if (dnf.cs.forall(c => !(c.vars.isEmpty && c.nvars.isEmpty)))
          S(List((pol, first) -> rest))
        else N
    }
    def lcgFunction(pol: Bool, first: FT, rest: FT)(implicit ctx: Ctx)
        : Opt[Ls[(Bool, ST) -> ST]] = {
      for {
        lm <- lcg(!pol, first.lhs, rest.lhs)
        rm <- lcg(pol, first.rhs, rest.rhs)
      } yield {
        lm ++ rm
      }
    }
    def mk(ov: Overload, f: FT)(implicit raise: Raise, ctx: Ctx): Opt[TupleSetConstraints] = {
      val u = ov.alts.flatMap(lcgFunction(false, f, _)).map { x =>
        x.groupMap(_._1)(_._2).map { case (u@(p,_),l) =>
          (u,l.reduce((x,y) => ComposedType(!p,x,y)(noProv)))
        }
      }
      if (u.isEmpty) { return N }
      val tvs = u.flatMap(_.keys).distinct
      val m = tvs.map(x => u.map(_.getOrElse(x,if (x._1) TopType else BotType)))
      val tsc = new TupleSetConstraints(m.transpose, tvs)
      tvs.values.map(_.unwrapProxies).zipWithIndex.foreach {
        case (tv: TV, i) => tv.tsc.updateWith(tsc)(_.map(_ + i).orElse(S(Set(i))))
        case _ => ()
      }
      println(s"TSC mk: ${tsc.tvs} in ${tsc.constraints}")
      S(tsc)
    }
  }
}
