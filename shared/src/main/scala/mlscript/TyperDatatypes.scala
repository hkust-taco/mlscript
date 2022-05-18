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
  sealed abstract class TypeScheme extends TypeInfo {
    def uninstantiatedBody: SimpleType
    def instantiate(implicit lvl: Int): SimpleType
  }
  
  /** A type with universally quantified type variables
    * (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(level: Int, body: SimpleType) extends TypeScheme {
    val prov: TypeProvenance = body.prov
    def uninstantiatedBody: SimpleType = body
    def instantiate(implicit lvl: Int): SimpleType = freshenAbove(level, body)
    def rigidify(implicit lvl: Int): SimpleType = freshenAbove(level, body, rigidify = true)
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
  
  /** A type without universally quantified type variables. */
  sealed abstract class SimpleType extends TypeScheme with SimpleTypeImpl {
    val prov: TypeProvenance
    def level: Int
    def uninstantiatedBody: SimpleType = this
    def instantiate(implicit lvl: Int) = this
    constructedTypes += 1
  }
  type ST = SimpleType
  
  sealed abstract class BaseTypeOrTag extends SimpleType
  sealed abstract class BaseType extends BaseTypeOrTag {
    def toRecord: RecordType = RecordType.empty
  }
  sealed abstract class MiscBaseType extends BaseType
  sealed trait Factorizable extends SimpleType
  
  case class FunctionType(lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends MiscBaseType {
    lazy val level: Int = lhs.level max rhs.level
    // override def toString = s"($lhs -> $rhs)"
    override def toString = s"(${lhs match {
      case TupleType((N, f) :: Nil) => f.toString
      case lhs => lhs.toString
    }} -> $rhs)"
  }
  
  case class RecordType(fields: List[(Var, FieldType)])(val prov: TypeProvenance) extends SimpleType {
    // TODO: assert no repeated fields
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    def toInter: SimpleType =
      fields.map(f => RecordType(f :: Nil)(prov)).foldLeft(TopType:SimpleType)(((l, r) => ComposedType(false, l, r)(noProv)))
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
    override def toString = s"{${fields.map(f => s"${f._1}: ${f._2}").mkString(", ")}}"
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
    def level: Int = inner.level
    override def toString = s"Array‹$inner›"
  }

  case class TupleType(fields: List[Opt[Var] -> FieldType])(val prov: TypeProvenance) extends ArrayBase {
    lazy val inner: FieldType = fields.map(_._2).reduceLeftOption(_ || _).getOrElse(BotType.toUpper(noProv))
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
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
  case class Without(base: SimpleType, names: SortedSet[Var])(val prov: TypeProvenance) extends MiscBaseType {
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
    override def toString = s"[$underlying]"
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
    override def toString = s"${base} w/ ${rcd}"
  }
  
  // /** A proxy type, `T as 'a` is equivalent to `['a -> (T as 'a))']T` and also `'a where 'a =:= T`. */
  // case class RecType(body: SimpleType, binding: TV)(val prov: TypeProvenance) extends ProxyType {
  //   lazy val underlying: ST =
  //     subst(body, Map.single(binding -> this))
  // }
  
  case class TypeRef(defn: TypeName, targs: Ls[SimpleType])(val prov: TypeProvenance) extends SimpleType {
    def level: Int = targs.iterator.map(_.level).maxOption.getOrElse(0)
    def expand(implicit ctx: Ctx): SimpleType = expandWith(paramTags = true)
    def expandWith(paramTags: Bool)(implicit ctx: Ctx): SimpleType = {
      val td = ctx.tyDefs(defn.name)
      require(targs.size === td.tparamsargs.size)
      lazy val tparamTags =
        if (paramTags) RecordType.mk(td.tparamsargs.map { case (tp, tv) =>
            tparamField(defn, tp) -> FieldType(Some(tv), tv)(prov)
          }.toList)(noProv)
        else TopType
      subst(td.kind match {
        case Als => td.bodyTy
        case Cls => clsNameToNomTag(td)(noProv/*TODO*/, ctx) & td.bodyTy & tparamTags
        case Trt => trtNameToNomTag(td)(noProv/*TODO*/, ctx) & td.bodyTy & tparamTags
      }, td.targs.lazyZip(targs).toMap)
    }
    private var tag: Opt[Opt[ClassTag]] = N
    def mkTag(implicit ctx: Ctx): Opt[ClassTag] = tag.getOrElse {
      val res = ctx.tyDefs.get(defn.name) match {
        case S(td @ TypeDef(Cls, _, _, _, _, _, _, _, _)) => S(clsNameToNomTag(td)(noProv, ctx))
        case _ => N
      }
      tag = S(res)
      res
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
    def level: Int = 0
    override def toString = showProvOver(false)(id.idStr+s"<${parents.mkString(",")}>")
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
    // def mk(lb: SimpleType, ub: SimpleType, prov: TypeProvenance = noProv)(implicit ctx: Ctx): SimpleType =
    //   if ((lb is ub) || lb === ub || lb <:< ub && ub <:< lb) lb else TypeBounds(lb, ub)(prov)
    def mk(lb: SimpleType, ub: SimpleType, prov: TypeProvenance = noProv)(implicit ctx: Ctx): SimpleType =
      if (lb <:< ub && ub <:< lb) lb else mk2(lb, ub, prov)
    def mk2(lb: SimpleType, ub: SimpleType, prov: TypeProvenance = noProv): SimpleType = (lb, ub) match {
      case (TypeBounds(lb, _), ub) => mk2(lb, ub, prov)
      case (lb, TypeBounds(_, ub)) => mk2(lb, ub, prov)
      case _ =>
        if ((lb is ub) || lb === ub) lb else TypeBounds(lb, ub)(prov)
    }
  }
  
  case class FieldType(lb: Option[SimpleType], ub: SimpleType)(val prov: TypeProvenance) {
    def level: Int = lb.map(_.level).getOrElse(ub.level) max ub.level
    def <:< (that: FieldType)(implicit ctx: Ctx): Bool =
      (that.lb.getOrElse(BotType) <:< this.lb.getOrElse(BotType)) && (this.ub <:< that.ub)
    def && (that: FieldType, prov: TypeProvenance = noProv): FieldType =
      FieldType(lb.fold(that.lb)(l => Some(that.lb.fold(l)(l | _))), ub & that.ub)(prov)
    def || (that: FieldType, prov: TypeProvenance = noProv): FieldType =
      FieldType(for {l <- lb; r <- that.lb} yield (l & r), ub | that.ub)(prov)
    def update(lb: SimpleType => SimpleType, ub: SimpleType => SimpleType): FieldType =
      FieldType(this.lb.map(lb), ub(this.ub))(prov)
    // override def toString = s"${lb.mkString}..$ub"
    // override def toString = lb.filterNot(_ === BotType).fold(ub.toString)(lb => s"$lb..$ub")
    override def toString = lb.filterNot(_ === BotType).fold(s"$ub")(lb => s"mut $lb..$ub")
  }
  
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
    * Invariant: Types appearing in the bounds never have a level higher than this variable's `level`. */
  final class TypeVariable(
      val level: Int,
      var lowerBounds: List[SimpleType],
      var upperBounds: List[SimpleType],
      val nameHint: Opt[Str] = N
  )(val prov: TypeProvenance) extends SimpleType with CompactTypeOrVariable with Ordered[TypeVariable] with Factorizable {
    private[mlscript] val uid: Int = { freshCount += 1; freshCount - 1 }
    lazy val asTypeVar = new TypeVar(L(uid), nameHint)
    def compare(that: TV): Int = this.uid compare that.uid
    override def toString: String = showProvOver(false)(nameHint.getOrElse("α") + uid + "'" * level)
    // /** None: not recursive; Some(true): linearly recursive; Some(false): nonlinearly recursive; */
    /** None: not recursive; Some(true): polarly-recursive; Some(false): nonpolarly-recursive; */
    // def isRecursive(implicit cache: MutMap[TV, Opt[Bool]]): Opt[Bool] = cache.getOrElse(this, {
    //   // // ???
    //   // S(false)
    //   // getVarsPol(S(true))(this) tap (r => println(s"isRecursive ${this} $r"))
    //   // val vars = getVarsPol(S(true))
    //   // val vars = (lowerBounds.iterator ++ upperBounds.iterator).foldLeft(TopType)(_ | _).getVarsPol(S(true))
    //   val vars = TupleType((lowerBounds.iterator ++ upperBounds.iterator).map(N -> _.toUpper(noProv)).toList)(noProv).getVarsPol(S(true))
    //   // println(s"isRecursive $vars ${vars.get(this)}")
    //   vars.get(this).map(_.isDefined)
    // })
    // def isBadlyRecursive(implicit cache: MutMap[TV, Opt[Bool]]): Opt[Bool] = cache.getOrElse(this, {
    //   // // ???
    //   // S(false)
    //   // getVarsPol(S(true))(this) tap (r => println(s"isRecursive ${this} $r"))
    //   // val vars = getVarsPol(S(true))
    //   // val vars = (lowerBounds.iterator ++ upperBounds.iterator).foldLeft(TopType)(_ | _).getVarsPol(S(true))
    //   // val vars = TupleType((lowerBounds.iterator.map(_.neg()) ++ upperBounds.iterator).map(N -> _.toUpper(noProv)).toList)(noProv).getVarsPol(S(true))
    //   val vars = TupleType((lowerBounds.iterator ++ upperBounds.iterator.map(_.neg())).map(N -> _.toUpper(noProv)).toList)(noProv).getVarsPol(S(true))
    //   println(s"isRecursive($this) = $vars  —  ${vars.get(this)}")
    //   vars.get(this).map(_.isDefined)
    // })
    def lbRecOccs = TupleType(lowerBounds.map(N -> _.toUpper(noProv)))(noProv).getVarsPol(S(true)).get(this)
    def ubRecOccs = TupleType(upperBounds.map(N -> _.toUpper(noProv)))(noProv).getVarsPol(S(false)).get(this)
    /** None: not recursive; Some(true): polarly-recursive; Some(false): nonpolarly-recursive; */
    def isBadlyRecursive_$: Opt[Bool] = {
      // val vars = TupleType((lowerBounds.iterator ++ upperBounds.iterator).map(N -> _.toUpper(noProv)).toList)(noProv).getVarsPol(S(true))
      // // println(s"isRecursive $vars ${vars.get(this)}")
      // vars.get(this).map(_.isDefined)
      val lvars = TupleType(lowerBounds.map(N -> _.toUpper(noProv)))(noProv).getVarsPol(S(true))
      val uvars = TupleType(upperBounds.map(N -> _.toUpper(noProv)))(noProv).getVarsPol(S(false))
      val locc = lvars.get(this)
      val uocc = uvars.get(this)
      // println(s"C ${cache.contains(this)} $cache")
      println(s"isBadlyRecursive($this) = $locc $uocc")
      if (locc.isDefined || uocc.isDefined) S(!(
        
        // // locc.exists(_.forall(_ === false)) && uocc.exists(_.isDefined) ||
        // // uocc.exists(_.forall(_ === true)) && locc.exists(_.isDefined)
        // locc.exists(_.forall(_ === false)) /* && uocc.isDefined */ ||
        // // uocc.exists(_.forall(_ === true)) /* && locc.isDefined */
        // uocc.exists(_.forall(_ === true)) /* && locc.isDefined */
        
        locc.exists(_.forall(_ === false)) && uocc.isDefined ||
        uocc.exists(_.forall(_ === true)) && locc.isDefined
        
        // locc.exists(_.isEmpty) || uocc.exists(_.isEmpty) ||
        //   locc.exists(_.forall(_ === false)) && uocc.isDefined ||
        //   uocc.exists(_.forall(_ === true)) && locc.isDefined
        
      ))
      else N
    }
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
