package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

abstract class TyperDatatypes extends TyperHelpers { self: Typer =>
  
  type TN = TypeName
  
  
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
  
  // TODO rm level? already in ctx
  class LazyTypeInfo(val level: Int, val decl: NuDecl)(implicit ctx: Ctx, vars: Map[Str, SimpleType]) extends TypeInfo {
  // class LazyTypeInfo[A](level: Int, decl: NuDecl) extends TypeInfo {
    private def outerCtx = ctx
    private def outerVars = vars
    val tparams: Ls[TN -> TV] = Nil // TODO
    var isComputing: Bool = false // TODO replace by a Ctx entry
    var result: Opt[TypedNuTermDef] = N
    // var result: Opt[A] = N
    
    val tv: TV = freshVar(
      TypeProvenance(decl.toLoc, decl.describe, S(decl.name), decl.isInstanceOf[NuTypeDef]),
      N,
      S(decl.name))(level)
    
    def map(f: TypedNuTermDef => TypedNuTermDef): LazyTypeInfo = {
      val res = new LazyTypeInfo(level, decl)
      // if (result.nonEmpty) res.result = res
      res.result = result.map(f)
      res
    }
    
    // TODO does this also need freshening in freshenAbove?
    private lazy val thisTV: TV =
      freshVar(noProv/*FIXME*/, N, S("this"))(lvl + 1)
    
    def complete()(implicit raise: Raise): TypedNuTermDef = result.getOrElse {
      if (isComputing) lastWords(s"TODO cyclic defition ${decl.name}")
      else trace(s"Completing ${decl}") {
        // var res: ST = errType
        val res = try {
          isComputing = true
          // res = 
          decl match {
            case fd: NuFunDef =>
              // assert(fd.isLetRec.isEmpty, fd.isLetRec)
              implicit val prov: TP = noProv // TODO
              val res_ty = fd.rhs match {
                case R(PolyType(tps, ty)) =>
                  // val body_ty = typeType(ty)(ctx.nextLevel, raise,
                  //   vars = tps.map(tp => tp.name -> freshVar(noProv/*FIXME*/, N)(1)).toMap)
                  val body_ty = ctx.nextLevel { implicit ctx: Ctx => // TODO use poly instead!
                    typeType(ty)(ctx, raise,
                    vars = vars ++ tps.map(tp => tp.asInstanceOf[L[TN]].value.name -> freshVar(noProv/*FIXME*/, N)(1)).toMap)
                  }
                  // TODO check against `tv`
                  TypedNuFun(ctx.lvl, fd, PolymorphicType(ctx.lvl, body_ty))
                case L(body) =>
                  implicit val vars: Map[Str, SimpleType] =
                    outerVars ++ Map.empty // TODO tparams
                  implicit val gl: GenLambdas = true
                  val body_ty = typeLetRhs2(isrec = true, fd.nme.name, body)
                  // implicit val prov: TP = noProv // TODO
                  // subsume(body_ty, PolymorphicType(level, tv)) // TODO
                  TypedNuFun(ctx.lvl, fd, body_ty)
              }
              // subsume(res_ty, tv)
              res_ty
            case td: NuTypeDef =>
              td.kind match {
                case Cls | Nms =>
                  implicit val prov: TP = noProv // TODO
                  ctx.nest.nextLevel { implicit ctx =>
                    
                    val tparams = td.tparams.map(tp =>
                      tp -> freshVar(TypeProvenance(
                        tp.toLoc,
                        "type parameter",
                        S(tp.name),
                        true), N, S(tp.name)))
                    
                    implicit val vars: Map[Str, SimpleType] =
                      outerVars ++ tparams.iterator.mapKeys(_.name).toMap
                    
                    val typedParams = td.params.fields.map {
                      case (S(nme), Fld(mut, spec, value)) =>
                        assert(!mut && !spec, "TODO") // TODO
                        value.toType match {
                          case R(tpe) =>
                            implicit val newDefsInfo: Map[Str, (TypeDefKind, Int)] = Map.empty // TODO?
                            val ty = typeType(tpe)
                            nme -> FieldType(N, ty)(provTODO)
                          case _ => ???
                        }
                      case (N, Fld(mut, spec, nme: Var)) =>
                        assert(!mut && !spec, "TODO") // TODO
                        nme -> FieldType(N, freshVar(ttp(nme), N, S(nme.name)))(provTODO)
                      case _ => ???
                    }
                    // ctx ++= typedParams.mapKeysIter(_.name).mapValues(_.ub |> VarSymbol(_))
                    ctx ++= typedParams.map(p => p._1.name -> VarSymbol(p._2.ub, p._1))
                    
                    // ctx += "this" -> VarSymbol(
                    //     ClassTag(Var(td.name),
                    //       Set.empty//TODO
                    //     )(provTODO),
                    //   Var("this"))
                    
                    // val thisTV = freshVar(noProv/*FIXME*/, N, S("this"))
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    
                    // // TODO check against `tv`
                    // println(td.tparams)
                    // println(td.params)
                    // println(td.parents)
                    
                    implicit val prov: TP =
                      TypeProvenance(decl.toLoc, decl.describe)
                    val finalType = freshVar(noProv/*TODO*/, N, S("this"))
                    // def inherit(parents: Ls[Term], superType: ST, members: Ls[TypedNuDecl -> ST]): Unit = parents match {
                    def inherit(parents: Ls[Term], superType: ST, members: Ls[NuMember]): Ls[NuMember] = parents match {
                    // def inherit(parents: Ls[Term \/ TypedTypingUnit], superType: ST, members: Ls[TypedNuDecl]): Ls[TypedNuDecl] = parents match {
                      // case R(p) :: ps => ???
                      // case L(p) :: ps =>
                      case p :: ps =>
                        val newMembs = trace(s"${lvl}. Inheriting from $p") {
                          p match {
                            case Var(nme) =>
                              ctx.get(nme) match {
                                case S(lti: LazyTypeInfo) =>
                                  lti.complete().freshen match {
                                    case mxn: TypedNuMxn =>
                                      // mxn.thisTV
                                      // mxn.ttu.entities
                                      // ???
                                      // val fresh = mxn.freshen
                                      // println(fresh)
                                      
                                      println(s"Fresh $mxn")
                                      
                                      constrain(superType, mxn.superTV)
                                      constrain(finalType, mxn.thisTV)
                                      
                                      // TODO check overriding
                                      mxn.ttu.entities.map(_.complete()).map {
                                        case fun @ TypedNuFun(_, fd, ty) =>
                                          fun
                                        case _ => ???
                                      }
                                    case cls: TypedNuCls =>
                                      ???
                                    case als: TypedNuAls =>
                                      // TODO dealias first?
                                      err(msg"Cannot inherit from a type alias", p.toLoc)
                                      Nil
                                    case cls: TypedNuFun =>
                                      ???
                                  }
                                case S(_) =>
                                  err(msg"Cannot inherit from this", p.toLoc)
                                  Nil
                                case N => 
                                  err(msg"Could not find definition `${nme}`", p.toLoc)
                                  Nil
                              }
                            case _ =>
                              err(msg"Illegal parent specification", p.toLoc)
                              Nil
                          }
                        }()
                        val newSuperType = 
                          // superType &
                          WithType(
                          superType,
                          RecordType(
                            // newMembs.foldLeft(TopType.toUpper(provTODO))(_ && _.ty.toUpper(provTODO))
                            newMembs.map(m => m.fd.nme -> m.ty.toUpper(provTODO))
                          )(provTODO)
                          )(provTODO)
                        inherit(ps, newSuperType, members ++ newMembs)
                      case Nil =>
                        constrain(superType, finalType)
                        members
                    }
                    val baseType = RecordType(typedParams)(ttp(td.params, isType = true))
                    val paramMems = typedParams.map(f => NuParam(f._1, f._2))
                    // val baseMems = inherit(td.parents, baseType, Nil)
                    val baseMems = inherit(td.parents, baseType, paramMems)
                    
                    // ctx += thisTV
                    
                    // TODO
                    // ctx += "super" -> VarSymbol(superTV, Var("super"))
                    
                    val ttu = typeTypingUnit(td.body, allowPure = false) // TODO use
                    
                    // TODO check overriding
                    val clsMems = ttu.entities.map(_.complete()).map {
                      case fun @ TypedNuFun(_, fd, ty) =>
                        fun
                      case _ => ???
                    }
                    
                    // val thisTy = ClassTag(Var(td.name),
                    //       Set.empty//TODO
                    //     )(provTODO)
                    // constrain(thisTy, thisTV)
                    
                    // val mems = baseMems ++ paramMems ++ clsMems
                    val mems = baseMems ++ clsMems
                    TypedNuCls(outerCtx.lvl, td, ttu,
                      tparams, typedParams, mems.map(d => d.name -> d).toMap)
                  }
                case Mxn =>
                  implicit val prov: TP = noProv // TODO
                  ctx.nest.nextLevel { implicit ctx =>
                    implicit val vars: Map[Str, SimpleType] =
                      outerVars ++ Map.empty // TODO type params
                    val thisTV = freshVar(noProv/*FIXME*/, N, S("this"))
                    val superTV = freshVar(noProv/*FIXME*/, N, S("super"))
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    ctx += "super" -> VarSymbol(superTV, Var("super"))
                    // ctx |> { implicit ctx =>
                    val ttu = typeTypingUnit(td.body, allowPure = false)
                    TypedNuMxn(td, thisTV, superTV, ttu)
                    // }
                  }
                case _ => ???
              }
          }
          
        // } finally { result = S(res); isComputing = false }
        } finally { /* result = S(res); */ isComputing = false }
        
        result = S(res)
        res
        
      }()
    }
    def typeSignature(implicit raise: Raise): ST =
        if (isComputing)
          decl match {
            case _: NuFunDef =>
              tv // TODO FIXME wrong in general (when accessed from difft scope/level)
            case _ =>
              err(msg"Cyclic definition", decl.toLoc)
          }
        else complete() match {
      case cls: TypedNuCls if cls.td.kind is Nms =>
        ClassTag(Var(cls.td.nme.name), Set.empty)(provTODO)
      case _cls: TypedNuCls =>
        val cls = _cls.freshen.asInstanceOf[TypedNuCls]
        FunctionType(
          TupleType(cls.params.mapKeys(some))(provTODO),
          // cls.tparams.foldLeft(
          //   ClassTag(Var(cls.td.nme.name), Set.empty)(provTODO)
          // ) { case (acc, (tn, tv)) => acc &  }
          ClassTag(Var(cls.td.nme.name), Set.empty)(provTODO) & RecordType.mk(
            cls.tparams.map { case (tn, tv) =>
              Var(cls.td.nme.name + "#" + tn.name).withLocOf(tn) -> FieldType(S(tv), tv)(provTODO) }
          )(provTODO)
        )(provTODO)
      case TypedNuFun(_, fd, ty) =>
        // println(fd, ty)
        // ???
        ty
    }
    def force()(implicit raise: Raise): TypedNuTermDef = {
      val res = complete()
      res.force()
      decl match {
        case td: NuTypeDef =>
          td.kind match {
            case Cls | Nms =>
              implicit val prov: TP = noProv // TODO
              val thisTy = ClassTag(Var(td.name),
                    Set.empty//TODO
                  )(provTODO)
              constrain(thisTy, thisTV)
            case _ =>
          }
        case _ =>
      }
      res
    }
    override def toString: String =
      s"${decl.name} ~> ${if (isComputing) "<computing>" else result.fold("<uncomputed>")(_.toString)}"
  }
  
  // /** A type that potentially contains universally quantified type variables,
  //   * and which can be isntantiated to a given level. */
  // sealed abstract class TypeScheme {
  //   def uninstantiatedBody: SimpleType
  //   def instantiate(implicit lvl: Int): SimpleType
  // }
  
  /** A type with universally quantified type variables
    * (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(polymLevel: Level, body: SimpleType) extends SimpleType { // TODO add own prov?
    require(polymLevel < MaxLevel, polymLevel)
    val prov: TypeProvenance = body.prov
    lazy val level = levelBelow(polymLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = body.levelBelow(ub min polymLevel)
    def instantiate(implicit ctx:Ctx, shadows: Shadows): SimpleType = {
      implicit val state: MutMap[TV, ST] = MutMap.empty
      println(s"INST [${polymLevel}]   $this")
      println(s"  where  ${showBounds}")
      val res = body.freshenAbove(polymLevel, rigidify = false)
      println(s"TO [${lvl}] ~>  $res")
      println(s"  where  ${res.showBounds}")
      res
    }
    def rigidify(implicit ctx:Ctx, raise:Raise, shadows: Shadows): SimpleType = {
      implicit val state: MutMap[TV, ST] = MutMap.empty
      body.freshenAbove(polymLevel, rigidify = true)
    }
    def raiseLevelTo(newPolymLevel: Level, leaveAlone: Set[TV] = Set.empty)
          (implicit ctx: Ctx, shadows: Shadows): PolymorphicType = {
      require(newPolymLevel >= polymLevel)
      if (newPolymLevel === polymLevel) return this
      implicit val freshened: MutMap[TV, ST] = MutMap.empty
      PolymorphicType(newPolymLevel,
        self.freshenAbove(polymLevel, body, leaveAlone = leaveAlone)(
          ctx.copy(lvl = newPolymLevel + 1), // * Q: is this really fine? cf. stashing/unstashing etc.
          freshened, shadows)
      ) //(prov)
    }
    /** Tries to split a polymorphic function type
      * by distributing the quantification of *some* of its type vars into the function result. */
    def splitFunction(implicit ctx: Ctx, raise: Raise, shadows: Shadows): Opt[ST] = body match {
      case AliasOf(ft @ FunctionType(par, bod)) =>
        val couldBeDistribbed = bod.varsBetween(polymLevel, MaxLevel)
        println(s"could be distribbed: $couldBeDistribbed")
        if (couldBeDistribbed.isEmpty) return N
        val cannotBeDistribbed = par.varsBetween(polymLevel, MaxLevel)
        println(s"cannot be distribbed: $cannotBeDistribbed")
        val canBeDistribbed = couldBeDistribbed -- cannotBeDistribbed
        if (canBeDistribbed.isEmpty) return N // TODO
        val newInnerLevel =
          (polymLevel + 1) max cannotBeDistribbed.maxByOption(_.level).fold(MinLevel)(_.level)
        val innerPoly = PolymorphicType(polymLevel, bod)
        println(s"inner: ${innerPoly}")
        val res = FunctionType(par, innerPoly.raiseLevelTo(newInnerLevel, cannotBeDistribbed))(ft.prov)
        println(s"raised: ${res}")
        println(s"  where: ${res.showBounds}")
        if (cannotBeDistribbed.isEmpty) S(res)
        else S(PolymorphicType(polymLevel, res))
      case _ => N
    }
    override def toString = s"‹∀ $polymLevel. $body›"
  }
  object PolymorphicType {
    def mk(polymLevel: Level, body: SimpleType): SimpleType = {
      require(polymLevel <= MaxLevel)
      if (polymLevel === MaxLevel || body.level <= polymLevel) body
      else body match { // TODO see through proxies?
        case PolymorphicType(lvl, bod) => PolymorphicType(polymLevel min lvl, bod)
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
  
  /** A general type form (TODO: rename to AnyType). */
  sealed abstract class SimpleType extends SimpleTypeImpl {
    val prov: TypeProvenance
    def level: Level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level
    def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): SimpleType =
      self.freshenAbove(lim, this, rigidify)
    constructedTypes += 1
  }
  type ST = SimpleType
  
  sealed abstract class BaseTypeOrTag extends SimpleType
  sealed abstract class BaseType extends BaseTypeOrTag {
    def toRecord: RecordType = RecordType.empty
    protected def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx:Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): BaseType
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): BaseType =
      freshenAboveImpl(lim, rigidify)
  }
  sealed abstract class MiscBaseType extends BaseType {
    override def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx:Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): MiscBaseType
  }
  sealed trait Factorizable extends SimpleType
  
  type FT = FunctionType
  
  case class FunctionType(lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends MiscBaseType {
    lazy val level: Int = lhs.level max rhs.level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = lhs.levelBelow(ub) max rhs.levelBelow(ub)
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): FunctionType =
      FunctionType(lhs.freshenAbove(lim, rigidify), rhs.freshenAbove(lim, rigidify))(prov)
    override def toString = s"(${lhs match {
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
      FunctionType(lhss.reduce(_ & _), rhss.reduce(_ | _))(prov)
    }
    lazy val level: Level = levelBelow(MaxLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      alts.iterator.map(_.levelBelow(ub)).max
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): Overload =
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
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): RecordType =
      self.mapPol(this, N, false)((_, x) => x.freshenAbove(lim, rigidify))
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
    def level: Level = inner.level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = inner.levelBelow(ub)
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): ArrayType =
      ArrayType(inner.freshenAbove(lim, rigidify))(prov)
    override def toString = s"Array‹$inner›"
  }
  
  case class TupleType(fields: List[Opt[Var] -> FieldType])(val prov: TypeProvenance) extends ArrayBase {
    lazy val inner: FieldType = fields.map(_._2).reduceLeftOption(_ || _).getOrElse(BotType.toUpper(noProv))
    lazy val level: Level = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = fields.iterator.map(_._2.levelBelow(ub)).maxOption.getOrElse(MinLevel)
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): TupleType =
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

  case class SpliceType(elems: Ls[Either[SimpleType, FieldType]])(val prov: TypeProvenance) extends ArrayBase {
    require(elems.nonEmpty) // ? – since `max` is used below...
    lazy val level: Int = elems.map{ case L(l) => l.level case R(r) => r.level }.max
    
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST]): MiscBaseType =
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
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): Without =
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
    override def toString = s"${base} w/ ${rcd}"
  }
  
  type TR = TypeRef
  case class TypeRef(defn: TypeName, targs: Ls[SimpleType])(val prov: TypeProvenance) extends SimpleType {
    def level: Level = targs.iterator.map(_.level).maxOption.getOrElse(0)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = targs.iterator.map(_.levelBelow(ub)).maxOption.getOrElse(MinLevel)
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): TypeRef =
      TypeRef(defn, targs.map(_.freshenAbove(lim, rigidify)))(prov)
    def expand(implicit ctx: Ctx): SimpleType = expandWith(paramTags = true)
    def expandWith(paramTags: Bool)(implicit ctx: Ctx): SimpleType = //if (defn.name.isCapitalized) {
      ctx.tyDefs2.get(defn.name).map(_.decl match {
        case td: NuTypeDef if td.kind is Cls =>
          ClassTag(Var(td.nme.name).withLocOf(td.nme),
            Set.empty//TODO
            )(provTODO)
        case _ => ???
      }
    ).getOrElse {
      val td = ctx.tyDefs(defn.name)
      require(targs.size === td.tparamsargs.size)
      lazy val tparamTags =
        if (paramTags) RecordType.mk(td.tparamsargs.map { case (tp, tv) =>
            val tvv = td.getVariancesOrDefault
            tparamField(defn, tp) -> FieldType(
              Some(if (tvv(tv).isCovariant) BotType else tv),
              if (tvv(tv).isContravariant) TopType else tv)(prov)
          })(noProv)
        else TopType
      subst(td.kind match {
        case Als => td.bodyTy
        case Nms => throw new NotImplementedError("Namespaces are not supported yet.")
        case Cls => clsNameToNomTag(td)(prov, ctx) & td.bodyTy & tparamTags
        case Trt => trtNameToNomTag(td)(prov, ctx) & td.bodyTy & tparamTags
      }, td.targs.lazyZip(targs).toMap) //.withProv(prov)
    } //tap { res => println(s"Expand $this => $res") }
    private var tag: Opt[Opt[ClassTag]] = N
    def mkTag(implicit ctx: Ctx): Opt[ClassTag] = tag.getOrElse {
      val res = ctx.tyDefs.get(defn.name) match {
        case S(td: TypeDef) if td.kind is Cls => S(clsNameToNomTag(td)(noProv, ctx))
        case _ => N
      }
      tag = S(res)
      res
    }
    def mapTargs[R](pol: Opt[Bool])(f: (Opt[Bool], ST) => R)(implicit ctx: Ctx): Ls[R] = {
      // val td = ctx.tyDefs(defn.name)
      // td.tvarVariances.fold(targs.map(f(N, _))) { tvv =>
      //   assert(td.tparamsargs.sizeCompare(targs) === 0)
      //   (td.tparamsargs lazyZip targs).map { case ((_, tv), ta) =>
      
      // TODO factor w/ below
      val (tvarVariances, tparamsargs) = ctx.tyDefs.get(defn.name) match {
        case S(td) =>
          (td.tvarVariances, td.tparamsargs)
        case N =>
          val td = ctx.tyDefs2(defn.name)
          (N, td.tparams)
      }
      tvarVariances.fold(targs.map(f(N, _))) { tvv =>
        assert(tparamsargs.sizeCompare(targs) === 0)
        (tparamsargs lazyZip targs).map { case ((_, tv), ta) =>
          tvv(tv) match {
            case VarianceInfo(true, true) =>
              f(N, TypeBounds(BotType, TopType)(noProv))
            case VarianceInfo(co, contra) =>
              f(if (co) pol else if (contra) pol.map(!_) else N, ta)
          }
      }}
    }
    // TODO dedup w/ above
    def mapTargs[R](pol: PolMap)(f: (PolMap, ST) => R)(implicit ctx: Ctx): Ls[R] = {
      // val td = ctx.tyDefs.getOrElse(defn.name, ctx.tyDefs2(defn.name))
      // td.tvarVariances.fold(targs.map(f(pol.invar, _))) { tvv =>
      //   assert(td.tparamsargs.sizeCompare(targs) === 0)
      //   (td.tparamsargs lazyZip targs).map { case ((_, tv), ta) =>
      val (tvarVariances, tparamsargs) = ctx.tyDefs.get(defn.name) match {
        case S(td) =>
          (td.tvarVariances, td.tparamsargs)
        case N =>
          val td = ctx.tyDefs2(defn.name)
          (N, td.tparams)
      }
      tvarVariances.fold(targs.map(f(pol.invar, _))) { tvv =>
        assert(tparamsargs.sizeCompare(targs) === 0)
        (tparamsargs lazyZip targs).map { case ((_, tv), ta) =>
          tvv(tv) match {
            case VarianceInfo(true, true) =>
              f(pol.invar, TypeBounds(BotType, TopType)(noProv))
            case VarianceInfo(co, contra) =>
              f(if (co) pol else if (contra) pol.contravar else pol.invar, ta)
          }
      }}
    }
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
      case (SkolemTag(_, id1), SkolemTag(_, id2)) => id1 compare id2
      case (_: ObjectTag, _: SkolemTag) => 1
      case (_: SkolemTag, _: ObjectTag) => -1
    }
  }
  
  case class ClassTag(id: SimpleTerm, parents: Set[TypeName])(val prov: TypeProvenance)
      extends BaseType with TypeTag with ObjectTag {
    lazy val parentsST = parents.iterator.map(tn => Var(tn.name)).toSet[IdentifiedTerm]
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
    def freshenAboveImpl(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): this.type = this
    override def toString = showProvOver(false)(id.idStr+s"<${parents.map(_.name).mkString(",")}>")
  }
  
  sealed trait TypeVarOrRigidVar extends SimpleType
  
  sealed trait ObjectTag extends TypeTag {
    val id: SimpleTerm
    override def toString = "#" + id.idStr
  }
  
  sealed abstract class AbstractTag extends BaseTypeOrTag with TypeTag with Factorizable
  
  case class TraitTag(id: Var)(val prov: TypeProvenance) extends AbstractTag with ObjectTag {
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = MinLevel
    def level: Level = MinLevel
  }
  
  case class SkolemTag(level: Level, id: TV)(val prov: TypeProvenance) extends AbstractTag with TypeVarOrRigidVar {
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      if (level <= ub) level else MinLevel
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
      if ((lb is ub) || lb === ub || lb <:< ub && ub <:< lb) lb else (lb, ub) match {
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
    def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]): FieldType =
      update(_.freshenAbove(lim, rigidify), _.freshenAbove(lim, rigidify))
    override def toString =
      lb.fold(s"$ub")(lb => s"mut ${if (lb === BotType) "" else lb}..$ub")
  }
  
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
    
    
    var assignedTo: Opt[ST] = N
    
    // * Bounds shoudl always be disregarded when `equatedTo` is defined, as they are then irrelevant:
    def lowerBounds: List[SimpleType] = { require(assignedTo.isEmpty); _lowerBounds }
    def upperBounds: List[SimpleType] = { require(assignedTo.isEmpty); _upperBounds }
    def lowerBounds_=(bs: Ls[ST]): Unit = { require(assignedTo.isEmpty); _lowerBounds = bs }
    def upperBounds_=(bs: Ls[ST]): Unit = { require(assignedTo.isEmpty); _upperBounds = bs }
    
    private val creationRun = currentConstrainingRun
    def original: TV =
      if (currentConstrainingRun === creationRun) originalTV.getOrElse(this)
      else this
    private lazy val trueOriginal: Opt[TV] =
      originalTV.flatMap(_.trueOriginal.orElse(originalTV))
    
    override def freshenAbove(lim: Int, rigidify: Bool)
        (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
        : TypeVarOrRigidVar =
      super.freshenAbove(lim, rigidify) match {
        case tv: TypeVarOrRigidVar =>
          tv // * Note that type variables can be refreshed as rigid variables (trait tags)
        case _ => die
      }
    
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
    private[mlscript] val uid: Int = { freshCount += 1; freshCount - 1 }
    lazy val asTypeVar = new TypeVar(L(uid), nameHint)
    def compare(that: TV): Int = this.uid compare that.uid
    override def toString: String =
      (trueOriginal match {
        case S(to) =>
          assert(to.nameHint === nameHint)
          to.mkStr + "_" + uid + showLevel(level)
        case N =>
          showProvOver(false)(mkStr + showLevel(level))
      }) + (if (assignedTo.isDefined) "#" else "")
    private[mlscript] def mkStr = nameHint.getOrElse("α") + uid
    
    def isRecursive_$(implicit ctx: Ctx) : Bool = (lbRecOccs_$, ubRecOccs_$) match {
      case (S(N | S(true)), _) | (_, S(N | S(false))) => true
      case _ => false
    } 
    /** None: not recursive in this bound; Some(Some(pol)): polarly-recursive; Some(None): nonpolarly-recursive.
      * Note that if we have something like 'a :> Bot <: 'a -> Top, 'a is not truly recursive
      *   and its bounds can actually be inlined. */
    private final def lbRecOccs_$(implicit ctx: Ctx): Opt[Opt[Bool]] = {
      // println("+", this, lowerBounds)
      assignedTo.getOrElse(TupleType(lowerBounds.map(N -> _.toUpper(noProv)))(noProv)).getVarsPol(PolMap.pos).get(this)
      }
    private final def ubRecOccs_$(implicit ctx: Ctx): Opt[Opt[Bool]] ={
      // println("-", this, upperBounds)
      assignedTo.getOrElse(TupleType(upperBounds.map(N -> _.toUpper(noProv)))(noProv)).getVarsPol(PolMap.posAtNeg).get(this)
    }
  }
  type TV = TypeVariable
  private var freshCount = 0
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
  
}
