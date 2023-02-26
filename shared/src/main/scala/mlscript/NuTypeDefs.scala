package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class NuTypeDefs extends ConstraintSolver { self: Typer =>
  import TypeProvenance.{apply => tp}
  
  
  sealed abstract class NuDeclInfo
  
  case class FunInfo() extends NuDeclInfo
  case class TypeDefInfo() extends NuDeclInfo
  
  
  // * For now these are just unused stubs to be completed and used later
  
  
  sealed trait NuMember {
    def name: Str
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : NuMember
    
    // TODO rm – just use `mapPolMap`
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember
    
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember
  }
  
  
  case class NuParam(nme: Var, ty: FieldType, isType: Bool) extends NuMember {
    def name: Str = nme.name
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : NuParam =
      NuParam(nme, ty.freshenAbove(lim, rigidify), isType)
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember =
        NuParam(nme, ty.update(t => f(pol.map(!_), t), t => f(pol, t)), isType)
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember =
        NuParam(nme, ty.update(t => f(pol.contravar, t), t => f(pol, t)), isType)
  }
  // case class NuTypeParam(nme: TN, ty: FieldType) extends NuMember {
  //   def name: Str = nme.name
    
  //   def freshenAbove(lim: Int, rigidify: Bool)
  //         (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
  //         : NuParam =
  //     NuParam(nme, ty.freshenAbove(lim, rigidify))
  // }
  
  
  // sealed abstract class TypedNuDecl extends NuMember {
  sealed trait TypedNuDecl extends NuMember {
    def name: Str
    // def freshen(implicit ctx: Ctx): TypedNuDecl = this match {
    //   case m @ TypedNuMxn(td, thisTV, superTV, ttu) =>
    //     implicit val freshened: MutMap[TV, ST] = MutMap.empty
    //     implicit val shadows: Shadows = Shadows.empty
    //     TypedNuMxn(td, thisTV, superTV, ttu.freshenAbove(m.level, rigidify = false))
    //   case _ => ???
    // }
  }
  
  sealed trait TypedNuTermDef extends TypedNuDecl with AnyTypeDef {
    // override def toString: String = this match {
    //   case _ => ???
    // }
    def level: Level
    def freshen(implicit ctx: Ctx): TypedNuDecl = {
      implicit val freshened: MutMap[TV, ST] = MutMap.empty
      implicit val shadows: Shadows = Shadows.empty
      // println(level)
      ctx.copy(lvl = level + 1) |> { implicit ctx =>
      freshenAbove(level, rigidify = false).asInstanceOf[TypedNuDecl]
      }
    }
    def map(f: ST => ST)(implicit ctx: Ctx): TypedNuTermDef =
      mapPol(N, false)((_, ty) => f(ty)).asInstanceOf[TypedNuTermDef]//TODO
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef
    // def childrenTypes: Ls[ST]
    /* 
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : TypedNuTermDef = {
      // implicit val freshened: MutMap[TV, ST] = MutMap.empty
      // implicit val shadows: Shadows = Shadows.empty
      // ctx.copy(lvl = level + 1) |> { implicit ctx =>
      this match {
        case m @ TypedNuMxn(td, thisTV, superTV, ttu) =>
          // println(">>",m.level)
          // TypedNuMxn(td, thisTV, superTV, ttu.freshenAbove(m.level, rigidify))
          // TypedNuMxn(td, thisTV, superTV, ttu.freshenAbove(lim, rigidify))
          TypedNuMxn(td,
            thisTV.freshenAbove(lim, rigidify).asInstanceOf[TV],
            superTV.freshenAbove(lim, rigidify).asInstanceOf[TV],
            ttu.freshenAbove(lim, rigidify))
        case TypedNuFun(level, fd, ty) =>
          // TypedNuFun(level min ctx.lvl, fd, ty.freshenAbove(level, rigidify))
          TypedNuFun(level min ctx.lvl, fd, ty.freshenAbove(lim, rigidify))
        case TypedNuCls(level, td, ttu, tps, params, members) =>
          println(">>",level,ctx.lvl)
          // TypedNuCls(level, td, ttu.freshenAbove(level, rigidify),
          //   params.mapValues(_.freshenAbove(level, rigidify)),
          //   members.mapValuesIter(_.freshenAbove(level, rigidify)).toMap)
          TypedNuCls(level, td, ttu.freshenAbove(lim, rigidify),
            tps.mapValues(_.freshenAbove(lim, rigidify).asInstanceOf[TV]),
            params.mapValues(_.freshenAbove(lim, rigidify)),
            members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap)
        // case _ => ???
      // }
      }
    }
    */
    def force()(implicit raise: Raise): Unit = this match {
      case x: TypedNuMxn => x.ttu.force()
      case x: TypedNuCls => x.ttu.force()
      case _: TypedNuFun => ()
    }
  }
  
  sealed abstract class TypedNuTypeDef(kind: TypeDefKind) extends TypedNuTypeDefBase with TypedNuDecl {
    def nme: TypeName
    // val tparams: Ls[TN -> TV] = Nil // TODO
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST]): TypedNuTypeDef = 
      this match {
        case m @ TypedNuMxn(td, thisTV, superTV, members, ttu) =>
          // println(">>",m.level)
          // TypedNuMxn(td, thisTV, superTV, ttu.freshenAbove(m.level, rigidify))
          // TypedNuMxn(td, thisTV, superTV, ttu.freshenAbove(lim, rigidify))
          TypedNuMxn(td,
            thisTV.freshenAbove(lim, rigidify).asInstanceOf[TV],
            superTV.freshenAbove(lim, rigidify).asInstanceOf[TV],
            members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
            ttu.freshenAbove(lim, rigidify))
        case cls @ TypedNuCls(level, td, ttu, tps, params, members, thisTy) =>
          println(">>",level,ctx.lvl)
          // TypedNuCls(level, td, ttu.freshenAbove(level, rigidify),
          //   params.mapValues(_.freshenAbove(level, rigidify)),
          //   members.mapValuesIter(_.freshenAbove(level, rigidify)).toMap)
          TypedNuCls(level, td, ttu.freshenAbove(lim, rigidify),
            // tps.mapValues(_.freshenAbove(lim, rigidify).asInstanceOf[TV]),
            tps.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).asInstanceOf[TV], tp._3)),
            params.mapValues(_.freshenAbove(lim, rigidify)),
            members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
            thisTy.freshenAbove(lim, rigidify))(
              cls.instanceType.freshenAbove(lim, rigidify))
        // case _ => ???
      // }
      }
    // val prov: TP
    val td: NuTypeDef
    val prov: TP = TypeProvenance(td.toLoc, td.describe, isType = true)
    val level: Level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = ???
  }
  // case class TypedNuTypeDef(
  //   kind: TypeDefKind,
  //   nme: TypeName,
  //   tparamsargs: List[(TypeName, TypeVariable)],
  //   bodyTy: SimpleType,
  //   baseClasses: Set[TypeName],
  //   toLoc: Opt[Loc],
  // )
  
  // case class TypedNuAls(level: Level, nme: TypeName)(val prov: TP) extends TypedNuTypeDef(Als) {
  case class TypedNuAls(level: Level, td: NuTypeDef) extends TypedNuTypeDef(Als) {
    def name: Str = nme.name
    def nme: mlscript.TypeName = ???
    // def freshenAbove(lim: Int, rigidify: Bool)
    //       (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
    //       : TypedNuTypeDef = ???
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember = ???
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember = ???
  }
  
  // case class TypedNuCls(nme: TypeName) extends TypedNuTypeDef(Als) with TypedNuTermDef {
  case class TypedNuCls(level: Level, td: NuTypeDef, ttu: TypedTypingUnit,
        tparams: Ls[(TN, TV, Opt[VarianceInfo])], params: Ls[Var -> FieldType],
      // members: Map[Str, LazyTypeInfo])
      members: Map[Str, NuMember],
      thisTy: ST
  )(
    val instanceType: ST, // only meant to be used in `force` and `variances`
  ) extends TypedNuTypeDef(Cls) with TypedNuTermDef {
  // case class TypedNuCls(td: NuTypeDef, paramTypes: Ls[ST], ttu: TypedTypingUnit) extends TypedNuTypeDef(Cls) with TypedNuTermDef {
    def nme: TypeName = td.nme
    def name: Str = nme.name
    
    private var _variances: Opt[VarianceStore] = N
    def variances(implicit ctx: Ctx): VarianceStore = {
      _variances match {
        case S(res) => res
        case N =>
          // CompletedTypingUnit(this :: Nil, N).childrenPol(PolMap.pos)
          
          // val vars = CompletedTypingUnit(this :: Nil, N).getVarsPol(PolMap.pos)
          // MutMap.from(vars.iterator.mapValues {
          //   case S(true) => VarianceInfo.co
          //   case S(false) => VarianceInfo.contra
          //   case N => VarianceInfo.in
          // })
          
          val store = VarianceStore.empty
          object Trav extends Traverser2.InvariantFields {
            override def apply(pol: PolMap)(ty: ST): Unit =
                trace(s"Trav($pol)($ty)") {
                ty match {
              case tv: TypeVariable =>
                store(tv) = store.getOrElse(tv, VarianceInfo.bi) && (pol(tv) match {
                  case S(true) => VarianceInfo.co
                  case S(false) => VarianceInfo.contra
                  case N => VarianceInfo.in
                })
                super.apply(pol)(ty)
              case ty @ RecordType(fs) =>
                // Ignore type param members such as `C#A` in `{C#A: mut A30'..A30'}`
                super.apply(pol)(RecordType(fs.filterNot(_._1.name.contains('#')))(ty.prov))
              case _ => super.apply(pol)(ty)
            }
            }()
          }
          // Trav.applyLike(PolMap.pos)(CompletedTypingUnit(this :: Nil, N))
          Trav(PolMap.pos)(instanceType)
          // println(store)
          store
          
      }
    }
    def varianceOf(tv: TV)(implicit ctx: Ctx): VarianceInfo =
      variances.getOrElse(tv, VarianceInfo.in)
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
        TypedNuCls(level, td, ttu,
          tparams.map(tp => (tp._1, f(N, tp._2).asInstanceOf[TV], tp._3)),
          // params.mapValues(_.mapPol(pol)(f)),
          params.mapValues(_.update(t => f(pol.map(!_), t), t => f(pol, t))),
          members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap,
          f(pol.map(!_), thisTy)//.asInstanceOf[TV]
        )(f(pol, instanceType))
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
        TypedNuCls(level, td, ttu,
          tparams.map(tp => (tp._1, f(pol.invar, tp._2).asInstanceOf[TV], tp._3)),
          // params.mapValues(_.mapPol(pol)(f)),
          params.mapValues(_.update(t => f(pol.contravar, t), t => f(pol, t))),
          members.mapValuesIter(_.mapPolMap(pol)(f)).toMap,
          f(pol.contravar, thisTy)//.asInstanceOf[TV]
        )(f(pol, instanceType))
  }
  
  case class TypedNuMxn(td: NuTypeDef, thisTV: ST, superTV: ST, members: Map[Str, NuMember], ttu: TypedTypingUnit) extends TypedNuTypeDef(Mxn) with TypedNuTermDef {
    val level: Level = thisTV.level - 1 // TODO cleaner
    def nme: TypeName = td.nme
    def name: Str = nme.name
    // def freshen(implicit ctx: Ctx): TypedNuMxn = TypedNuMxn(td, 
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      TypedNuMxn(td, f(pol.map(!_), thisTV), f(pol.map(!_), superTV), members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap, ttu)
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      TypedNuMxn(td, f(pol.contravar, thisTV), f(pol.contravar, superTV), members.mapValuesIter(_.mapPolMap(pol)(f)).toMap, ttu)
  }
  
  /** Note: the type `ty` is stoed *without* its polymorphic wrapper! */
  case class TypedNuFun(level: Level, fd: NuFunDef, ty: ST) extends TypedNuDecl with TypedNuTermDef {
    def name: Str = fd.nme.name
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : TypedNuFun = this match {
      case TypedNuFun(level, fd, ty) =>
        // TypedNuFun(level min ctx.lvl, fd, ty.freshenAbove(level, rigidify))
        TypedNuFun(level min ctx.lvl, fd, ty.freshenAbove(lim, rigidify))
    }
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      // TypedNuFun(level, fd, ty.mapPol(pol, smart)(f))
      TypedNuFun(level, fd, f(pol, ty))
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      TypedNuFun(level, fd, f(pol, ty))
  }
  
  case class CompletedTypingUnit(entities: Ls[TypedNuTermDef], result: Opt[ST]) extends OtherTypeLike {
    def map(f: ST => ST)(implicit ctx: Ctx): CompletedTypingUnit =
      CompletedTypingUnit(entities.map(_.map(f)), result.map(f))
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): CompletedTypingUnit =
      CompletedTypingUnit(entities.map(_.mapPol(pol, smart)(f)), result.map(f(pol, _)))
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): CompletedTypingUnit =
      CompletedTypingUnit(entities.map(_.mapPolMap(pol)(f)), result.map(f(pol, _)))
  }
  case class TypedTypingUnit(entities: Ls[LazyTypeInfo], result: Opt[ST]) /* extends OtherTypeLike */ {
    // def freshen(implicit ctx: Ctx): TypedTypingUnit = ???
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : TypedTypingUnit =
      TypedTypingUnit(entities.map(_.map(_.freshenAbove(lim, rigidify).asInstanceOf[TypedNuTermDef]))
        , result.map(_.freshenAbove(lim, rigidify)))
    def force()(implicit raise: Raise): CompletedTypingUnit = {
      CompletedTypingUnit(entities.map(_.force()), result)
    }
  }
  
  def typeTypingUnit(tu: TypingUnit, allowPure: Bool)
        (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType]): TypedTypingUnit =
      trace(s"${ctx.lvl}. Typing $tu") {
      // trace(s"${ctx.lvl}. Typing $tu") { ctx.nextLevel { implicit ctx: Ctx =>
    // val named = mutable.Map.empty[Str, LazyTypeInfo[TypedNuTermDef]]
    val named = mutable.Map.empty[Str, LazyTypeInfo]
    // val namedTerms = mutable.Map.empty[Var, LazyTypeInfo[TypedNuTypeDef]]
    // val namedTypes = mutable.Map.empty[TypeName, LazyTypeInfo[TypedNuTypeDef]]
    // val namedTerms = mutable.Map.empty[Str, LazyTypeInfo[ST]]
    // val namedTypes = mutable.Map.empty[Str, LazyTypeInfo[TypedNuTypeDef]]
    // val infos = tu.entities.collect {
    //   case fd: NuFunDef => fd.nme.name -> new LazyTypeInfo(lvl, fd)
    //   case td: NuTypeDef => td.nme.name -> new LazyTypeInfo(lvl, td)
    // }
    val infos = tu.entities.collect {
      case decl: NuDecl =>
        val lti = new LazyTypeInfo(lvl, decl)
        decl match {
          case td: NuTypeDef =>
            ctx.tyDefs2 += td.nme.name -> lti
          case _: NuFunDef =>
        }
        // def registerTerm = 
        named.updateWith(decl.name) {
          case sv @ S(v) =>
            // * TODO allow defining a previously given signature
            err(msg"Refininition of ${decl.name}", decl.toLoc)
            S(lti)
          case N =>
            S(lti)
        }
        decl.name -> lti
        // decl match {
        //   case fd: NuFunDef =>
        //     registerTerm
        //     fd.nme.name -> lti
        //   case td: NuTypeDef =>
        //     registerTerm
        //     td.nme.name -> new LazyTypeInfo(lvl, td)
        // }
    }
    ctx ++= infos
    def go(stmts: Ls[Statement])(implicit ctx: Ctx): Opt[ST] = stmts match {
      case s :: stmts =>
        val res_ty = s match {
          // case NuFunDef(isLetRec, nme, targs, rhs) =>
          // case fd: NuFunDef =>
          //   ???
          // case td: NuTypeDef =>
          //   ???
          case decl: NuDecl =>
            val lti = named.getOrElse(decl.name, die)
            // completeTypeInfo()
            // lti.complete() // ???
            // UnitType
            N
          // case ds: DesugaredStatement =>
          //   val (poly_ty, bindings) = typeStatement(ds, allowPure)
          //   poly_ty.instantiate
          case s: Statement =>
            val (diags, dss) = s.desugared
            diags.foreach(raise)
            // typeStatement(desug, allowPure)
            // go(dss ::: stmts)
            S(typeTerms(dss, false, Nil)(ctx, raise, TypeProvenance(s.toLoc, s match {
              case trm: Term => trm.describe
              case s => ???
            }), Map.empty, genLambdas = false))
        }
        stmts match {
          case Nil => res_ty
          case stmts =>
            // TODO check discarded non-unit values
            go(stmts)
        }
      // case Nil => UnitType
      case Nil => N
    }
    val res_ty = go(tu.entities)
    // TypedTypingUnit(infos.unzip._2.map(_.complete()), S(res_ty))
    // TypedTypingUnit(infos.unzip._2.map(_.complete()), res_ty)
    TypedTypingUnit(infos.unzip._2, res_ty)
  }()
  // }(raise, noProv/*TODO*/)}()
  
  // class TypedTypingUnit(tu: TypingUnit)(implicit ctx: Ctx, raise: Raise) {
  // }
  
  
}

