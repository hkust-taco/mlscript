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
    def level: Level
    // def freshen(implicit ctx: Ctx): TypedNuDecl = this match {
    //   case m @ TypedNuMxn(td, thisTV, superTV, ttu) =>
    //     implicit val freshened: MutMap[TV, ST] = MutMap.empty
    //     implicit val shadows: Shadows = Shadows.empty
    //     TypedNuMxn(td, thisTV, superTV, ttu.freshenAbove(m.level, rigidify = false))
    //   case _ => ???
    // }
    def freshen(implicit ctx: Ctx): TypedNuDecl = {
      implicit val freshened: MutMap[TV, ST] = MutMap.empty
      implicit val shadows: Shadows = Shadows.empty
      // println(level)
      ctx.copy(lvl = level + 1) |> { implicit ctx =>
      freshenAbove(level, rigidify = false).asInstanceOf[TypedNuDecl]
      }
    }
    def map(f: ST => ST)(implicit ctx: Ctx): TypedNuDecl =
      mapPol(N, false)((_, ty) => f(ty))
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuDecl
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuDecl
    def force()(implicit raise: Raise): Unit = this match {
      case x: TypedNuMxn => x.ttu.force()
      case x: TypedNuCls => x.ttu.force()
      case _: TypedNuFun => ()
      case _: TypedNuAls => ()
    }
  }
  
  sealed trait TypedNuTermDef extends TypedNuDecl with AnyTypeDef {
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
  }
  
  sealed abstract class TypedNuTypeDef(kind: TypeDefKind) extends TypedNuDecl {
    def nme: TypeName
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST]): TypedNuTypeDef = 
      this match {
        case m @ TypedNuMxn(td, thisTV, superTV, tparams, params, members, ttu) =>
          TypedNuMxn(td,
            thisTV.freshenAbove(lim, rigidify).asInstanceOf[TV],
            superTV.freshenAbove(lim, rigidify).asInstanceOf[TV],
            tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).asInstanceOf[TV], tp._3)),
            params.mapValues(_.freshenAbove(lim, rigidify)),
            members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
            ttu.freshenAbove(lim, rigidify))
        case cls @ TypedNuCls(level, td, ttu, tparams, params, members, thisTy) =>
          TypedNuCls(level, td, ttu.freshenAbove(lim, rigidify),
            tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).asInstanceOf[TV], tp._3)),
            params.mapValues(_.freshenAbove(lim, rigidify)),
            members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
            thisTy.freshenAbove(lim, rigidify))(
              cls.instanceType.freshenAbove(lim, rigidify))
      }
    val td: NuTypeDef
    val prov: TP = TypeProvenance(td.toLoc, td.describe, isType = true)
    val level: Level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = ???
  }
  
  case class TypedNuAls(level: Level, td: NuTypeDef,
      tparams: Ls[(TN, TV, Opt[VarianceInfo])],
      body: ST,
  ) extends TypedNuTypeDef(Als) {
    def name: Str = nme.name
    def nme: mlscript.TypeName = td.nme
    // def freshenAbove(lim: Int, rigidify: Bool)
    //       (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
    //       : TypedNuTypeDef = ???
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuDecl =
        TypedNuAls(
          level, td,
          tparams.map(tp => (tp._1, f(N, tp._2).asInstanceOf[TV], tp._3)),
          f(pol, body)
        )
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuDecl =
        TypedNuAls(
          level, td,
          tparams.map(tp => (tp._1, f(pol.invar, tp._2).asInstanceOf[TV], tp._3)),
          f(pol, body)
        )
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
    
    
    // TODO
    // def checkVariances
    
    // lazy val explicitVariances: VarianceStore =
    //   MutMap.from(tparams.iterator.map(tp => tp._2 -> tp._3.getOrElse(VarianceInfo.in)))
    
    // TODO should we really recompute them on freshened instances, or can we avoid that?
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
          
          // TODO check consistency with explicitVariances
          store ++ tparams.iterator.collect { case (_, tv, S(vi)) => tv -> vi }
          
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
  
  case class TypedNuMxn(td: NuTypeDef, thisTV: ST, superTV: ST,
        tparams: Ls[(TN, TV, Opt[VarianceInfo])], params: Ls[Var -> FieldType],
        members: Map[Str, NuMember], ttu: TypedTypingUnit,
      ) extends TypedNuTypeDef(Mxn) with TypedNuTermDef {
    val level: Level = thisTV.level - 1 // TODO cleaner
    def nme: TypeName = td.nme
    def name: Str = nme.name
    // def freshen(implicit ctx: Ctx): TypedNuMxn = TypedNuMxn(td, 
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      TypedNuMxn(td, f(pol.map(!_), thisTV), f(pol.map(!_), superTV),
        tparams.map(tp => (tp._1, f(N, tp._2).asInstanceOf[TV], tp._3)),
        params.mapValues(_.update(t => f(pol.map(!_), t), t => f(pol, t))),
        members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap, ttu)
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      TypedNuMxn(td, f(pol.contravar, thisTV), f(pol.contravar, superTV),
        tparams.map(tp => (tp._1, f(pol.invar, tp._2).asInstanceOf[TV], tp._3)),
        params.mapValues(_.update(t => f(pol.contravar, t), t => f(pol, t))),
        members.mapValuesIter(_.mapPolMap(pol)(f)).toMap, ttu)
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
  
  case class CompletedTypingUnit(entities: Ls[TypedNuDecl], result: Opt[ST]) extends OtherTypeLike {
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
        val lti = new LazyTypeInfo(decl, implicitly)
        decl match {
          case td: NuTypeDef =>
            ctx.tyDefs2 += td.nme.name -> lti
          case _: NuFunDef =>
        }
        // def registerTerm = 
        named.updateWith(decl.name) {
          case sv @ S(v) =>
            // * TODO allow defining a previously given signature
            decl match {
              case NuFunDef(S(_), _, _, _) => ()
              case _ =>
                err(msg"Refininition of ${decl.name}", decl.toLoc)
            }
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
              case s => "statement"
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
  
  
  trait LazyTypeInfoImpl { this: LazyTypeInfo =>
  // class LazyTypeInfo[A](level: Int, decl: NuDecl) extends TypeInfo {
    private def outerCtx = ctx
    // private def outerVars = vars
    
    val level: Level = ctx.lvl
    
    private implicit val prov: TP =
      TypeProvenance(decl.toLoc, decl.describe)
    
    println(s"${ctx.lvl}. Created lazy type info $decl")
    
    lazy val tparams: Ls[(TN, TV, Opt[VarianceInfo])] = ctx.nest.nextLevel { implicit ctx =>
      decl match {
        case td: NuTypeDef =>
          td.tparams.map(tp =>
            (tp._2, freshVar(TypeProvenance(
              tp._2.toLoc,
              "type parameter",
              S(tp._2.name),
              true), N, S(tp._2.name)), tp._1))
        case fd: NuFunDef => Nil // TODO
      }
    }
    
    lazy val explicitVariances: VarianceStore =
      MutMap.from(tparams.iterator.map(tp => tp._2 -> tp._3.getOrElse(VarianceInfo.in)))
    
    def varianceOf(tv: TV)(implicit ctx: Ctx): VarianceInfo =
      // TODO make use of inferred vce if result is completed
      explicitVariances.get(tv).getOrElse(VarianceInfo.in)
    
    // println(s"Type params ${tparams.mkString(" ")}")
    
    lazy private implicit val vars: Map[Str, SimpleType] =
      // outerVars ++ tparams.iterator.mapKeys(_.name).toMap
      outerVars ++ tparams.iterator.map {
        case (tp, tv, vi) => (tp.name, SkolemTag(tv.level, tv)(tv.prov))
      }
    
    lazy val typedParams: Ls[Var -> FieldType] = ctx.nest.nextLevel { implicit ctx =>
      decl match {
        case td: NuTypeDef =>
          td.params.fields.map {
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
              // assert(!mut && !spec, "TODO") // TODO
              // nme -> FieldType(N, freshVar(ttp(nme), N, S(nme.name)))(provTODO)
              nme -> FieldType(N, err(msg"Class parameters currently need type annotations", nme.toLoc))(provTODO)
            case _ => ???
          }
        case fd: NuFunDef => Nil // TODO
      }
    }
    
    
    // val tparams: Ls[(TN, TV, VarianceInfo)] = Nil // TODO
    var isComputing: Bool = false // TODO replace by a Ctx entry
    var result: Opt[TypedNuDecl] = N
    // var result: Opt[A] = N
    
    val tv: TV = freshVar(
      TypeProvenance(decl.toLoc, decl.describe, S(decl.name), decl.isInstanceOf[NuTypeDef]),
      N,
      S(decl.name))(level + 1)
    
    def map(f: TypedNuDecl => TypedNuDecl): LazyTypeInfo = {
      val res = new LazyTypeInfo(decl, implicitly)
      // if (result.nonEmpty) res.result = res
      res.result = result.map(f)
      res
    }
    
    // TODO does this also need freshening in freshenAbove?
    private lazy val thisTV: TV =
      // freshVar(noProv/*FIXME*/, N, S("this_"+decl.name))(lvl + 1)
      freshVar(noProv/*FIXME*/, N, S(decl.name.decapitalize))(lvl + 1)
    
    def complete()(implicit raise: Raise): TypedNuDecl = result.getOrElse {
      if (isComputing) {
        // lastWords(s"TODO cyclic defition ${decl.name}")
        err(msg"Unhandled cyclic definition", decl.toLoc) // TODO better loc/explanation
      }
      // else // TODO avert infinite completion recursion here?
      trace(s"Completing ${decl.showDbg}") {
        println(s"Type params ${tparams.mkString(" ")}")
        println(s"Params ${typedParams.mkString(" ")}")
        
        val res = try {
          isComputing = true
          decl match {
            case fd: NuFunDef =>
              // assert(fd.isLetRec.isEmpty, fd.isLetRec)
              def checkNoTyParams() =
                if (fd.tparams.nonEmpty)
                  err(msg"Type parameters here are not yet supported in this position",
                    fd.tparams.head.toLoc)
              val res_ty = fd.rhs match {
                case R(PolyType(tps, ty)) =>
                  checkNoTyParams()
                  // val body_ty = typeType(ty)(ctx.nextLevel, raise,
                  //   vars = tps.map(tp => tp.name -> freshVar(noProv/*FIXME*/, N)(1)).toMap)
                  val body_ty = 
                  // ctx.nextLevel { implicit ctx: Ctx =>
                  //   // * Note: can't use `ctx.poly` instead of `ctx.nextLevel` because all the methods
                  //   // * in the current typing unit are quantified together.
                  ctx.poly { implicit ctx: Ctx =>
                    typeType(ty)(ctx, raise,
                      vars = vars ++ tps.map(tp => tp.asInstanceOf[L[TN]].value.name -> freshVar(noProv/*FIXME*/, N)(1)).toMap)
                  }
                  // TODO check against `tv`
                  TypedNuFun(ctx.lvl, fd, PolymorphicType(ctx.lvl, body_ty))
                case L(body) =>
                  // println(fd.isLetRec)
                  // implicit val vars: Map[Str, SimpleType] =
                  //   outerVars ++ Map.empty // TODO tparams
                  fd.isLetRec match {
                    case S(true) => // * Let rec bindings
                      checkNoTyParams()
                      implicit val gl: GenLambdas = true
                      TypedNuFun(ctx.lvl, fd, typeTerm(
                        Let(true, fd.nme, body, fd.nme)
                      ))
                    case S(false) => // * Let bindings
                      checkNoTyParams()
                      implicit val gl: GenLambdas = true
                      TypedNuFun(ctx.lvl, fd, typeTerm(body))
                    case N =>
                      /* 
                      implicit val gl: GenLambdas = true
                      val body_ty = typeLetRhs2(isrec = true, fd.nme.name, body)
                      // implicit val prov: TP = noProv // TODO
                      // subsume(body_ty, PolymorphicType(level, tv)) // TODO
                      TypedNuFun(ctx.lvl, fd, body_ty)
                      */
                      
                      // * We don't type functions polymorphically from the point of view of a typing unit
                      // * to avoid cyclic-looking constraints due to the polymorphic recursion limitation,
                      // * as these functions are allowed to be mutually-recursive.
                      // * In the future, we should type each mutual-recursion-component independently
                      // * and polymorphically wrt to non-recursive users of them.
                      implicit val gl: GenLambdas = false
                      val body_ty = ctx.nextLevel { implicit ctx: Ctx =>
                        // * Note: can't use `ctx.poly` instead of `ctx.nextLevel` because all the methods
                        // * in the current typing unit are quantified together.
                        vars ++ fd.tparams.map { tn =>
                          tn.name -> freshVar(TypeProvenance(tn.toLoc, "method type parameter",
                            originName = S(tn.name),
                            isType = true), N)
                        } |> { implicit vars =>
                          typeTerm(body)
                        }
                      }
                      TypedNuFun(ctx.lvl, fd, body_ty)
                  }
              }
              // // subsume(res_ty, tv)
              // constrain(res_ty.ty, tv)
              ctx.nextLevel { implicit ctx: Ctx => constrain(res_ty.ty, tv) }
              res_ty
              
              
            case td: NuTypeDef =>
              
              td.kind match {
                
                case Trt =>
                  err(msg"traits are not yet supported" -> td.toLoc :: Nil)
                  ???
                  
                case Als =>
                  
                  if (td.params.fields.nonEmpty)
                    err(msg"type alias definitions cannot have value parameters" -> td.params.toLoc :: Nil)
                  if (td.parents.nonEmpty)
                    err(msg"type alias definitions cannot extend parents" -> Loc(td.parents) :: Nil)
                  
                  val body_ty = td.sig match {
                    case S(sig) =>
                      typeType(sig)
                    case N =>
                      err(msg"type alias definition requires a right-hand side", td.toLoc)
                  }
                  
                  TypedNuAls(outerCtx.lvl, td, tparams, body_ty)
                  
                case Cls | Nms =>
                  
                  // implicit val prov: TP = noProv // TODO
                  ctx.nest.nextLevel { implicit ctx =>
                    
                    if ((td.kind is Nms) && typedParams.nonEmpty)
                      // * Can we do better? (Memoization semantics?)
                      err(msg"${td.kind.str} parameters are not supported",
                        Loc(typedParams.iterator.map(_._1)))
                    
                    ctx ++= typedParams.map(p => p._1.name -> VarSymbol(p._2.ub, p._1))
                    
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    
                    val sig_ty = typeType(td.sig.getOrElse(Top))
                    td.sig match {
                      case S(sig) =>
                        err(msg"type signatures not yet supported for classes", sig.toLoc)
                      case N => ()
                    }
                    
                    implicit val prov: TP =
                      TypeProvenance(decl.toLoc, decl.describe)
                    
                    // val finalType = freshVar(noProv/*TODO*/, N, S("this"))
                    val finalType = thisTV
                    
                    val tparamMems = tparams.map { case (tp, tv, vi) => // TODO use vi
                      val fldNme = td.nme.name + "#" + tp.name
                      NuParam(Var(fldNme).withLocOf(tp), FieldType(S(tv), tv)(tv.prov), isType = true)
                    }
                    // tparamMems.map(p => p.nme -> p.ty):Int
                    val tparamFields = tparamMems.map(p => p.nme -> p.ty)
                    assert(!typedParams.keys.exists(tparamFields.keys.toSet), ???)
                    
                    
                    def inherit(parents: Ls[Term], superType: ST, members: Ls[NuMember])
                          : (ST, Ls[NuMember]) =
                        parents match {
                    // def inherit(parents: Ls[Term \/ TypedTypingUnit], superType: ST, members: Ls[TypedNuDecl]): Ls[TypedNuDecl] = parents match {
                      // case R(p) :: ps => ???
                      // case L(p) :: ps =>
                      case p :: ps =>
                        val newMembs = trace(s"${lvl}. Inheriting from $p") {
                          val (v @ Var(mxnNme), mxnArgs) = p match {
                            case v @ Var(nme) =>
                              v -> Nil
                            case App(v @ Var(nme), Tup(args)) =>
                              v -> args
                            case _ =>
                              err(msg"Unsupported parent specification", p.toLoc) // TODO
                              return inherit(ps, superType, members)
                          }
                          ctx.get(mxnNme) match {
                            case S(lti: LazyTypeInfo) =>
                              lti.complete().freshen match {
                                case mxn: TypedNuMxn =>
                                  
                                  println(s"Fresh $mxn")
                                  
                                  assert(finalType.level === lvl)
                                  assert(mxn.superTV.level === lvl)
                                  assert(mxn.thisTV.level === lvl)
                                  
                                  constrain(superType, mxn.superTV)
                                  constrain(finalType, mxn.thisTV)
                                  
                                  if (mxnArgs.sizeCompare(mxn.params) =/= 0)
                                    err(msg"mixin $mxnNme expects ${
                                      mxn.params.size.toString} parameters; got ${mxnArgs.size.toString}", Loc(v :: mxnArgs.unzip._2))
                                  
                                  val paramMems = mxn.params.lazyZip(mxnArgs).map { case (nme -> p, _ -> Fld(_, _, a)) => // TODO check name, mut, spec
                                    implicit val genLambdas: GenLambdas = true
                                    val a_ty = typeTerm(a)
                                    p.lb.foreach(constrain(_, a_ty))
                                    constrain(a_ty, p.ub)
                                    NuParam(nme, FieldType(p.lb, a_ty)(provTODO), isType = false)
                                  }
                                  
                                  // TODO check overriding
                                  val bodyMems = mxn.ttu.entities.map(_.complete()).map {
                                    case fun @ TypedNuFun(_, fd, ty) =>
                                      fun
                                    case m: NuMember => m
                                    // case _ => ???
                                  }
                                  
                                  paramMems ++ bodyMems
                                  
                                case cls: TypedNuCls =>
                                  err(msg"Class inheritance is not supported yet (use mixins)", p.toLoc) // TODO
                                  Nil
                                case als: TypedNuAls =>
                                  // TODO dealias first?
                                  err(msg"Cannot inherit from a type alias", p.toLoc)
                                  Nil
                                case cls: TypedNuFun =>
                                  err(msg"Cannot inherit from this", p.toLoc)
                                  Nil
                              }
                            case S(_) =>
                              err(msg"Cannot inherit from this", p.toLoc)
                              Nil
                            case N => 
                              err(msg"Could not find definition `${mxnNme}`", p.toLoc)
                              Nil
                          }
                        }()
                        val newSuperType = 
                          // superType &
                          WithType(
                          superType,
                          RecordType(
                            // newMembs.foldLeft(TopType.toUpper(provTODO))(_ && _.ty.toUpper(provTODO))
                            // newMembs.map(m => m.fd.nme -> m.ty.toUpper(provTODO))
                            newMembs.collect{
                              case m: NuParam => m.nme -> m.ty
                              case m: TypedNuFun => m.fd.nme -> m.ty.toUpper(provTODO)
                            }
                          )(provTODO)
                          )(provTODO)
                        inherit(ps, newSuperType, members ++ newMembs)
                      case Nil =>
                        val thisType = WithType(superType, RecordType(typedParams)(ttp(td.params, isType = true)))(provTODO) &
                          clsNameToNomTag(td)(provTODO, ctx) &
                          RecordType(tparamFields)(TypeProvenance(Loc(td.tparams.map(_._2)), "type parameters", isType = true))
                        trace(s"${lvl}. Finalizing inheritance with $thisType <: $finalType") {
                          assert(finalType.level === lvl)
                          constrain(thisType, finalType)
                          members
                        }()
                        // println(s"${lvl}. Finalized inheritance with $superType ~> $thisType")
                        (thisType, members)
                    }
                    
                    // * We start from an empty super type.
                    val baseType =
                      RecordType(Nil)(TypeProvenance(Loc(td.parents).map(_.left), "Object"))
                    
                    val paramMems = typedParams.map(f => NuParam(f._1, f._2, isType = false))
                    // val baseMems = inherit(td.parents, baseType, Nil)
                    
                    val (thisType, baseMems) =
                      inherit(td.parents, baseType, tparamMems ++ paramMems)
                    
                    // ctx += thisTV
                    
                    // TODO
                    // ctx += "super" -> VarSymbol(superTV, Var("super"))
                    ctx += "super" -> VarSymbol(thisType, Var("super"))
                    
                    val ttu = typeTypingUnit(td.body, allowPure = false) // TODO use
                    
                    // TODO check overriding
                    val clsMems = ttu.entities.map(_.complete())
                    // .map {
                    //   case fun @ TypedNuFun(_, fd, ty) =>
                    //     fun
                    //   // case _ => ???
                    //   case m => m
                    // }
                    
                    // val thisTy = ClassTag(Var(td.name),
                    //       Set.empty//TODO
                    //     )(provTODO)
                    // constrain(thisTy, thisTV)
                    
                    // val thisType = superType &
                    //   clsNameToNomTag(td)(provTODO, ctx) &
                    //   RecordType(tparamFields)(ttp(td.params, isType = true))
                    
                    // val mems = baseMems ++ paramMems ++ clsMems
                    val mems = baseMems ++ clsMems
                    
                    TypedNuCls(outerCtx.lvl, td, ttu,
                      tparams, typedParams, mems.map(d => d.name -> d).toMap,
                      // if (td.kind is Nms) TopType else thisTV
                      TopType
                    )(thisType)
                  }
                case Mxn =>
                  if (td.parents.nonEmpty)
                    err(msg"mixin definitions cannot yet extend parents" -> Loc(td.parents) :: Nil)
                  ctx ++= typedParams.map(p => p._1.name -> VarSymbol(p._2.ub, p._1))
                  val paramMems = typedParams.map(f => NuParam(f._1, f._2, isType = false))
                  ctx.nest.nextLevel { implicit ctx =>
                    implicit val vars: Map[Str, SimpleType] =
                      outerVars ++ Map.empty // TODO type params
                    val thisTV = freshVar(noProv/*FIXME*/, N, S("this"))
                    val superTV = freshVar(noProv/*FIXME*/, N, S("super"))
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    ctx += "super" -> VarSymbol(superTV, Var("super"))
                    // ctx |> { implicit ctx =>
                    val ttu = typeTypingUnit(td.body, allowPure = false)
                    val mems = paramMems ++ttu.entities.map(_.complete())
                    TypedNuMxn(td, thisTV, superTV, tparams, typedParams, mems.map(m => m.name -> m).toMap, ttu)
                    // }
                  }
                // case Als => ???
                // case _ => ???
              }
          }
          
        // } finally { result = S(res); isComputing = false }
        } finally { /* result = S(res); */ isComputing = false }
        
        result = S(res)
        res
        
      }()
    }
    def typeSignature(implicit raise: Raise): ST =
    /* 
        if (isComputing)
          decl match {
            case _: NuFunDef =>
              println(s"Already computing! Using TV: $tv")
              tv // TODO FIXME wrong in general (when accessed from difft scope/level)
            case _ =>
              err(msg"Cyclic definition", decl.toLoc)
          }
        else complete() match {
      case cls: TypedNuCls if cls.td.kind is Nms =>
        ClassTag(Var(cls.td.nme.name), Set.empty)(provTODO)
      case _cls: TypedNuCls =>
        val cls = _cls.freshen.asInstanceOf[TypedNuCls]
        PolymorphicType.mk(cls.level,
          FunctionType(
            TupleType(cls.params.mapKeys(some))(provTODO),
            // cls.tparams.foldLeft(
            //   ClassTag(Var(cls.td.nme.name), Set.empty)(provTODO)
            // ) { case (acc, (tn, tv)) => acc &  }
            ClassTag(Var(cls.td.nme.name), Set.empty)(provTODO) & RecordType.mk(
              cls.tparams.map { case (tn, tv, vi) => // TODO use vi
                Var(cls.td.nme.name + "#" + tn.name).withLocOf(tn) -> FieldType(S(tv), tv)(provTODO) }
            )(provTODO)
          )(provTODO)
        )
      case TypedNuFun(_, fd, ty) =>
        // println(fd, ty)
        // ???
        ty
    }
    */
      decl match {
        case _: NuFunDef =>
          if (isComputing) {
            println(s"Already computing! Using TV: $tv")
            tv // TODO FIXME wrong in general (when accessed from difft scope/level)
          } else complete() match {
            case TypedNuFun(_, fd, ty) =>
              ty
            case _ => die
          }
        case td: NuTypeDef if td.kind is Nms =>
          ClassTag(Var(td.nme.name),
              // TODO base classes
              // Set.empty
              Set.single(TN("Eql"))
            )(provTODO)
        case td: NuTypeDef if td.kind is Cls =>
          PolymorphicType.mk(level,
            FunctionType(
              TupleType(typedParams.mapKeys(some))(provTODO),
              ClassTag(Var(td.nme.name),
                // TODO base classes
                // Set.empty
                Set.single(TypeName("Eql"))
              )(provTODO) & RecordType.mk(
                tparams.map { case (tn, tv, vi) => // TODO use vi
                  Var(td.nme.name + "#" + tn.name).withLocOf(tn) -> FieldType(S(tv), tv)(provTODO) }
              )(provTODO)
            )(provTODO)
          )
      }
    
    def force()(implicit raise: Raise): TypedNuDecl = {
      val res = complete()
      res.force()
      // decl match {
      //   case td: NuTypeDef =>
      //     td.kind match {
      //       case Cls | Nms =>
      //         // implicit val prov: TP = noProv // TODO
      //         // val thisTy = ClassTag(Var(td.name),
      //         //       Set.empty//TODO
      //         //     )(provTODO)
      //         // constrain(thisTy, thisTV)
      //       case _ =>
      //     }
      //   case _ =>
      // }
      res match {
        case cls: TypedNuCls =>
          // implicit val prov: TP = noProv // TODO
          // constrain(cls.instanceType, thisTV)
          // println(cls.variances)
        case _ =>
      }
      res
    }
    override def toString: String =
      s"${decl.name} ~> ${if (isComputing) "<computing>" else result.fold("<uncomputed>")(_.toString)}"
    
  }
  
  
  
}

