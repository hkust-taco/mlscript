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
  
  
  type Params = Ls[Var -> FieldType]
  type TyParams = Ls[(TN, TV, Opt[VarianceInfo])]
  
  
  sealed abstract class NuDeclInfo
  
  case class FunInfo() extends NuDeclInfo
  case class TypeDefInfo() extends NuDeclInfo
  
  
  sealed trait NuMember {
    def name: Str
    def kind: DeclKind
    
    /** Used in inheritance processing, for parent types. */
    def freshen(implicit ctx: Ctx): NuMember
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : NuMember
    
    def map(f: ST => ST)(implicit ctx: Ctx): NuMember =
      mapPol(N, false)((_, ty) => f(ty))
    
    // TODO rm – just use `mapPolMap`
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember
    
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember
  }
  
  
  case class NuParam(nme: Var, ty: FieldType, isType: Bool) extends NuMember {
    def name: Str = nme.name
    def kind: DeclKind = Val
    def typeSignature: ST = ty.ub
    
    def freshen(implicit ctx: Ctx): NuMember = this
    
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
  
  
  // TODO:
  // case class NuTypeParam(nme: TN, ty: FieldType) extends NuMember {
  //   def name: Str = nme.name
  //   
  //   def freshenAbove(lim: Int, rigidify: Bool)
  //         (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
  //         : NuParam =
  //     NuParam(nme, ty.freshenAbove(lim, rigidify))
  // }
  
  
  sealed trait TypedNuDecl extends NuMember {
    def name: Str
    def level: Level
    
    def freshen(implicit ctx: Ctx): NuMember = {
      implicit val freshened: MutMap[TV, ST] = MutMap.empty
      implicit val shadows: Shadows = Shadows.empty
      ctx.copy(lvl = level + 1) |> { implicit ctx =>
        freshenAbove(level, rigidify = false)
      }
    }
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuDecl
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuDecl
  }
  
  
  /** Those declarations that introduce term names in scope. */
  sealed trait TypedNuTermDef extends TypedNuDecl with AnyTypeDef {
    def typeSignature: ST
  }
  
  
  sealed abstract class TypedNuTypeDef(kind: TypeDefKind) extends TypedNuDecl {
    def nme: TypeName
    def decl: NuTypeDef
    def tparams: TyParams
    
    override def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST]): TypedNuTypeDef = 
      this match {
        case m @ TypedNuMxn(td, thisTV, superTV, tparams, params, members, ttu) =>
          TypedNuMxn(td,
            thisTV.freshenAbove(lim, rigidify),
            superTV.freshenAbove(lim, rigidify),
            tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
            params.mapValues(_.freshenAbove(lim, rigidify)),
            members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
            ttu.freshenAbove(lim, rigidify))
        case cls @ TypedNuCls(level, td, ttu, tparams, params, members, thisTy) =>
          TypedNuCls(level, td, ttu.freshenAbove(lim, rigidify),
            tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
            params.mapValues(_.freshenAbove(lim, rigidify)),
            members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
            thisTy.freshenAbove(lim, rigidify),
          )(cls.instanceType.freshenAbove(lim, rigidify))
        case cls @ TypedNuAls(level, td, tparams, body) =>
          TypedNuAls(level, td,
            tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
            body.freshenAbove(lim, rigidify))
      }
    val td: NuTypeDef
    val prov: TP = TypeProvenance(td.toLoc, td.describe, isType = true)
    val level: Level
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level = ???
  }
  
  
  case class TypedNuAls(level: Level, td: NuTypeDef, tparams: TyParams, body: ST)
    extends TypedNuTypeDef(Als)
  {
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def name: Str = nme.name
    def nme: mlscript.TypeName = td.nme
    
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
  
  
  case class TypedNuCls(
        level: Level, td: NuTypeDef, ttu: TypedTypingUnit,
        tparams: TyParams, params: Ls[Var -> FieldType],
        members: Map[Str, NuMember], thisTy: ST, //typeSignature: ST,
      )(val instanceType: ST, // * only meant to be used in `force` and `variances`
      ) extends TypedNuTypeDef(Cls) with TypedNuTermDef
  {
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def nme: TypeName = td.nme
    def name: Str = nme.name
    
    def typeSignature: ST = typeSignatureOf(td, level, tparams, params)
    
    
    // TODO
    // def checkVariances
    
    // lazy val explicitVariances: VarianceStore =
    //   MutMap.from(tparams.iterator.map(tp => tp._2 -> tp._3.getOrElse(VarianceInfo.in)))
    
    // TODO should we really recompute them on freshened instances, or can we avoid that?
    private var _variances: Opt[VarianceStore] = N
    def variances(implicit ctx: Ctx): VarianceStore = {
      _variances match {
        case S(res) => res
        case N => trace(s"Computing variances of ${this.name}") {
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
          Trav(PolMap.pos)(instanceType)
          
          // TODO check consistency with explicitVariances
          val res = store ++ tparams.iterator.collect { case (_, tv, S(vi)) => tv -> vi }
          
          _variances = S(res)
          
          res
        }(r => s"= $r")
      }
    }
    
    def varianceOf(tv: TV)(implicit ctx: Ctx): VarianceInfo =
      variances.getOrElse(tv, VarianceInfo.in)
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
        TypedNuCls(level, td, ttu,
          tparams.map(tp => (tp._1, f(N, tp._2).asInstanceOf[TV], tp._3)),
          params.mapValues(_.update(t => f(pol.map(!_), t), t => f(pol, t))),
          members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap,
          f(pol.map(!_), thisTy),
        )(f(pol, instanceType))
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
        TypedNuCls(level, td, ttu,
          tparams.map(tp => (tp._1, f(pol.invar, tp._2).asInstanceOf[TV], tp._3)),
          params.mapValues(_.update(t => f(pol.contravar, t), t => f(pol, t))),
          members.mapValuesIter(_.mapPolMap(pol)(f)).toMap,
          f(pol.contravar, thisTy),
        )(f(pol, instanceType))
  }
  
  
  case class TypedNuMxn(
        td: NuTypeDef, thisTV: ST, superTV: ST,
        tparams: TyParams, params: Ls[Var -> FieldType],
        members: Map[Str, NuMember], ttu: TypedTypingUnit,
      ) extends TypedNuTypeDef(Mxn)
  {
    val level: Level = thisTV.level - 1 // TODO cleaner
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def nme: TypeName = td.nme
    def name: Str = nme.name
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuMxn =
      TypedNuMxn(td, f(pol.map(!_), thisTV), f(pol.map(!_), superTV),
        tparams.map(tp => (tp._1, f(N, tp._2).asInstanceOf[TV], tp._3)),
        params.mapValues(_.update(t => f(pol.map(!_), t), t => f(pol, t))),
        members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap, ttu)
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuMxn =
      TypedNuMxn(td, f(pol.contravar, thisTV), f(pol.contravar, superTV),
        tparams.map(tp => (tp._1, f(pol.invar, tp._2).asInstanceOf[TV], tp._3)),
        params.mapValues(_.update(t => f(pol.contravar, t), t => f(pol, t))),
        members.mapValuesIter(_.mapPolMap(pol)(f)).toMap, ttu)
  }
  
  
  /** Note: the type `bodyType` is stored *without* its polymorphic wrapper! (unlike `typeSignature`) */
  case class TypedNuFun(level: Level, fd: NuFunDef, bodyType: ST) extends TypedNuDecl with TypedNuTermDef {
    def kind: DeclKind = Val
    def name: Str = fd.nme.name
    lazy val typeSignature: ST = PolymorphicType.mk(level, bodyType)
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : TypedNuFun = this match {
      case TypedNuFun(level, fd, ty) =>
        TypedNuFun(level min ctx.lvl, fd, ty.freshenAbove(lim, rigidify))
    }
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      TypedNuFun(level, fd, f(pol, bodyType))
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      TypedNuFun(level, fd, f(pol, bodyType))
  }
  
  
  case class TypedTypingUnit(entities: Ls[NuMember], result: Opt[ST]) extends OtherTypeLike {
    def map(f: ST => ST)(implicit ctx: Ctx): TypedTypingUnit =
      TypedTypingUnit(entities.map(_.map(f)), result.map(f))
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedTypingUnit =
      TypedTypingUnit(entities.map(_.mapPol(pol, smart)(f)), result.map(f(pol, _)))
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedTypingUnit =
      TypedTypingUnit(entities.map(_.mapPolMap(pol)(f)), result.map(f(pol, _)))
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : TypedTypingUnit =
      TypedTypingUnit(entities.map(_.freshenAbove(lim, rigidify)//.asInstanceOf[TypedNuTermDef]
        )
        , result.map(_.freshenAbove(lim, rigidify)))
  }
  
  
  def typeSignatureOf(td: NuTypeDef, level: Level, tparams: TyParams, params: Params): ST = td.kind match {
    case Nms =>
      ClassTag(Var(td.nme.name),
          // TODO base classes
          Set.single(TN("Eql"))
        )(provTODO)
    case Cls =>
      PolymorphicType.mk(level,
        FunctionType(
          TupleType(params.mapKeys(some))(provTODO),
          ClassTag(Var(td.nme.name),
            // TODO base classes
            Set.single(TypeName("Object")) + TypeName("Eql")
          )(provTODO) & RecordType.mk(
            tparams.map { case (tn, tv, vi) => // TODO use vi
              Var(td.nme.name + "#" + tn.name).withLocOf(tn) -> FieldType(S(tv), tv)(provTODO) }
          )(provTODO)
        )(provTODO)
      )
    // case k => err
    case k => errType // FIXME
  }
  
  
  
  /** Type checks a typing unit, which is a sequence of possibly-nutually-recursive type and function definitions
   *  interleaved with plain statements. */
  def typeTypingUnit(tu: TypingUnit, topLevel: Bool)
        (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType]): TypedTypingUnit =
      trace(s"${ctx.lvl}. Typing $tu")
  {
    // println(s"vars ${vars}")
    
    val named = mutable.Map.empty[Str, LazyTypeInfo]
    
    // * Not sure we should support declaring signature with the `ident: type` syntax
    // val (signatures, otherEntities) = tu.entities.partitionMap {
    //   case Asc(v: Var, ty) => L(v -> ty)
    //   case s => R(s)
    // }
    val (decls, statements) = tu.entities.partitionMap {
      case decl: NuDecl => L(decl)
      case s => R(s)
    }
    val implems = if (topLevel) decls else decls.filter {
      case NuFunDef(N, nme, tparams, R(rhs)) => false // There will already be typed in DelayedTypeInfo
      case _ => true
    }
    val infos = implems.map {
      case decl: NuDecl =>
        val lti = new DelayedTypeInfo(decl, implicitly)
        decl match {
          case td: NuTypeDef =>
            ctx.tyDefs2 += td.nme.name -> lti
          case _: NuFunDef =>
        }
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
    }
    ctx ++= infos
    
    // * Complete typing of block definitions and add results to context
    val completedInfos = infos.mapValues(_.complete() |> (res => CompletedTypeInfo(res)))
    ctx ++= completedInfos
    
    // * Type the block statements
    def go(stmts: Ls[Statement]): Opt[ST] = stmts match {
      case s :: stmts =>
        val res_ty = s match {
          case decl: NuDecl => N
          case s: Statement =>
            val (diags, dss) = s.desugared
            diags.foreach(raise)
            S(typeTerms(dss, false, Nil)(ctx, raise, TypeProvenance(s.toLoc, s match {
              case trm: Term => trm.describe
              case s => "statement"
            }), vars, genLambdas = false))
        }
        stmts match {
          case Nil => res_ty
          case stmts =>
            // TODO check discarded non-unit values
            go(stmts)
        }
      case Nil => N
    }
    val res_ty = trace("Typing unit statements") { go(statements) } (r => s": $r")
    
    TypedTypingUnit(completedInfos.map(_._2.member), res_ty)
    
  }()
  
  
  
  
  trait DelayedTypeInfoImpl { this: DelayedTypeInfo =>
    private def outerCtx = ctx
    
    var isComputing: Bool = false // Replace by a Ctx entry?
    var result: Opt[TypedNuDecl] = N
    
    val level: Level = ctx.lvl
    
    val kind: DeclKind = decl.kind
    
    private implicit val prov: TP =
      TypeProvenance(decl.toLoc, decl.describe)
    
    println(s"${ctx.lvl}. Created lazy type info for $decl")
    
    lazy val tparams: TyParams = ctx.nest.nextLevel { implicit ctx =>
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
    
    lazy private implicit val vars: Map[Str, SimpleType] =
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
        case fd: NuFunDef => Nil
      }
    }
    
    lazy val paramSymbols = typedParams.map(p => p._1.name -> VarSymbol(p._2.ub, p._1))
    
    // TODO also import signatures from base classes and mixins!
    lazy val typedSignatures: Ls[(NuFunDef, ST)] = decl match {
      case td: NuTypeDef => ctx.nest.nextLevel { implicit ctx =>
        val (signatures, rest) = td.body.entities.partitionMap {
          case fd @ NuFunDef(N, nme, tparams, R(rhs)) =>
            L((fd, rhs))
          // TODO also pick up signature off implems with typed params/results
          case s => R(s)
        }
        // TODO use `rest`
        
        ctx ++= paramSymbols
        
        signatures.map { case (fd, rhs) =>
          (fd, ctx.poly { implicit ctx: Ctx =>
            vars ++ fd.tparams.map { tn =>
              tn.name -> freshVar(TypeProvenance(tn.toLoc, "method type parameter",
                originName = S(tn.name),
                isType = true), N, S(tn.name))
            } |> { implicit vars =>
              
              typeType(rhs).withProv(
                TypeProvenance(Loc(rhs :: fd.nme :: fd.tparams), s"signature of member ${fd.nme.name}")
              )
              
            }
          })
        }
      }
      case _: NuFunDef => Nil
    }
    lazy val typedSignatureMembers: Ls[Str -> TypedNuFun] =
      typedSignatures.iterator.map { case (fd, ty) =>
        fd.nme.name -> TypedNuFun(level + 1, fd, ty)
      }.toList
    
    lazy val allFields: Set[Var] = decl match {
      case td: NuTypeDef =>
        // TODO also get fields from parents!
        (td.params.fields.iterator.flatMap(_._1) ++ td.body.entities.iterator.collect {
          case fd: NuFunDef => fd.nme
        }).toSet
      case _: NuFunDef => Set.empty
    }
    
    lazy val typedFields: Map[Var, FieldType] =
      typedParams.toMap ++ typedSignatures.iterator.map(fd_ty => fd_ty._1.nme -> fd_ty._2.toUpper(noProv))
    
    lazy val mutRecTV: TV = freshVar(
      TypeProvenance(decl.toLoc, decl.describe, S(decl.name), decl.isInstanceOf[NuTypeDef]),
      N,
      S(decl.name))(level + 1)
    
    private lazy val thisTV: TV =
      freshVar(provTODO, N, S(decl.name.decapitalize))(lvl + 1)
    
    
    def complete()(implicit raise: Raise): TypedNuDecl = result.getOrElse {
      if (isComputing) {
        val ty = err(msg"Unhandled cyclic definition", decl.toLoc)
        // * Hacky: return a dummy decl to avoid possible infinite completion recursions
        TypedNuFun(0, NuFunDef(N, decl.nameVar, Nil, R(Top))(N), ty)
      }
      else trace(s"Completing ${decl.showDbg}") {
        println(s"Type params ${tparams.mkString(" ")}")
        println(s"Params ${typedParams.mkString(" ")}")
        
        val res = try {
          isComputing = true
          decl match {
            case fd: NuFunDef =>
              def checkNoTyParams() =
                if (fd.tparams.nonEmpty)
                  err(msg"Type parameters here are not yet supported in this position",
                    fd.tparams.head.toLoc)
              val res_ty = fd.rhs match {
                case R(PolyType(tps, ty)) =>
                  checkNoTyParams()
                  val body_ty = ctx.poly { implicit ctx: Ctx =>
                    typeType(ty)(ctx, raise,
                      vars = vars ++ tps.map(tp => tp.asInstanceOf[L[TN]].value.name -> freshVar(provTODO, N)(1)).toMap)
                  }
                  TypedNuFun(ctx.lvl, fd, PolymorphicType(ctx.lvl, body_ty))
                case R(_) => die
                case L(body) =>
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
                      // * We don't type functions polymorphically from the point of view of a typing unit
                      // * to avoid cyclic-looking constraints due to the polymorphic recursion limitation,
                      // * as these functions are allowed to be mutually-recursive.
                      // * In the future, we should type each mutual-recursion-component independently
                      // * and polymorphically wrt to external uses of them.
                      implicit val gl: GenLambdas = false
                      val body_ty = ctx.nextLevel { implicit ctx: Ctx =>
                        // * Note: can't use `ctx.poly` instead of `ctx.nextLevel` because all the methods
                        // * in the current typing unit are quantified together.
                        vars ++ fd.tparams.map { tn =>
                          tn.name -> freshVar(TypeProvenance(tn.toLoc, "method type parameter",
                            originName = S(tn.name),
                            isType = true), N, S(tn.name))
                        } |> { implicit vars =>
                          typeTerm(body)
                        }
                      }.withProv(TypeProvenance(fd.toLoc, s"definition of method ${fd.nme.name}"))
                      TypedNuFun(ctx.lvl, fd, body_ty)
                  }
              }
              ctx.nextLevel { implicit ctx: Ctx => constrain(res_ty.bodyType, mutRecTV) }
              res_ty
              
              
            case td: NuTypeDef =>
              
              val signatures = typedSignatures
              ctx ++= signatures.map(nt => nt._1.name -> VarSymbol(nt._2, nt._1.nme))
              
              val (res, funMembers) = td.kind match {
                
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
                  
                  TypedNuAls(outerCtx.lvl, td, tparams, body_ty) -> Nil
                  
                case Cls | Nms =>
                  
                  ctx.nest.nextLevel { implicit ctx =>
                    
                    if ((td.kind is Nms) && typedParams.nonEmpty)
                      // * Can we do better? (Memoization semantics?)
                      err(msg"${td.kind.str} parameters are not supported",
                        Loc(typedParams.iterator.map(_._1)))
                    
                    ctx ++= paramSymbols
                    
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    
                    val sig_ty = typeType(td.sig.getOrElse(Top))
                    td.sig match {
                      case S(sig) =>
                        err(msg"type signatures not yet supported for classes", sig.toLoc)
                      case N => ()
                    }
                    
                    implicit val prov: TP =
                      TypeProvenance(decl.toLoc, decl.describe)
                    
                    val finalType = thisTV
                    
                    val tparamMems = tparams.map { case (tp, tv, vi) => // TODO use vi
                      val fldNme = td.nme.name + "#" + tp.name
                      NuParam(Var(fldNme).withLocOf(tp), FieldType(S(tv), tv)(tv.prov), isType = true)
                    }
                    val tparamFields = tparamMems.map(p => p.nme -> p.ty)
                    assert(!typedParams.keys.exists(tparamFields.keys.toSet), ???)
                    
                    
                    def inherit(parents: Ls[Term], superType: ST, members: Ls[NuMember])
                          : (ST, Ls[NuMember]) =
                        parents match {
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
                                  val bodyMems = mxn.ttu.entities
                                  
                                  paramMems ++ bodyMems
                                  
                                case cls: TypedNuCls =>
                                  err(msg"Class inheritance is not supported yet (use mixins)", p.toLoc) // TODO
                                  Nil
                                case als: TypedNuAls =>
                                  // TODO dealias first?
                                  err(msg"Cannot inherit from a type alias", p.toLoc)
                                  Nil
                                case als: NuParam =>
                                  // TODO first-class mixins/classes...
                                  err(msg"Cannot inherit from a parameter", p.toLoc)
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
                        val newSuperType = WithType(
                          superType,
                          RecordType(
                            newMembs.collect{
                              case m: NuParam => m.nme -> m.ty
                              case m: TypedNuFun => m.fd.nme -> m.typeSignature.toUpper(provTODO)
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
                    
                    val (thisType, baseMems) =
                      inherit(td.parents, baseType, tparamMems ++ paramMems)
                    
                    ctx += "super" -> VarSymbol(thisType, Var("super"))
                    
                    val ttu = typeTypingUnit(td.body, topLevel = false)
                    
                    // TODO report non-unit result/statements?
                    // TODO check overriding
                    val clsMems = ttu.entities
                    
                    val impltdMems = baseMems ++ clsMems
                    val mems = impltdMems.map(d => d.name -> d).toMap ++ typedSignatureMembers
                    
                    TypedNuCls(outerCtx.lvl, td, ttu,
                      tparams, typedParams, mems,
                      // if (td.kind is Nms) TopType else thisTV
                      TopType
                    )(thisType) -> impltdMems
                  }
                case Mxn =>
                  if (td.parents.nonEmpty)
                    err(msg"mixin definitions cannot yet extend parents" -> Loc(td.parents) :: Nil)
                  ctx.nest.nextLevel { implicit ctx =>
                    ctx ++= paramSymbols
                    val paramMems = typedParams.map(f => NuParam(f._1, f._2, isType = false))
                    implicit val vars: Map[Str, SimpleType] =
                      outerVars ++ Map.empty // TODO type params
                    val thisTV = freshVar(provTODO, N, S("this"))
                    val superTV = freshVar(provTODO, N, S("super"))
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    ctx += "super" -> VarSymbol(superTV, Var("super"))
                    val ttu = typeTypingUnit(td.body, topLevel = false)
                    val impltdMems = paramMems ++ ttu.entities
                    val mems = impltdMems.map(m => m.name -> m).toMap ++ typedSignatureMembers
                    TypedNuMxn(td, thisTV, superTV, tparams, typedParams, mems, ttu) -> impltdMems
                  }
              }
              
              // TODO check member duplication? in mems or before?
              
              // * Check signatures
              // val isAbstract = // TODO
              ctx.nextLevel { implicit ctx: Ctx => 
                typedSignatures.foreach { case (fd, sign) =>
                  implicit val prov: TP = sign.prov
                  funMembers.find(m => m.name === fd.nme.name) match {
                    case S(mem: TypedNuTermDef) =>
                      val memSign = mem.typeSignature
                      implicit val prov: TP = memSign.prov
                      constrain(memSign, sign)
                    case S(mem: NuParam) =>
                    case S(_) => ??? // TODO
                    case N =>
                      if (!td.isDecl)
                        err(msg"Member ${fd.nme.name} is declared but not defined", fd.nme.toLoc)
                  }
                }
              }
              
              res
          }
          
        } finally { isComputing = false }
        
        result = S(res)
        res
        
      }()
    }
    def typeSignature(implicit raise: Raise): ST =
      decl match {
        case _: NuFunDef =>
          if (isComputing) {
            println(s"Already computing! Using TV: $mutRecTV")
            mutRecTV // TODO make sure this is never misused (ie not accessed from difft scope/level)
          } else complete() match {
            case TypedNuFun(_, fd, ty) =>
              ty
            case _ => die
          }
        case td: NuTypeDef =>
          typeSignatureOf(td, level, tparams, typedParams)
      }
    
    override def toString: String =
      s"${decl.name} ~> ${if (isComputing) "<computing>" else result.fold("<uncomputed>")(_.toString)}"
    
  }
  
  
  
}

