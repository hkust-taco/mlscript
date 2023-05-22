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
    def level: Level
    
    protected def withLevel[R](k: Ctx => R)(implicit ctx: Ctx): R = k(ctx.copy(lvl = level + 1))
    
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
  
  
  case class NuParam(nme: NameRef, ty: FieldType)(val level: Level) extends NuMember {
    def name: Str = nme.name
    def isType: Bool = nme.isInstanceOf[TypeName]
    def kind: DeclKind =
      if (isType) Als // FIXME?
      else Val
    def typeSignature: ST = ty.ub
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : NuParam =
      NuParam(nme, ty.freshenAbove(lim, rigidify))(level)
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember =
        NuParam(nme, ty.update(t => f(pol.map(!_), t), t => f(pol, t)))(level)
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember =
        NuParam(nme, ty.update(t => f(pol.contravar, t), t => f(pol, t)))(level)
  }
  
  
  /* 
  // TODO:
  case class NuTypeParam(nme: TN, ty: FieldType)(val level: Level) extends NuMember {
    def name: Str = nme.name
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : NuTypeParam =
      NuTypeParam(nme, ty.freshenAbove(lim, rigidify))(level)
      
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember =
        NuTypeParam(nme, ty.update(t => f(pol.map(!_), t), t => f(pol, t)))(level)
    
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuMember =
        NuTypeParam(nme, ty.update(t => f(pol.contravar, t), t => f(pol, t)))(level)
    
    def kind: DeclKind = Als // FIXME?
  }
  */
  
  sealed trait TypedNuDecl extends NuMember {
    def name: Str
    def level: Level
    
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
    def members: Map[Str, NuMember]
    val allFields: Set[Var] = members.valuesIterator.map(_.name |> Var).toSet
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
    def members: Map[Str, NuMember] = Map.empty

    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST])
          : TypedNuAls = withLevel { implicit ctx =>
      TypedNuAls(level, td,
        tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
        body.freshenAbove(lim, rigidify))
    }
    
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
  
  sealed trait PolyNuDecl extends TypedNuDecl {
    def tparams: TyParams
  }
  
  
  case class TypedNuTrt(
        level: Level, td: NuTypeDef, ttu: TypedTypingUnit,
        tparams: TyParams,
        members: Map[Str, NuMember],
        thisTy: ST,
        sign: Opt[ST],
        selfTy: ST,
        inheritedTags: Set[TypeName],
        parentTP: Map[Str, NuMember]
      ) extends TypedNuTypeDef(Trt) with PolyNuDecl
  {
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def nme: TypeName = td.nme
    def name: Str = nme.name

    lazy val virtualMembers: Map[Str, NuMember] = members ++ tparams.map {
                      case (nme @ TypeName(name), tv, _) => 
                        td.nme.name+"#"+name -> NuParam(nme, FieldType(S(tv), tv)(provTODO))(level)
                    } ++ parentTP

    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST])
          : TypedNuTrt = withLevel { implicit ctx =>
      TypedNuTrt(level, td, ttu.freshenAbove(lim, rigidify),
        tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
        members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
        thisTy.freshenAbove(lim, rigidify),
        sign.map(_.freshenAbove(lim, rigidify)),
        selfTy.freshenAbove(lim, rigidify),
        inheritedTags,
        parentTP.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap
      )
    }
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTrt =
        TypedNuTrt(level, td, ttu,
          tparams.map(tp => (tp._1, f(N, tp._2).asInstanceOf[TV], tp._3)),
          members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap,
          f(pol.map(!_), thisTy),
          sign.map(f(pol, _)),
          f(pol, selfTy),
          inheritedTags,
          parentTP.mapValuesIter(_.mapPol(pol, smart)(f)).toMap
        )
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTrt =
        TypedNuTrt(level, td, ttu,
          tparams.map(tp => (tp._1, f(pol.invar, tp._2).asInstanceOf[TV], tp._3)),
          members.mapValuesIter(_.mapPolMap(pol)(f)).toMap,
          f(pol.contravar, thisTy),
          sign.map(f(pol, _)),
          f(pol, selfTy),
          inheritedTags,
          parentTP.mapValuesIter(_.mapPolMap(pol)(f)).toMap
        )
  }
  
  
  case class TypedNuCls(
        level: Level, td: NuTypeDef, ttu: TypedTypingUnit,
        tparams: TyParams, params: Ls[Var -> FieldType],
        members: Map[Str, NuMember], thisTy: ST, //typeSignature: ST,
        selfTy: ST,
        inheritedTags: Set[TypeName],
        parentTP: Map[Str, NuMember]
      )(val instanceType: ST, // * only meant to be used in `force` and `variances`
      ) extends TypedNuTypeDef(Cls) with TypedNuTermDef with PolyNuDecl
  {
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def nme: TypeName = td.nme
    def name: Str = nme.name
    
    def typeSignature: ST = typeSignatureOf(td, level, tparams, params, selfTy, inheritedTags)
    
    /** Includes class-name-coded type parameter fields. */
    lazy val virtualMembers: Map[Str, NuMember] = members ++ tparams.map {
                      case (nme @ TypeName(name), tv, _) => 
                        td.nme.name+"#"+name -> NuParam(nme, FieldType(S(tv), tv)(provTODO))(level)
                    } ++ parentTP
    
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

    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST])
          : TypedNuCls = withLevel { implicit ctx =>
      TypedNuCls(level, td, ttu.freshenAbove(lim, rigidify),
        tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
        params.mapValues(_.freshenAbove(lim, rigidify)),
        members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
        thisTy.freshenAbove(lim, rigidify),
        selfTy.freshenAbove(lim, rigidify),
        inheritedTags,
        parentTP.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap
      )(this.instanceType.freshenAbove(lim, rigidify))
    }
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
        TypedNuCls(level, td, ttu,
          tparams.map(tp => (tp._1, f(N, tp._2).asInstanceOf[TV], tp._3)),
          params.mapValues(_.update(t => f(pol.map(!_), t), t => f(pol, t))),
          members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap,
          f(pol.map(!_), thisTy),
          f(pol, selfTy),
          inheritedTags,
          parentTP.mapValuesIter(_.mapPol(pol, smart)(f)).toMap,
        )(f(pol, instanceType))
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
        TypedNuCls(level, td, ttu,
          tparams.map(tp => (tp._1, f(pol.invar, tp._2).asInstanceOf[TV], tp._3)),
          params.mapValues(_.update(t => f(pol.contravar, t), t => f(pol, t))),
          members.mapValuesIter(_.mapPolMap(pol)(f)).toMap,
          f(pol.contravar, thisTy),
          f(pol, selfTy),
          inheritedTags,
          parentTP.mapValuesIter(_.mapPolMap(pol)(f)).toMap,
        )(f(pol, instanceType))
  }
  
  
  case class TypedNuMxn(
        td: NuTypeDef, thisTV: ST, superTV: ST,
        tparams: TyParams, params: Ls[Var -> FieldType],
        members: Map[Str, NuMember], ttu: TypedTypingUnit,
      ) extends TypedNuTypeDef(Mxn) with PolyNuDecl
  {
    val level: Level = thisTV.level - 1 // TODO cleaner
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def nme: TypeName = td.nme
    def name: Str = nme.name

    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST])
          : TypedNuMxn = withLevel { implicit ctx =>
      TypedNuMxn(td,
        thisTV.freshenAbove(lim, rigidify),
        superTV.freshenAbove(lim, rigidify),
        tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
        params.mapValues(_.freshenAbove(lim, rigidify)),
        members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
        ttu.freshenAbove(lim, rigidify)
      )
    }
    
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
  
  
  /** Used when there was an error while tying a definition. */
  case class TypedNuDummy(d: NuDecl) extends TypedNuDecl with TypedNuTermDef {
    def level = MinLevel
    def kind: DeclKind = Val
    def name: Str = d.name
    def typeSignature: ST = errType
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST]) =
      this
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      this
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      this
  }
  
  
  /** Note: the type `bodyType` is stored *without* its polymorphic wrapper! (unlike `typeSignature`) */
  case class TypedNuFun(level: Level, fd: NuFunDef, bodyType: ST) extends TypedNuDecl with TypedNuTermDef {
    def kind: DeclKind = Val
    def name: Str = fd.nme.name
    lazy val typeSignature: ST = PolymorphicType.mk(level, bodyType)
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : TypedNuFun = withLevel { implicit ctx => this match {
      case TypedNuFun(level, fd, ty) =>
        TypedNuFun(level min ctx.lvl, fd, ty.freshenAbove(lim, rigidify))
          // .tap(res => println(s"Freshen[$level,${ctx.lvl}] $this ~> $res"))
    }}
    
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
  
  
  def typeSignatureOf(td: NuTypeDef, level: Level, tparams: TyParams, params: Params, selfTy: ST, ihtags: Set[TypeName]): ST = td.kind match {
    case Nms =>
      ClassTag(Var(td.nme.name),
          ihtags + TN("Eql")  // Eql and ihtags (parent tags)
        )(provTODO)
    case Cls =>
      PolymorphicType.mk(level,
        FunctionType(
          TupleType(params.mapKeys(some))(provTODO),
          ClassTag(Var(td.nme.name),
            ihtags + TN("Eql") // Eql and ihtags (parent tags)
          )(provTODO) & selfTy & RecordType.mk(
            tparams.map { case (tn, tv, vi) => // TODO use vi
              Var(td.nme.name + "#" + tn.name).withLocOf(tn) -> FieldType(S(tv), tv)(provTODO) }
          )(provTODO)
        )(provTODO)
      )
    // case k => err
    case k => errType // FIXME
  }
  
  
  
  /** Type checks a typing unit, which is a sequence of possibly-mutually-recursive type and function definitions
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
    val funSigs = MutMap.empty[Str, NuFunDef]
    val implems = if (topLevel) decls else decls.filter {
      case fd @ NuFunDef(N, nme, tparams, R(rhs)) =>
        funSigs.updateWith(nme.name) {
          case S(s) =>
            err(s"A type signature for '$nme' has already been given", fd.toLoc)
            S(s)
          case N => S(fd)
        }
        false // There will already be typed in DelayedTypeInfo
      case _ => true
    }
    val infos = implems.map {
      case _decl: NuDecl =>
        val decl = _decl match {
          case fd: NuFunDef =>
            assert(fd.signature.isEmpty)
            funSigs.get(fd.nme.name) match {
              case S(sig) =>
                fd.copy()(fd.declareLoc, S(sig))
              case _ =>
                fd
            }
          case _ => _decl
        }
        val lti = new DelayedTypeInfo(decl, implicitly)
        decl match {
          case td: NuTypeDef =>
            ctx.tyDefs2 += td.nme.name -> lti
          case _: NuFunDef =>
        }
        named.updateWith(decl.name) {
          case sv @ S(v) =>
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

    type ParentSpec = (Term, Var, Ls[Type], Ls[Opt[Var] -> Fld])
    val parentSpecs: Ls[ParentSpec] = decl match {
      case td: NuTypeDef => 
        td.parents.flatMap {
          case v @ Var(nme) =>
            S(v, v, Nil, Nil)
          case p @ App(v @ Var(nme), Tup(args)) =>
            S(p, v, Nil, args)
          case TyApp(v @ Var(nme), targs) =>
            S(v, v, targs, Nil)
          case p @ App(TyApp(v @ Var(nme), targs), Tup(args)) =>
            S(p, v, targs, args)
          case p =>
            err(msg"Unsupported parent specification", p.toLoc) // TODO
            N
        }
      case _ => Nil
    }
    
    type TypedParentSpec = (TypedNuTypeDef, Ls[NuMember], Map[Str, NuMember], Opt[Loc])
    
    lazy val typedParents: Ls[TypedParentSpec] = ctx.nest.nextLevel { implicit ctx =>
      
      ctx ++= paramSymbols
      
      parentSpecs.flatMap {
        case (p, v @ Var(parNme), parTargs, parArgs) =>
          trace(s"${lvl}. Typing parent spec $p") {
            ctx.get(parNme) match {
              case S(lti: LazyTypeInfo) =>
                val info = lti.complete()
                info match {
                  
                  case rawMxn: TypedNuMxn =>
                    
                    // println(s"Raw $rawMxn")
                    val (fr, ptp) = refreshHelper(rawMxn, v, N) // type args inferred
                    implicit val frenshened: MutMap[TV,ST] = fr
                    implicit val shadows: Shadows = Shadows.empty
                    val mxn = rawMxn.freshenAbove(info.level, rigidify = false)
                    // println(s"Fresh $mxn")
                    
                    val newMembs =  {
                      if (parTargs.nonEmpty) err(msg"mixin type arguments not yet supported", p.toLoc)
                      
                      if (parArgs.sizeCompare(mxn.params) =/= 0)
                        err(msg"mixin $parNme expects ${
                          mxn.params.size.toString} parameter(s); got ${parArgs.size.toString}", Loc(v :: parArgs.unzip._2))
                      
                      val paramMems = mxn.params.lazyZip(parArgs).map { case (nme -> p, _ -> Fld(_, _, a)) => // TODO check name, mut, spec
                        implicit val genLambdas: GenLambdas = true
                        val a_ty = typeTerm(a)
                        p.lb.foreach(constrain(_, a_ty))
                        constrain(a_ty, p.ub)
                        NuParam(nme, FieldType(p.lb, a_ty)(provTODO))(lvl)
                      }
                      
                      val bodyMems = mxn.ttu.entities // TODO Q: why not `mxn.members`?
                      
                      paramMems ++ bodyMems
                      
                    }
                    println(s"Members $newMembs")
                    
                    S((mxn, newMembs, 
                      Map.empty[Str, NuMember], // TODO add ptp here once we support explicit type args
                      p.toLoc
                    ))
                    
                  case rawTrt: TypedNuTrt =>
                    if (parArgs.nonEmpty) err(msg"trait parameters not yet supported", p.toLoc)

                    val (fr, ptp) = refreshHelper(rawTrt, v, S(parTargs))
                    implicit val frenshened: MutMap[TV,ST] = fr
                    implicit val shadows: Shadows = Shadows.empty
                    val trt = rawTrt.freshenAbove(info.level, rigidify = false)
                    
                    val paramMems = Nil // * Maybe support trait params? (not sure)
                    S((trt, paramMems, ptp ++ trt.parentTP, p.toLoc))
                    
                  case rawCls: TypedNuCls =>
                    val (fr, ptp) = refreshHelper(rawCls, v, S(parTargs))
                    implicit val frenshened: MutMap[TV,ST] = fr
                    implicit val shadows: Shadows = Shadows.empty
                    val cls = rawCls.freshenAbove(info.level, rigidify = false)

                    if (parArgs.sizeCompare(cls.params) =/= 0)
                      err(msg"class $parNme expects ${
                        cls.params.size.toString} parameter(s); got ${parArgs.size.toString}", Loc(v :: parArgs.unzip._2))
                    
                    val paramMems = cls.params.lazyZip(parArgs).map { case (nme -> p, _ -> Fld(_, _, a)) => // TODO check name, mut, spec
                      implicit val genLambdas: GenLambdas = true
                      val a_ty = typeTerm(a)
                      p.lb.foreach(constrain(_, a_ty))
                      constrain(a_ty, p.ub)
                      NuParam(nme, FieldType(p.lb, a_ty)(provTODO))(lvl)
                    }
                    
                    S((cls, paramMems, ptp ++ cls.parentTP, p.toLoc))
                    
                  case als: TypedNuAls =>
                    // TODO dealias first?
                    err(msg"Cannot inherit from a type alias", p.toLoc)
                    N
                  case als: NuParam =>
                    // TODO first-class mixins/classes...
                    err(msg"Cannot inherit from a parameter", p.toLoc)
                    N
                  // case als: NuTypeParam =>
                  //   err(msg"Cannot inherit from a type parameter", p.toLoc)
                  //   Nil
                  case cls: TypedNuFun =>
                    err(msg"Cannot inherit from a function", p.toLoc)
                    N
                    
                  case cls: TypedNuDummy =>
                    N
                    
                }
              case S(_) =>
                err(msg"Cannot inherit from this", p.toLoc)
                N
              case N => 
                err(msg"Could not find definition `${parNme}`", p.toLoc)
                N
            }
          }()
      }
      
    }
    
    
    def lookupTags(parents: Ls[ParentSpec], tags: Set[TypeName]): Set[TypeName] = {
      parents match {
        case Nil => tags
        case (p, Var(nm), _, _) :: ps =>
          ctx.get(nm) match {
          case S(lti: DelayedTypeInfo) => lti.kind match {
            case Trt | Cls | Nms =>  lookupTags(ps, Set.single(TypeName(nm)) union lti.inheritedTags union tags)
            case _ => lookupTags(ps, tags)
          }
          case S(lti: CompletedTypeInfo) => lti.kind match {
            case Trt => lookupTags(ps, 
              Set.single(TypeName(nm)) union 
              lti.member.asInstanceOf[TypedNuTrt].inheritedTags union 
              tags)
            case Cls | Nms => lookupTags(ps, 
              Set.single(TypeName(nm)) union 
              lti.member.asInstanceOf[TypedNuCls].inheritedTags union 
              tags)
            case _ => lookupTags(ps, tags)
            }
          case _ => lookupTags(ps, tags)
        }
      }
    }

    lazy val inheritedTags = lookupTags(parentSpecs, Set.empty)
    
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
        (td.params.fields.iterator.flatMap(_._1) ++ td.body.entities.iterator.collect {
          case fd: NuFunDef => fd.nme
        }).toSet ++ typedParents.flatMap(_._1.allFields)
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

    // refresh trait/class/mixin
    def refreshHelper(raw: PolyNuDecl, v: Var, parTargs: Opt[Ls[Type]]): (MutMap[TV, ST], Map[Str, NuParam]) = {
      val freshened: MutMap[TV, ST] = MutMap.empty
      val rawName = v.name

      parTargs foreach { pta => 
        if (raw.tparams.sizeCompare(pta.size) =/= 0)
          err(msg"${raw.kind.str} $rawName expects ${
            raw.tparams.size.toString} type parameter(s); got ${pta.size.toString}", Loc(v :: pta))
      }

      val parTP = raw.tparams.lazyZip(parTargs.getOrElse(Nil)).map { case ((tn, _tv, vi), targTy) =>
        val targ = typeType(targTy)
        val tv = (targ match {
          case tv: TV => 
            // TODO
            println(s"Passing ${tn.name} :: ${_tv} <=< ${tv}")
            tv
          case _ =>
            println(s"Assigning ${tn.name} :: ${_tv} := $targ where ${targ.showBounds}")
            val tv =
              freshVar(_tv.prov, N, _tv.nameHint)(targ.level) // TODO safe not to set original?!
              // freshVar(_tv.prov, S(_tv), _tv.nameHint)(targ.level)
            println(s"Set ${tv} ~> ${_tv}")
            assert(tv.assignedTo.isEmpty)
            tv.assignedTo = S(targ)
            // println(s"Assigned ${tv.assignedTo}")
            tv
        })
        freshened += _tv -> tv
        rawName+"#"+tn.name -> NuParam(tn, FieldType(S(tv), tv)(provTODO))(level)
      }
      
      freshened -> parTP.toMap
    }
    
    
    def complete()(implicit raise: Raise): TypedNuDecl = result.getOrElse {
      if (isComputing) {
        err(msg"Unhandled cyclic definition", decl.toLoc)
        TypedNuDummy(decl)
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
                  err(msg"Type parameters are not yet supported in this position",
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
                      val outer_ctx = ctx
                      val body_ty = ctx.nextLevel { implicit ctx: Ctx =>
                        // * Note: can't use `ctx.poly` instead of `ctx.nextLevel` because all the methods
                        // * in the current typing unit are quantified together.
                        vars ++ fd.tparams.map { tn =>
                          tn.name -> freshVar(TypeProvenance(tn.toLoc, "method type parameter",
                            originName = S(tn.name),
                            isType = true), N, S(tn.name))
                        } |> { implicit vars =>
                          // * Only type methods polymorphically if they're at the top level or if
                          // * they're annotated with a type signature.
                          // * Otherwise, we get too much extrusion and cycle check failures
                          // * especially in the context of open recursion and mixins.
                          if (ctx.lvl === 1 || fd.signature.nonEmpty)
                            typeTerm(body)
                          else outer_ctx |> {
                            println(s"Not typing polymorphicall (cf. not top level or not annotated)")
                            println(typedSignatureMembers)
                            implicit ctx: Ctx => typeTerm(body) }
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
                  ctx.nest.nextLevel { implicit ctx =>
                    ctx ++= paramSymbols
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    
                    val sig_ty = typeType(td.sig.getOrElse(Top))
                    
                    def inherit(parents: Ls[TypedParentSpec], tags: ST, members: Ls[NuMember], vms: Map[Str, NuMember])
                          : (ST, Ls[NuMember], Map[Str, NuMember]) =
                        parents match {
                      case (trt: TypedNuTrt, newMembs, tpms, loc) :: ps =>
                        inherit(ps,
                          tags & trt.selfTy,
                          memberUnion(members, trt.members.values.toList),
                          vms ++ tpms   // with type members of parent class
                        )
                      case (_, _, _, loc) :: ps => 
                        err(msg"trait can only inherit from traits", loc)
                        inherit(ps, tags, members, vms)
                      case Nil => (tags, members, vms)
                    }
                    val (tags, baseMems, vms) =
                      inherit(typedParents, trtNameToNomTag(td)(noProv, ctx), Nil, Map.empty)
                    
                    // val selfType = tags & sig_ty
                    val selfType = sig_ty
                    
                    val ttu = typeTypingUnit(td.body, topLevel = false)
                    val mems = 
                      baseMems.map(d => d.name -> d).toMap ++ 
                      typedSignatureMembers.toMap ++ 
                      ttu.entities.map(d => d.name -> d).toMap

                    // check trait overriding
                    implCheck(baseMems, typedSignatureMembers.map(_._2) ++ ttu.entities, true)(td)

                    TypedNuTrt(outerCtx.lvl, td, ttu, 
                      tparams, 
                      mems, 
                      TopType,  // thisType (same as Cls)
                      None, 
                      selfType, 
                      inheritedTags,
                      vms
                    ) -> Nil
                  }
                  
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
                      NuParam(TypeName(fldNme).withLocOf(tp), FieldType(S(tv), tv)(tv.prov))(lvl)
                    }
                    val tparamFields = tparamMems.map(p => p.nme.toVar -> p.ty)
                    assert(!typedParams.keys.exists(tparamFields.keys.toSet), ???)

                    case class Pack(
                      superType: ST,
                      clsMem: Ls[NuMember], 
                      bsCls: Opt[Str], 
                      bsMem: Ls[NuMember], 
                      trtMem: Ls[NuMember],
                      pTP: Map[Str, NuMember]
                    )
                    
                    def inherit(parents: Ls[TypedParentSpec], pack: Pack): Pack = parents match {
                      case (p, newMembs, tpms, loc) :: ps => p match {
                        
                        
                        case mxn: TypedNuMxn =>
                          
                          assert(finalType.level === lvl)
                          assert(mxn.superTV.level === lvl)
                          assert(mxn.thisTV.level === lvl)
                          
                          constrain(pack.superType, mxn.superTV)
                          constrain(finalType, mxn.thisTV)
                          
                          assert(tpms.isEmpty) // FIXME
                          
                          val newSuperType = WithType(
                              pack.superType,
                              RecordType(
                                newMembs.collect{
                                  case m: NuParam => m.nme.toVar -> m.ty
                                  case m: TypedNuFun => m.fd.nme -> m.typeSignature.toUpper(provTODO)
                                }
                              )(provTODO)
                            )(provTODO)
                          
                          inherit(ps, pack.copy(
                            superType = newSuperType, 
                            clsMem = pack.clsMem ++ newMembs // FIXME add `mxn.members.values.toList`?
                          ))
                        
                        case trt: TypedNuTrt =>
                          
                          inherit(ps, pack.copy(
                            trtMem = memberUnion(pack.trtMem, trt.members.values.toList),
                            pTP = pack.pTP ++ tpms
                          ))

                        case cls: TypedNuCls =>
                          val parNme = cls.nme.name
                          
                          pack.bsCls.foreach { cls =>
                            err(msg"cannot inherit from more than one base class: ${
                              cls} and ${parNme}", loc)
                          }
                          
                          inherit(ps, pack.copy(
                            bsCls = S(parNme), 
                            bsMem = newMembs ++ cls.members.values.toList, 
                            pTP = pack.pTP ++ tpms
                          ))
                          
                        case als: TypedNuAls => // Should be rejected in `typedParents`
                          inherit(ps, pack)
                        
                      }
                      case Nil =>
                        val thisType = WithType(pack.superType, RecordType(typedParams)(ttp(td.params, isType = true)))(provTODO) &
                          clsNameToNomTag(td)(provTODO, ctx) &
                          RecordType(tparamFields)(TypeProvenance(Loc(td.tparams.map(_._2)), "type parameters", isType = true))
                        
                        trace(s"${lvl}. Finalizing inheritance with $thisType <: $finalType") {
                          assert(finalType.level === lvl)
                          constrain(thisType, finalType)
                          pack.clsMem
                        }()
                        
                        // println(s"${lvl}. Finalized inheritance with $superType ~> $thisType")
                        pack.copy(superType = thisType)
                    }
                    
                    // * We start from an empty super type.
                    val baseType =
                      RecordType(Nil)(TypeProvenance(Loc(td.parents).map(_.left), "Object"))
                    
                    val paramMems = typedParams.map(f => NuParam(f._1, f._2)(lvl))
                    
                    val Pack(thisType, baseMems, _, bsMembers, ifaceMembers, ptps) =
                      inherit(typedParents, Pack(baseType, tparamMems ++ paramMems, N, Nil, Nil, Map.empty))
                    
                    ctx += "super" -> VarSymbol(thisType, Var("super"))
                    val ttu = typeTypingUnit(td.body, topLevel = false)
                    
                    // local members overrides mixin members
                    val cmems = ttu.entities ++ baseMems.flatMap { m =>
                      ttu.entities.find(x => x.name == m.name) match {
                        case S(mem: TypedNuTermDef) => Nil
                        case S(pm: NuParam) => Nil
                        case _ => m :: Nil
                      }
                    }
                    // local members overrides parent members
                    val impltdMems = cmems ++ bsMembers.flatMap { m =>
                      cmems.find(x => x.name == m.name) match {
                        case S(mem: TypedNuTermDef) => Nil
                        case S(pm: NuParam) => Nil
                        case _ => m :: Nil
                      }
                    }
                    val mems = impltdMems.map(d => d.name -> d).toMap ++ typedSignatureMembers

                    // overriding check for class/interface inheritance
                    implCheck(bsMembers ++ ifaceMembers, impltdMems, false)(td)
                    
                    TypedNuCls(outerCtx.lvl, td, ttu,
                      tparams, typedParams, mems,
                      // if (td.kind is Nms) TopType else thisTV
                      TopType,
                      TopType, // TODO selfTy: use signature
                      inheritedTags,
                      ptps
                    )(thisType) -> impltdMems
                  }
                case Mxn =>
                  if (td.parents.nonEmpty)
                    err(msg"mixin definitions cannot yet extend parents" -> Loc(td.parents) :: Nil)
                  ctx.nest.nextLevel { implicit ctx =>
                    ctx ++= paramSymbols
                    val paramMems = typedParams.map(f => NuParam(f._1, f._2)(lvl))
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
                      if (!td.isDecl && td.kind != Trt)
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
          typeSignatureOf(td, level, tparams, typedParams, TopType, inheritedTags)
      }
    
    override def toString: String =
      s"${decl.name} ~> ${if (isComputing) "<computing>" else result.fold("<uncomputed>")(_.toString)}"
    
  }

  private def implCheck(abst: Ls[NuMember], impl: Ls[NuMember], isTrt: Bool)(td: NuTypeDef)
        (implicit raise: Raise, ctx: Ctx): Unit = {
    abst.foreach { m =>
      lazy val parSign = m match {
        case nt: TypedNuTermDef => nt.typeSignature
        case np: NuParam => np.typeSignature
        case _ => ??? // probably no other cases
      }
      impl.find(x => x.name === m.name) match {
        case S(mem: TypedNuTermDef) =>
          val memSign = mem.typeSignature
          implicit val prov: TP = memSign.prov
          println(s"checking overriding `${m.name}`")
          constrain(memSign, parSign)
        case S(pm: NuParam) =>
          val pmSign = pm.typeSignature
          implicit val prov: TP = pmSign.prov
          constrain(pmSign, parSign)
        case S(_) => ()
        case N => 
          if (!isTrt)
            err(msg"Member ${m.name} is declared in parent trait but not implemented", td.toLoc)
      }
    }
  }
  
  // intersection of members
  def memberUnion(l: Ls[NuMember], r: Ls[NuMember])(implicit raise: Raise): Ls[NuMember] = {
    def merge(ltm: NuMember, rtm: Option[NuMember]) = { 
      (ltm, rtm) match {
        case (a: TypedNuFun, S(b: TypedNuFun)) =>
          if (a.level =/= b.level)
            err(msg"member ${a.name} has mismatch levels ${a.level.toString} and ${b.level.toString}", a.fd.toLoc)
          if (a.fd.tparams =/= b.fd.tparams)
            err(msg"method ${a.name} has mismatch type parameters", a.fd.toLoc)
          val fd = NuFunDef((a.fd.isLetRec, b.fd.isLetRec) match {
            case (S(a), S(b)) => S(a || b)
            case _ => N // if one is fun, then it will be fun
          }, a.fd.nme, a.fd.tparams, a.fd.rhs)(a.fd.declareLoc, N)
          println(s"united ${a.name}")
          S(TypedNuFun(a.level, fd, a.bodyType & b.bodyType))
        case (a: NuParam, S(b: NuParam)) => 
          if (a.level =/= b.level)
            err(msg"member ${a.name} has mismatch levels ${a.level.toString} and ${b.level.toString}", N)
          S(NuParam(a.nme, a.ty && b.ty)(a.level))
        case (a: NuParam, S(b: TypedNuFun)) => // not sure
          if (a.level =/= b.level)
            err(msg"member ${a.name} has mismatch levels ${a.level.toString} and ${b.level.toString}", N)
          S(NuParam(a.nme, a.ty && FieldType(S(b.bodyType), b.bodyType)(b.bodyType.prov))(a.level))
        case (a: TypedNuFun, S(b: NuParam)) => // not sure
          if (a.level =/= b.level)
            err(msg"member ${a.name} has mismatch levels ${a.level.toString} and ${b.level.toString}", N)
          S(NuParam(b.nme, FieldType(S(a.bodyType), a.bodyType)(a.bodyType.prov) && b.ty)(b.level))
        case (a, N) => S(a)
        case (a, S(b)) =>
          err(msg"intersection of member ${a.name} is currently not supported", N)
          N
      }
    }
    l.foldLeft(r.map(d => d.name -> d).toMap) { case (acc, ltm) => 
      acc.updatedWith(ltm.name)(merge(ltm, _))
    }.values.toList
  }
  
}

