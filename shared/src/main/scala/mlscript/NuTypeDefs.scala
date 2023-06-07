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
    def toLoc: Opt[Loc]
    def level: Level
    def isImplemented: Bool
    
    def isValueParam: Bool = this match {
      case p: NuParam => !p.isType
      case _ => false
    }
    
    protected def withLevel[R](k: Ctx => R)(implicit ctx: Ctx): R = k(ctx.copy(lvl = ctx.lvl + 1))
    
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
    
    def showBounds: Str = TypedTypingUnit(this :: Nil, N).showBounds
  }
  
  
  case class NuParam(nme: NameRef, ty: FieldType)(val level: Level) extends NuMember with TypedNuTermDef {
    def name: Str = nme.name
    def isType: Bool = nme.isInstanceOf[TypeName]
    def kind: DeclKind =
      if (isType) Als // FIXME?
      else Val
    def toLoc: Opt[Loc] = nme.toLoc
    def isImplemented: Bool = true
    def typeSignature: ST = ty.ub
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : NuParam =
      NuParam(nme, ty.freshenAbove(lim, rigidify))(ctx.lvl)
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuParam =
        NuParam(nme, ty.update(t => f(pol.map(!_), t), t => f(pol, t)))(level)
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuParam =
        NuParam(nme, ty.update(t => f(pol.contravar, t), t => f(pol, t)))(level)
  }
  
  
  sealed trait TypedNuDecl extends NuMember {
    def name: Str
    def level: Level
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuDecl
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuDecl
  }
  
  
  // TODO rm?
  /** Those declarations that introduce term names in scope. */
  sealed trait TypedNuTermDef extends TypedNuDecl with AnyTypeDef {
    def typeSignature: ST
  }
  
  
  sealed abstract class TypedNuTypeDef(kind: TypeDefKind) extends TypedNuDecl {
    def nme: TypeName
    def decl: NuTypeDef
    def toLoc: Opt[Loc] = decl.toLoc
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
    def isImplemented: Bool = td.sig.isDefined
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST])
          : TypedNuAls = { val outer = ctx; withLevel { implicit ctx =>
      TypedNuAls(outer.lvl, td,
        tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
        body.freshenAbove(lim, rigidify))
    }}
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuDecl =
        TypedNuAls(
          level, td,
          tparams.map(tp => (tp._1, f(N, tp._2).assertTV, tp._3)),
          f(pol, body)
        )
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuDecl =
        TypedNuAls(
          level, td,
          tparams.map(tp => (tp._1, f(pol.invar, tp._2).assertTV, tp._3)),
          f(pol, body)
        )
  }
  
  sealed trait PolyNuDecl extends TypedNuDecl {
    def tparams: TyParams
  }
  
  
  case class TypedNuTrt(
        level: Level, td: NuTypeDef,
        tparams: TyParams,
        members: Map[Str, NuMember],
        thisTy: ST,
        sign: ST,
        inheritedTags: Set[TypeName],
        parentTP: Map[Str, NuMember]
      ) extends TypedNuTypeDef(Trt) with PolyNuDecl
  {
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def nme: TypeName = td.nme
    def name: Str = nme.name
    def isImplemented: Bool = true
    
    lazy val virtualMembers: Map[Str, NuMember] = members ++ tparams.map {
      case (nme @ TypeName(name), tv, _) => 
        td.nme.name+"#"+name -> NuParam(nme, FieldType(S(tv), tv)(provTODO))(level)
    } ++ parentTP
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST])
          : TypedNuTrt = { val outer = ctx; withLevel { implicit ctx =>
      TypedNuTrt(outer.lvl, td,
        tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
        members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
        thisTy.freshenAbove(lim, rigidify),
        sign.freshenAbove(lim, rigidify),
        inheritedTags,
        parentTP.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap
      )
    }}
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTrt =
        TypedNuTrt(level, td,
          tparams.map(tp => (tp._1, f(N, tp._2).assertTV, tp._3)),
          members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap,
          f(pol.map(!_), thisTy),
          f(pol, sign),
          inheritedTags,
          parentTP.mapValuesIter(_.mapPol(pol, smart)(f)).toMap
        )
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTrt =
        TypedNuTrt(level, td,
          tparams.map(tp => (tp._1, f(pol.invar, tp._2).assertTV, tp._3)),
          members.mapValuesIter(_.mapPolMap(pol)(f)).toMap,
          f(pol.contravar, thisTy),
          f(pol, sign),
          inheritedTags,
          parentTP.mapValuesIter(_.mapPolMap(pol)(f)).toMap
        )
  }
  
  
  case class TypedNuCls(
        level: Level, td: NuTypeDef,
        tparams: TyParams,
        params: Ls[Var -> FieldType],
        members: Map[Str, NuMember],
        thisTy: ST,
        sign: ST,
        inheritedTags: Set[TypeName],
        parentTP: Map[Str, NuMember]
      )(val instanceType: ST, // * only meant to be used in `force` and `variances`
      ) extends TypedNuTypeDef(Cls) with PolyNuDecl
  {
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def nme: TypeName = td.nme
    def name: Str = nme.name
    def isImplemented: Bool = true
    
    def typeSignature: ST = typeSignatureOf(td, level, tparams, params, sign, inheritedTags)
    
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
          : TypedNuCls = { val outer = ctx; withLevel { implicit ctx =>
      TypedNuCls(outer.lvl, td,
        tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
        params.mapValues(_.freshenAbove(lim, rigidify)),
        members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
        thisTy.freshenAbove(lim, rigidify),
        sign.freshenAbove(lim, rigidify),
        inheritedTags,
        parentTP.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
      )(this.instanceType.freshenAbove(lim, rigidify))
    }}
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuCls =
        TypedNuCls(level, td,
          tparams.map(tp => (tp._1, f(N, tp._2).assertTV, tp._3)),
          params.mapValues(_.update(t => f(pol.map(!_), t), t => f(pol, t))),
          members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap,
          f(pol.map(!_), thisTy),
          f(pol, sign),
          inheritedTags,
          parentTP.mapValuesIter(_.mapPol(pol, smart)(f)).toMap,
        )(f(pol, instanceType))
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuCls =
        TypedNuCls(level, td,
          tparams.map(tp => (tp._1, f(pol.invar, tp._2).assertTV, tp._3)),
          params.mapValues(_.update(t => f(pol.contravar, t), t => f(pol, t))),
          members.mapValuesIter(_.mapPolMap(pol)(f)).toMap,
          f(pol.contravar, thisTy),
          f(pol, sign),
          inheritedTags,
          parentTP.mapValuesIter(_.mapPolMap(pol)(f)).toMap,
        )(f(pol, instanceType))
    
    override def toString: Str = s"TypedNuCls($level, ${td.nme},\n\t$tparams,\n\t$params,\n\tthis: $thisTy, ${
      members.lnIndent()},\n\t: $sign, $inheritedTags, $parentTP)"
  }
  
  
  case class TypedNuMxn(
        level: Level, td: NuTypeDef,
        thisTy: ST, superTy: ST,
        tparams: TyParams, params: Ls[Var -> FieldType],
        members: Map[Str, NuMember],
      ) extends TypedNuTypeDef(Mxn) with PolyNuDecl
  {
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def nme: TypeName = td.nme
    def name: Str = nme.name
    def isImplemented: Bool = true

    lazy val virtualMembers: Map[Str, NuMember] = members ++ tparams.map {
      case (nme @ TypeName(name), tv, _) => 
        td.nme.name+"#"+name -> NuParam(nme, FieldType(S(tv), tv)(provTODO))(level)
    } 
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV,ST])
          : TypedNuMxn = { val outer = ctx; withLevel { implicit ctx =>
      TypedNuMxn(outer.lvl, td,
        thisTy.freshenAbove(lim, rigidify),
        superTy.freshenAbove(lim, rigidify),
        tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
        params.mapValues(_.freshenAbove(lim, rigidify)),
        members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
      )
    }}
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuMxn =
      TypedNuMxn(level, td, f(pol.map(!_), thisTy), f(pol.map(!_), superTy),
        tparams.map(tp => (tp._1, f(N, tp._2).assertTV, tp._3)),
        params.mapValues(_.update(t => f(pol.map(!_), t), t => f(pol, t))),
        members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap)
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuMxn =
      TypedNuMxn(level, td, f(pol.contravar, thisTy), f(pol.contravar, superTy),
        tparams.map(tp => (tp._1, f(pol.invar, tp._2).assertTV, tp._3)),
        params.mapValues(_.update(t => f(pol.contravar, t), t => f(pol, t))),
        members.mapValuesIter(_.mapPolMap(pol)(f)).toMap)
    
    override def toString: Str = s"TypedNuMxn($level, ${td.nme},\n\tthis: $thisTy,\n\tsuper: $superTy,\n\ttparams: $tparams,\n\tparams: $params,\n\tmembers: ${members.lnIndent()}\n)"
  }
  
  
  /** Used when there was an error while tying a definition. */
  case class TypedNuDummy(d: NuDecl) extends TypedNuDecl with TypedNuTermDef {
    def level = MinLevel
    def kind: DeclKind = Val
    def toLoc: Opt[Loc] = N
    def name: Str = d.name
    def isImplemented: Bool = true
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
  case class TypedNuFun(level: Level, fd: NuFunDef, bodyType: ST)(val isImplemented: Bool)
      extends TypedNuDecl with TypedNuTermDef {
    def kind: DeclKind = Val
    def name: Str = fd.nme.name
    def toLoc: Opt[Loc] = fd.toLoc
    lazy val typeSignature: ST = PolymorphicType.mk(level, bodyType)
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : TypedNuFun = { val outer = ctx; withLevel { implicit ctx => this match {
      case TypedNuFun(level, fd, ty) =>
        TypedNuFun(outer.lvl, fd, ty.freshenAbove(lim, rigidify))(isImplemented)
          // .tap(res => println(s"Freshen[$level,${ctx.lvl}] $this ~> $res"))
    }}}
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuFun =
      TypedNuFun(level, fd, f(pol, bodyType))(isImplemented)
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuFun =
      TypedNuFun(level, fd, f(pol, bodyType))(isImplemented)
  }
  
  
  case class TypedTypingUnit(implementedMembers: Ls[NuMember], result: Opt[ST]) extends OtherTypeLike {
    def map(f: ST => ST)(implicit ctx: Ctx): TypedTypingUnit =
      TypedTypingUnit(implementedMembers.map(_.map(f)), result.map(f))
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedTypingUnit =
      TypedTypingUnit(implementedMembers.map(_.mapPol(pol, smart)(f)), result.map(f(pol, _)))
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedTypingUnit =
      TypedTypingUnit(implementedMembers.map(_.mapPolMap(pol)(f)), result.map(f(pol, _)))
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : TypedTypingUnit =
      TypedTypingUnit(implementedMembers.map(_.freshenAbove(lim, rigidify)), result.map(_.freshenAbove(lim, rigidify)))
    override def toString: Str = s"TypedTypingUnit(${(implementedMembers :+ result).lnIndent()})"
  }
  
  
  def typeSignatureOf(td: NuTypeDef, level: Level, tparams: TyParams, params: Params, selfTy: ST, ihtags: Set[TypeName])
      : ST = td.kind match {
    case Mod =>
      ClassTag(Var(td.nme.name),
          ihtags + TN("Object")
        )(provTODO)
    case Cls =>
      PolymorphicType.mk(level,
        FunctionType(
          TupleType(params.mapKeys(some))(provTODO),
          ClassTag(Var(td.nme.name),
            ihtags + TN("Object")
          )(provTODO) & RecordType.mk(
            // * ^ Note: we used to include the self type here (& selfTy),
            // *  but it doesn't seem to be needed – if the class has a constructor,
            // *  then surely it satisfies the self type (once we check it).
            tparams.map { case (tn, tv, vi) =>
              // TODO also use computed variance info when available!
              Var(td.nme.name + "#" + tn.name).withLocOf(tn) ->
                FieldType.mk(vi.getOrElse(VarianceInfo.in), tv, tv)(provTODO) }
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
            err(s"A type signature for '$nme' was already given", fd.toLoc)
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
                fd.copy()(fd.declareLoc, fd.exportLoc, S(sig))
              case _ =>
                fd
            }
          case td: NuTypeDef =>
            if (td.nme.name in reservedTypeNames)
              err(msg"Type name '${td.nme.name}' is reserved", td.toLoc)
            td
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
    def isComputed: Bool = result.isDefined
    
    val level: Level = ctx.lvl
    
    val kind: DeclKind = decl.kind
    
    private implicit val prov: TP =
      TypeProvenance(decl.toLoc, decl.describe)
    
    println(s"${ctx.lvl}. Created lazy type info for $decl")

    type ParentSpec = (Term, Var, LazyTypeInfo, Ls[Type], Ls[Opt[Var] -> Fld])
    lazy val parentSpecs: Ls[ParentSpec] = decl match {
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
        }.flatMap {
          case (p, v @ Var(parNme), parTargs, parArgs) =>
            ctx.get(parNme) match {
              case S(lti: LazyTypeInfo) =>
                S((p, v, lti, parTargs, parArgs))
              case S(_) =>
                err(msg"Cannot inherit from this", p.toLoc)
                N
              case N => 
                err(msg"Could not find definition `${parNme}`", p.toLoc)
                N
            }
        }
      case _ => Nil
    }
    
    /** First list of members is for the typed arguments;
     *  the map of members is for the inherited virtual type argument members. */
    type TypedParentSpec = (TypedNuTypeDef, Ls[NuParam], Map[Str, NuMember], Opt[Loc])
    
    lazy val typedParents: Ls[TypedParentSpec] = ctx.nest.nextLevel { implicit ctx =>
      
      ctx ++= paramSymbols
      
      parentSpecs.flatMap {
        case (p, v @ Var(parNme), lti, parTargs, parArgs) =>
          trace(s"${lvl}. Typing parent spec $p") {
            val info = lti.complete()
            info match {
              
              case rawMxn: TypedNuMxn =>
                
                // println(s"Raw $rawMxn")
                val (fr, ptp) = refreshHelper(rawMxn, v, if (parTargs.isEmpty) N else S(parTargs)) // type args inferred
                val mxn = {
                  implicit val frenshened: MutMap[TV,ST] = fr
                  implicit val shadows: Shadows = Shadows.empty
                  implicit val ctx: Ctx = outerCtx
                  rawMxn.freshenAbove(info.level, rigidify = false)
                }
                // println(s"Fresh $mxn")
                
                val argMembs =  {                      
                  if (parArgs.sizeCompare(mxn.params) =/= 0)
                    err(msg"mixin $parNme expects ${
                      mxn.params.size.toString} parameter(s); got ${parArgs.size.toString}", Loc(v :: parArgs.unzip._2))
                  
                  val paramMems = mxn.params.lazyZip(parArgs).map {
                    case (nme -> p, _ -> Fld(_, _, a)) => // TODO check name, mut, spec
                      implicit val genLambdas: GenLambdas = true
                      val a_ty = typeTerm(a)
                      p.lb.foreach(constrain(_, a_ty))
                      constrain(a_ty, p.ub)
                      NuParam(nme, FieldType(p.lb, a_ty)(provTODO))(lvl)
                  }
                  
                  paramMems //++ mxn.members.valuesIterator
                  
                }
                println(s"Members $argMembs")
                
                S((mxn, argMembs, 
                  Map.empty[Str, NuMember], // TODO add ptp here once we support explicit type args
                  p.toLoc
                ))
                
              case rawTrt: TypedNuTrt =>
                if (parArgs.nonEmpty) err(msg"trait arguments are not yet supported", p.toLoc)

                val (fr, ptp) = refreshHelper(rawTrt, v, if (parTargs.isEmpty) N else S(parTargs))  // infer ty args if not provided
                val trt = {
                  implicit val frenshened: MutMap[TV,ST] = fr
                  implicit val shadows: Shadows = Shadows.empty
                  implicit val ctx: Ctx = outerCtx
                  rawTrt.freshenAbove(info.level, rigidify = false)
                }
                
                val paramMems = Nil // * Maybe support trait params? (not sure)
                
                S((trt, paramMems, ptp ++ trt.parentTP, p.toLoc))
                
              case rawCls: TypedNuCls =>
                
                // println(s"Raw $rawCls")
                
                val (fr, ptp) = refreshHelper(rawCls, v, if (parTargs.isEmpty) N else S(parTargs)) // infer ty args if not provided
                val cls = {
                  implicit val frenshened: MutMap[TV,ST] = fr
                  implicit val shadows: Shadows = Shadows.empty
                  implicit val ctx: Ctx = outerCtx
                  rawCls.freshenAbove(info.level, rigidify = false)
                }
                
                // println(s"Fresh[${ctx.lvl}] $cls")
                
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
          }()
      }
      
    }
    
    
    def lookupTags(parents: Ls[ParentSpec], tags: Set[TypeName]): Set[TypeName] = {
      parents match {
        case Nil => tags
        case (p, Var(nm), lti, _, _) :: ps => lti match {
          case lti: DelayedTypeInfo => lti.kind match {
            case Trt | Cls | Mod =>  lookupTags(ps, Set.single(TypeName(nm)) union lti.inheritedTags union tags)
            case Val | Mxn | Als => lookupTags(ps, tags)
          }
          case CompletedTypeInfo(trt: TypedNuTrt) =>
            lookupTags(ps, Set.single(TypeName(nm)) union trt.inheritedTags union tags)
          case CompletedTypeInfo(cls: TypedNuCls) =>
            lookupTags(ps, Set.single(TypeName(nm)) union cls.inheritedTags union tags)
          case CompletedTypeInfo(_: NuParam | _: TypedNuFun | _: TypedNuAls | _: TypedNuMxn | _: TypedNuDummy) =>
            lookupTags(ps, tags)
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
          td.params.getOrElse(Tup(Nil)).fields.map {
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
              nme -> FieldType(N, err(msg"${td.kind.str.capitalize} parameters currently need type annotations",
                nme.toLoc))(provTODO)
            case _ => ???
          }
        case fd: NuFunDef => Nil
      }
    }
    
    lazy val paramSymbols = typedParams.map(p => p._1.name -> VarSymbol(p._2.ub, p._1))
    
    // TODO also import signatures from base classes and mixins!
    lazy val (typedSignatures, funImplems) : (Ls[(NuFunDef, ST)], Ls[NuFunDef]) = decl match {
      case td: NuTypeDef => ctx.nest.nextLevel { implicit ctx =>
        val (signatures, rest) = td.body.entities.partitionMap {
          case fd @ NuFunDef(N | S(false), nme, tparams, R(rhs)) => // currently `val`s are encoded with `S(false)`
            L((fd, rhs))
          // TODO also pick up signature off implems with typed params/results
          case s => R(s)
        }
        val implems = rest.collect { case fd @ NuFunDef(N | S(false), nme, tparams, L(rhs)) => fd }
        
        ctx ++= paramSymbols
        
        signatures.map { case (fd, rhs) =>
          (fd, ctx.poly { implicit ctx: Ctx =>
            vars ++ fd.tparams.map { tn =>
              tn.name -> freshVar(TypeProvenance(tn.toLoc, "method type parameter",
                originName = S(tn.name),
                isType = true), N, S(tn.name))
            } |> { implicit vars =>
              
              typeType(rhs).withProv(
                TypeProvenance(Loc(rhs :: fd.nme :: fd.tparams), s"signature of member `${fd.nme.name}`")
              )
              
            }
          })
        } -> implems
      }
      case _: NuFunDef => Nil -> Nil
    }
    lazy val typedSignatureMembers: Ls[Str -> TypedNuFun] = {
      val implemented = funImplems.iterator.map(_.nme.name).toSet
      typedSignatures.iterator.map { case (fd, ty) =>
        fd.nme.name -> TypedNuFun(level + 1, fd, ty)(implemented.contains(fd.nme.name))
      }.toList
    }
    
    lazy val inheritedFields: Set[Var] = decl match {
      case td: NuTypeDef =>
        parentSpecs.iterator.flatMap(_._3 match {
          case dti: DelayedTypeInfo => dti.allFields
          case CompletedTypeInfo(m: TypedNuTypeDef) => m.allFields
          case _ => Set.empty}).toSet
      case _: NuFunDef => Set.empty
    }
    
    lazy val allFields: Set[Var] = decl match {
      case td: NuTypeDef =>
        (td.params.getOrElse(Tup(Nil)).fields.iterator.flatMap(_._1) ++ td.body.entities.iterator.collect {
          case fd: NuFunDef => fd.nme
        }).toSet ++ inheritedFields
      case _: NuFunDef => Set.empty
    }
    
    lazy val typedFields: Map[Var, FieldType] =
      (typedParams.toMap -- inheritedFields /* parameters can be overridden by inherited fields/methods */) ++
        typedSignatures.iterator.map(fd_ty => fd_ty._1.nme -> fd_ty._2.toUpper(noProv))
    
    lazy val mutRecTV: TV = freshVar(
      TypeProvenance(decl.toLoc, decl.describe, S(decl.name), decl.isInstanceOf[NuTypeDef]),
      N,
      S(decl.name))(level + 1)
    
    private lazy val thisTV: TV =
      freshVar(provTODO, N, S(decl.name.decapitalize))(lvl + 1)
    
    def refreshHelper(raw: PolyNuDecl, v: Var, parTargs: Opt[Ls[Type]])
          (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType])
          : (MutMap[TV, ST], Map[Str, NuParam]) = {
      val rawName = v.name
      parTargs foreach { pta => 
        if (raw.tparams.sizeCompare(pta.size) =/= 0)
          err(msg"${raw.kind.str} $rawName expects ${
            raw.tparams.size.toString} type parameter(s); got ${pta.size.toString}", Loc(v :: pta))
      }
      refreshHelper2(raw: PolyNuDecl, v: Var, parTargs.map(_.map(typeType(_))))
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
                      vars = vars ++ tps.map {
                          case L(tn) => tn.name -> freshVar(provTODO, N)(1)
                          case _ => die
                        }.toMap)
                  }
                  TypedNuFun(ctx.lvl, fd, PolymorphicType(ctx.lvl, body_ty))(isImplemented = false)
                case R(_) => die
                case L(body) =>
                  fd.isLetRec match {
                    case S(true) => // * Let rec bindings
                      checkNoTyParams()
                      implicit val gl: GenLambdas = true
                      TypedNuFun(ctx.lvl, fd, typeTerm(
                        Let(true, fd.nme, body, fd.nme)
                      ))(isImplemented = true)
                    case S(false) => // * Let bindings
                      checkNoTyParams()
                      implicit val gl: GenLambdas = true
                      TypedNuFun(ctx.lvl, fd, typeTerm(body))(isImplemented = true)
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
                          else outer_ctx |> { implicit ctx: Ctx =>
                            println(s"Not typing polymorphicall (cf. not top level or not annotated)")
                            typeTerm(body) }
                        }
                      }.withProv(TypeProvenance(fd.toLoc, s"definition of method ${fd.nme.name}"))
                      TypedNuFun(ctx.lvl, fd, body_ty)(isImplemented = true)
                  }
              }
              ctx.nextLevel { implicit ctx: Ctx => constrain(res_ty.bodyType, mutRecTV) }
              res_ty
              
              
            case td: NuTypeDef =>
              
              
              /** Checks everything is implemented and there are no implementation duplicates. */
              def implemCheck(implementedMembers: Ls[NuMember], toImplement: Ls[NuMember]): Unit = {
                
                val implemsMap = MutMap.empty[Str, NuMember]
                implementedMembers.foreach { m =>
                  implemsMap.updateWith(m.name) {
                    case S(_) =>
                      err(msg"Duplicated `${m.name}` member definition in `${td.name}`", m.toLoc)
                      N
                    case N => S(m)
                  }
                }
                if (!td.isDecl && td.kind =/= Trt && !td.isAbstract) {
                  toImplement.foreach { m =>
                    implemsMap.get(m.name) match {
                      case S(_) =>
                      case N =>
                        err(msg"Member `${m.name}` is declared in parent but not implemented in `${
                            td.nme.name}`" -> td.nme.toLoc ::
                          msg"Declared here:" -> m.toLoc ::
                          Nil)
                    }
                  }
                }
                
              }
              
              /** Checks overriding members against their parent types. */
              def overrideCheck(newMembers: Ls[NuMember], signatures: Ls[NuMember]): Unit =
                  ctx.nextLevel { implicit ctx: Ctx => // * Q: why exactly do we need `ctx.nextLevel`?
                
                val sigMap = MutMap.empty[Str, NuMember]
                signatures.foreach { m =>
                  sigMap.updateWith(m.name) {
                    case S(_) => die
                    case N => S(m)
                  }
                }
                
                newMembers.foreach { m =>
                  println(s"Checking overriding for `${m.name}`...")
                  (m, sigMap.get(m.name)) match {
                    case (_, N) =>
                    case (m: TypedNuTermDef, S(fun: TypedNuTermDef)) =>
                      val mSign = m.typeSignature
                      implicit val prov: TP = mSign.prov
                      constrain(mSign, fun.typeSignature)
                    case (_, S(that)) =>
                      err(msg"${m.kind.str.capitalize} member `${m.name}` cannot override ${
                          that.kind.str} member of the same name declared in parent" -> td.toLoc ::
                        msg"Declared here:" -> that.toLoc ::
                        Nil)
                  }
                }
                
              }
              
              
              // intersection of members
              def membersInter(l: Ls[NuMember], r: Ls[NuMember]): Ls[NuMember] = {
                def merge(ltm: NuMember, rtm: Option[NuMember]) = {
                  rtm.foreach(rtm => assert(rtm.level === ltm.level, (ltm.level, rtm.level)))
                  (ltm, rtm) match {
                    case (a: TypedNuFun, S(b: TypedNuFun)) =>
                      assert(!(a.isImplemented && b.isImplemented))
                      val fd = NuFunDef((a.fd.isLetRec, b.fd.isLetRec) match {
                        case (S(a), S(b)) => S(a || b)
                        case _ => N // if one is fun, then it will be fun
                      }, a.fd.nme, a.fd.tparams, a.fd.rhs)(a.fd.declareLoc, a.fd.exportLoc, N)
                      S(TypedNuFun(a.level, fd, a.bodyType & b.bodyType)(a.isImplemented || b.isImplemented))
                    case (a: NuParam, S(b: NuParam)) => 
                      S(NuParam(a.nme, a.ty && b.ty)(a.level))
                    case (a: NuParam, S(b: TypedNuFun)) =>
                      S(TypedNuFun(a.level, b.fd, a.ty.ub & b.bodyType)(a.isImplemented || b.isImplemented))
                    case (a: TypedNuFun, S(b: NuParam)) =>
                      S(TypedNuFun(a.level, a.fd, b.ty.ub & a.bodyType)(a.isImplemented || b.isImplemented))
                    case (a, N) => S(a)
                    case (a, S(b)) =>
                      err(msg"Intersection of ${a.kind.str} member and ${b.kind.str} members currently unsupported" -> td.toLoc
                        :: msg"The ${a.kind.str} member is defined here:" -> a.toLoc
                        :: msg"The ${b.kind.str} member is defined here:" -> b.toLoc
                        :: Nil)
                      N
                  }
                }
                l.foldLeft(r.map(d => d.name -> d).toMap) { case (acc, ltm) => 
                  acc.updatedWith(ltm.name)(merge(ltm, _))
                }.values.toList
              }
              
              
              if (((td.kind is Mod) || (td.kind is Mxn)) && td.ctor.isDefined)
                err(msg"Explicit ${td.kind.str} constructors are not supported",
                  td.ctor.fold[Opt[Loc]](N)(c => c.toLoc))
              
              // * To type signatures correctly, we need to deal with type unbound variables 'X,
              // * which should be treated as unknowns (extruded skolems).
              // * Allowing such type variables is important for the typing of signatures such as
              // *  `: Foo | Bar` where `Foo` and `Bar` take type parameters,
              // *  as these will be (in the future) desugared to `: Foo['A0] | Bar['A1]`
              def typeTypeSignature(sign: Type)(implicit ctx: Ctx): ST = {
                val outer = ctx
                val ty = ctx.nest.nextLevel { implicit ctx =>
                  // * Type the signature in a higher level, so as to contain unbound type vars
                  val ty = typeType(td.sig.getOrElse(Top))
                  // * Make these type vars skolems
                  implicit val freshened: MutMap[TV, ST] = MutMap.empty
                  implicit val shadows: Shadows = Shadows.empty
                  ty.freshenAbove(outer.lvl, rigidify = true)
                }
                // * Create a lower-levl type variable to extrude the type through it,
                // * which will result in making the unbound type vars extruded skolems (i.e., unknowns)
                val res = freshVar(provTODO, N, N)(ctx.lvl)
                // * Subtle note: it is sufficient and important to add the type as a LB of the TV
                // *  instead of unifying them because:
                // *  1. currently we expand type defs the same no matter of the position polarity
                // *      so `class S: T` is always expanded as `#S & 'X` where `'X :> T`
                // *  2. we don't want to have to check every single subtype of S against T,
                // *      as this check will already have been performed generally when typing class T,
                // *      but this would happen if we instead expanded into a type equivalent to #S & T...
                constrain(ty, res)
                // * Retrieve the extruded lower bound.
                // * Note that there should be only one, and in particular it should not be recursive,
                // * since the variable is never shared outside this scope.
                res.lowerBounds match {
                  case lb :: Nil => TypeBounds.mk(TopType, lb)
                  case _ => die
                }
              }
              
              td.kind match {
                
                case Trt =>
                  td.params match {
                    case S(ps) => err(msg"trait parameters are not yet supported", ps.toLoc)
                    case _ =>
                  }
                  
                  ctx.nest.nextLevel { implicit ctx =>
                    ctx ++= paramSymbols
                    ctx ++= typedSignatures.map(nt => nt._1.name -> VarSymbol(nt._2, nt._1.nme))
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    
                    val sig_ty = td.sig.fold(TopType: ST)(typeTypeSignature)
                    
                    def inherit(parents: Ls[TypedParentSpec], tags: ST, members: Ls[NuMember], tparamMembs: Map[Str, NuMember])
                          : (ST, Ls[NuMember], Map[Str, NuMember]) =
                        parents match {
                      case (trt: TypedNuTrt, argMembs, tpms, loc) :: ps =>
                        assert(argMembs.isEmpty, argMembs)
                        inherit(ps,
                          tags & trt.sign,
                          membersInter(members, trt.members.values.toList),
                          tparamMembs ++ tpms   // with type members of parent class
                        )
                      case (_, _, _, loc) :: ps => 
                        err(msg"A trait can only inherit from other traits", loc)
                        inherit(ps, tags, members, tparamMembs)
                      case Nil => (tags, members, tparamMembs)
                    }
                    val (tags, trtMembers, tparamMembs) =
                      inherit(typedParents, trtNameToNomTag(td)(noProv, ctx), Nil, Map.empty)
                    
                    td.body.entities.foreach {
                      case fd @ NuFunDef(_, _, _, L(_)) =>
                        err(msg"Method implementations in traits are not yet supported", fd.toLoc)
                      case _ =>
                    }
                    
                    val ttu = typeTypingUnit(td.body, topLevel = false)
                    
                    val allMembers = (
                      trtMembers.iterator.map(d => d.name -> d)
                      ++ ttu.implementedMembers.map(d => d.name -> d)
                      ++ typedSignatureMembers
                    ).toMap
                    
                    // check trait overriding
                    overrideCheck(typedSignatureMembers.map(_._2), trtMembers)
                    
                    TypedNuTrt(outerCtx.lvl, td,
                      tparams,
                      allMembers,
                      TopType, // thisType (same as for Cls)
                      sig_ty,
                      inheritedTags,
                      tparamMembs
                    )
                  }
                  
                case Als =>
                  
                  if (td.params.getOrElse(Tup(Nil)).fields.nonEmpty)
                    err(msg"Type alias definitions cannot have value parameters" -> td.params.getOrElse(Tup(Nil)).toLoc :: Nil)
                  if (td.parents.nonEmpty)
                    err(msg"Type alias definitions cannot extend parents" -> Loc(td.parents) :: Nil)
                  
                  val body_ty = td.sig match {
                    case S(sig) =>
                      typeType(sig)
                    case N =>
                      err(msg"Type alias definition requires a right-hand side", td.toLoc)
                  }
                  
                  TypedNuAls(outerCtx.lvl, td, tparams, body_ty)
                  
                case Cls | Mod =>
                  
                  ctx.nest.nextLevel { implicit ctx =>
                    
                    if ((td.kind is Mod) && typedParams.nonEmpty)
                      // * Can we do better? (Memoization semantics?)
                      err(msg"${td.kind.str} parameters are not supported",
                        Loc(typedParams.iterator.map(_._1)))
                    
                    ctx ++= paramSymbols
                    ctx ++= typedSignatures.map(nt => nt._1.name -> VarSymbol(nt._2, nt._1.nme))
                    
                    val sig_ty = td.sig.fold(TopType: ST)(typeTypeSignature)
                    
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
                      mxnMembers: Ls[NuMember], 
                      baseClsNme: Opt[Str], 
                      baseClsMembers: Ls[NuMember], 
                      traitMembers: Ls[NuMember],
                      tparamMembers: Map[Str, NuMember]
                    )
                    
                    def inherit(parents: Ls[TypedParentSpec], pack: Pack): Pack = parents match {
                      case (p, argMembs, tpms, loc) :: ps => p match {
                        
                        
                        case mxn: TypedNuMxn =>
                          
                          assert(finalType.level === lvl)
                          assert(mxn.superTy.level === lvl)
                          assert(mxn.thisTy.level === lvl)
                          
                          constrain(pack.superType, mxn.superTy)
                          constrain(finalType, mxn.thisTy)
                          
                          assert(tpms.isEmpty) // Mixins do not introduce virtual members for type params
                          
                          val newMembs = argMembs ++ mxn.members.valuesIterator.filterNot(_.isValueParam)
                          val newSuperType = WithType(
                              pack.superType,
                              RecordType(
                                newMembs.collect {
                                  case m: NuParam => m.nme.toVar -> m.ty
                                  case m: TypedNuFun => m.fd.nme -> m.typeSignature.toUpper(provTODO)
                                }
                              )(provTODO)
                            )(provTODO)
                          
                          inherit(ps, pack.copy(
                            superType = newSuperType,
                            mxnMembers = newMembs ++ pack.mxnMembers
                          ))
                        
                        case trt: TypedNuTrt =>
                          
                          assert(argMembs.isEmpty, argMembs)
                          
                          inherit(ps, pack.copy(
                            traitMembers = membersInter(pack.traitMembers, trt.members.valuesIterator.filterNot(_.isValueParam).toList),
                            tparamMembers = pack.tparamMembers ++ tpms
                          ))

                        case cls: TypedNuCls =>
                          val parNme = cls.nme.name
                          
                          pack.baseClsNme.foreach { cls =>
                            err(msg"cannot inherit from more than one base class: ${
                              cls} and ${parNme}", loc)
                          }
                          
                          inherit(ps, pack.copy(
                            baseClsNme = S(parNme), 
                            baseClsMembers = argMembs ++ cls.members.valuesIterator.filterNot(_.isValueParam), 
                            tparamMembers = pack.tparamMembers ++ tpms
                          ))
                          
                        case als: TypedNuAls => // Should be rejected in `typedParents`
                          inherit(ps, pack)
                        
                      }
                      case Nil =>
                        val thisType = WithType(pack.superType, RecordType(typedParams)(ttp(td.params.getOrElse(Tup(Nil)), isType = true)))(provTODO) &
                          clsNameToNomTag(td)(provTODO, ctx) &
                          RecordType(tparamFields)(TypeProvenance(Loc(td.tparams.map(_._2)), "type parameters", isType = true)) &
                          sig_ty
                        
                        trace(s"${lvl}. Finalizing inheritance with $thisType <: $finalType") {
                          assert(finalType.level === lvl)
                          constrain(thisType, finalType)
                        }()
                        
                        // println(s"${lvl}. Finalized inheritance with $superType ~> $thisType")
                        pack.copy(superType = thisType)
                    }
                    
                    // * We start from an empty super type.
                    val baseType =
                      RecordType(Nil)(TypeProvenance(Loc(td.parents).map(_.left), "Object"))
                    
                    val paramMems = typedParams.map(f => NuParam(f._1, f._2)(lvl))
                    
                    val Pack(thisType, mxnMembers, _, baseClsMembers, traitMembers, tparamMembers) =
                      inherit(typedParents, Pack(baseType, tparamMems ++ paramMems, N, Nil, Nil, Map.empty))
                    
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    ctx += "super" -> VarSymbol(thisType, Var("super"))
                    val ttu = typeTypingUnit(td.body, topLevel = false)
                    
                    val (baseClsImplemMembers, baseClsIfaceMembers) =
                      baseClsMembers.partition(_.isImplemented)
                    
                    val newImplems = ttu.implementedMembers
                    
                    // * Those member implementations we inherit from the base class that are not overridden
                    val implemsInheritedFromBaseCls = {
                      val possiblyOverridingNames = (newImplems.iterator ++ mxnMembers).map(_.name).toSet
                      baseClsImplemMembers.iterator
                        .filterNot(possiblyOverridingNames contains _.name)
                        .toList
                    }
                    // * ... must type check against the trait signatures
                    trace(s"Checking base class implementations...") {
                      println(implemsInheritedFromBaseCls, newImplems)
                      overrideCheck(implemsInheritedFromBaseCls, traitMembers)
                    }()
                    
                    // * The following are type signatures all implementations must satisfy
                    // * (but we already know the base class implems satisfy the baseClsMembers signatures)
                    val ifaceMembers = membersInter(baseClsMembers, traitMembers)
                    
                    val clsSigns = typedSignatureMembers.map(_._2)
                    
                    // * We now check current and non-overridden mixin implementations against 
                    // * the signatures from the base class and traits
                    val toCheck =
                      (newImplems.iterator ++ mxnMembers).distinctBy(_.name).toList
                    trace(s"Checking new implementations...") {
                      overrideCheck(toCheck,
                        (clsSigns.iterator ++ ifaceMembers).distinctBy(_.name).toList)
                    }()
                    
                    val impltdMems = (
                      newImplems // local members override mixin members:
                      ++ mxnMembers // local and mixin members override parent members:
                      ++ baseClsImplemMembers
                    ).distinctBy(_.name)
                    
                    overrideCheck(clsSigns, ifaceMembers)
                    
                    implemCheck(impltdMems,
                      (clsSigns.iterator ++ ifaceMembers.iterator)
                      .distinctBy(_.name).filterNot(_.isImplemented).toList)
                    
                    val allMembers =
                      (ifaceMembers ++ impltdMems).map(d => d.name -> d).toMap ++ typedSignatureMembers
                    
                    TypedNuCls(outerCtx.lvl, td,
                      tparams, typedParams, allMembers,
                      TopType,
                      sig_ty,
                      inheritedTags,
                      tparamMembers
                    )(thisType)
                  }
                  
                case Mxn =>
                  if (td.parents.nonEmpty)
                    err(msg"mixin definitions cannot yet extend parents" -> Loc(td.parents) :: Nil)
                  val outer = ctx
                  ctx.nest.nextLevel { implicit ctx =>
                    ctx ++= paramSymbols
                    ctx ++= typedSignatures.map(nt => nt._1.name -> VarSymbol(nt._2, nt._1.nme))
                    val paramMems = typedParams.map(f => NuParam(f._1, f._2)(lvl))
                    val thisTV = freshVar(provTODO, N, S("this"))
                    val superTV = freshVar(provTODO, N, S("super"))
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    ctx += "super" -> VarSymbol(superTV, Var("super"))
                    val ttu = typeTypingUnit(td.body, topLevel = false)
                    val impltdMems = ttu.implementedMembers
                    val signs = typedSignatureMembers.map(_._2)
                    overrideCheck(impltdMems, signs)
                    implemCheck(impltdMems, signs)
                    val mems = impltdMems.map(m => m.name -> m).toMap ++ typedSignatureMembers
                    TypedNuMxn(outer.lvl, td, thisTV, superTV, tparams, typedParams, mems)
                  }
              }
              
          }
          
        } finally { isComputing = false }
        
        result = S(res)
        res
        
      }(r => s"Completed ${r} where ${r.showBounds}")
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
  
  def refreshHelper2(raw: PolyNuDecl, v: Var, parTargs: Opt[Ls[ST]])
        (implicit ctx: Ctx): (MutMap[TV, ST], Map[Str, NuParam]) = {
    val freshened: MutMap[TV, ST] = MutMap.empty
    val rawName = v.name
    
    val parTP = raw.tparams.lazyZip(parTargs.getOrElse(raw.tparams.map {
        case (_, tv, _) => freshVar(tv.prov, S(tv), tv.nameHint)(tv.level)
    })).map { case ((tn, _tv, vi), targ) =>
      val tv = (targ match {
        case tv: TV => 
          println(s"Passing ${tn.name} :: ${_tv} <=< ${tv}")
          tv
        case _ =>
          println(s"Assigning ${tn.name} :: ${_tv} := $targ where ${targ.showBounds}")
          val tv =
            freshVar(_tv.prov, S(_tv), _tv.nameHint)(targ.level)
          println(s"Set ${tv} ~> ${_tv}")
          assert(tv.assignedTo.isEmpty)
          tv.assignedTo = S(targ)
          // println(s"Assigned ${tv.assignedTo}")
          tv
      })
      freshened += _tv -> tv
      rawName+"#"+tn.name -> NuParam(tn, FieldType(S(tv), tv)(provTODO))(ctx.lvl)
    }
    
    freshened -> parTP.toMap
  }
  
}

