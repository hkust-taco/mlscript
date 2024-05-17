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
    def isPublic: Bool
    def isPrivate: Bool = !isPublic // * We currently don't support `protected`
    
    def isValueParam: Bool = this match {
      case p: NuParam => !p.isType
      case _ => false
    }
    
    protected def withLevel[R](k: Ctx => R)(implicit ctx: Ctx): R = k(ctx.copy(lvl = ctx.lvl + 1))
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, freshened: MutMap[TV, ST])
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
  
  
  case class NuParam(nme: NameRef, ty: FieldType, isPublic: Bool)(val level: Level)
      extends NuMember with TypedNuTermDef
  {
    def name: Str = nme.name
    def isType: Bool = nme.isInstanceOf[TypeName]
    def kind: DeclKind =
      if (isType) Als // FIXME?
      else Val
    def toLoc: Opt[Loc] = nme.toLoc
    def isImplemented: Bool = true
    def isVirtual: Bool = false // TODO allow annotating parameters with `virtual`
    def typeSignature: ST = ty.ub
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, freshened: MutMap[TV, ST])
          : NuParam =
      NuParam(nme, ty.freshenAbove(lim, rigidify), isPublic)(ctx.lvl)
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuParam =
        NuParam(nme, ty.update(t => f(pol.map(!_), t), t => f(pol, t)), isPublic)(level)
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): NuParam =
        NuParam(nme, ty.update(t => f(pol.contravar, t), t => f(pol, t)), isPublic)(level)
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
    def isPublic = true // TODO
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, freshened: MutMap[TV,ST])
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
    def isPublic = true // TODO
    
    // TODO dedup with the one in TypedNuCls
    lazy val virtualMembers: Map[Str, NuMember] = members ++ tparams.map {
      case (nme @ TypeName(name), tv, _) => 
        td.nme.name+"#"+name -> NuParam(nme, FieldType(S(tv), tv)(provTODO), isPublic = true)(level)
    } ++ parentTP
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, freshened: MutMap[TV,ST])
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
        params: Opt[Ls[Var -> FieldType]],
        auxCtorParams: Opt[Ls[Var -> ST]],
        members: Map[Str, NuMember],
        thisTy: ST,
        sign: ST,
        inheritedTags: Set[TypeName],
        parentTP: Map[Str, NuMember]
      ) extends TypedNuTypeDef(Cls) with PolyNuDecl
  {
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def nme: TypeName = td.nme
    def name: Str = nme.name
    def isImplemented: Bool = true
    def isPublic = true // TODO
    
    /** The type of a palin term reference to this type definition. */
    def typeSignature(usesNew: Bool, loco: Opt[Loc])(implicit raise: Raise): ST =
      typeSignatureOf(usesNew, loco, td, level, tparams, params, auxCtorParams, sign, inheritedTags)
    
    /** Includes class-name-coded type parameter fields. */
    lazy val virtualMembers: Map[Str, NuMember] = members ++ tparams.map {
      case (nme @ TypeName(name), tv, _) => 
        td.nme.name+"#"+name -> NuParam(nme, FieldType(S(tv), tv)(provTODO), isPublic = true)(level)
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
          val traversed = MutSet.empty[Pol -> TV]
          
          object Trav extends Traverser2.InvariantFields {
            override def apply(pol: PolMap)(ty: ST): Unit =
                trace(s"Trav($pol)($ty)") {
                ty match {
              case tv: TypeVariable => if (traversed.add(pol(tv) -> tv)) {
                store(tv) = store.getOrElse(tv, VarianceInfo.bi) && (pol(tv) match {
                  case S(true) => VarianceInfo.co
                  case S(false) => VarianceInfo.contra
                  case N => VarianceInfo.in
                })
                super.apply(pol)(ty)
              }
              case ty @ RecordType(fs) =>
                // Ignore type param members such as `C#A` in `{C#A: mut A30'..A30'}`
                super.apply(pol)(RecordType(fs.filterNot(_._1.name.contains('#')))(ty.prov))
              case _ => super.apply(pol)(ty)
            }
            }()
          }
          members.foreachEntry {
            case (_, m: NuParam) if m.isType =>
            case (_, m) => Trav.applyMem(PolMap.pos)(m)
          }
          
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
          (implicit ctx: Ctx, freshened: MutMap[TV,ST])
          : TypedNuCls = { val outer = ctx; withLevel { implicit ctx =>
      TypedNuCls(outer.lvl, td,
        tparams.map(tp => (tp._1, tp._2.freshenAbove(lim, rigidify).assertTV, tp._3)),
        params.map(_.mapValues(_.freshenAbove(lim, rigidify))),
        auxCtorParams.map(_.mapValues(_.freshenAbove(lim, rigidify))),
        members.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
        thisTy.freshenAbove(lim, rigidify),
        sign.freshenAbove(lim, rigidify),
        inheritedTags,
        parentTP.mapValuesIter(_.freshenAbove(lim, rigidify)).toMap,
      )
    }}
    
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuCls =
        TypedNuCls(level, td,
          tparams.map(tp => (tp._1, f(N, tp._2).assertTV, tp._3)),
          params.map(_.mapValues(_.update(t => f(pol.map(!_), t), t => f(pol, t)))),
          auxCtorParams.map(_.mapValues(t => f(pol.map(!_), t))),
          members.mapValuesIter(_.mapPol(pol, smart)(f)).toMap,
          f(pol.map(!_), thisTy),
          f(pol, sign),
          inheritedTags,
          parentTP.mapValuesIter(_.mapPol(pol, smart)(f)).toMap,
        )
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuCls =
        TypedNuCls(level, td,
          tparams.map(tp => (tp._1, f(pol.invar, tp._2).assertTV, tp._3)),
          params.map(_.mapValues(_.update(t => f(pol.contravar, t), t => f(pol, t)))),
          auxCtorParams.map(_.mapValues(t => f(pol.contravar, t))),
          members.mapValuesIter(_.mapPolMap(pol)(f)).toMap,
          f(pol.contravar, thisTy),
          f(pol, sign),
          inheritedTags,
          parentTP.mapValuesIter(_.mapPolMap(pol)(f)).toMap,
        )
    
    override def toString: Str = s"TypedNuCls($level, ${td.nme},\n\t$tparams,\n\t$params,\n\tthis: $thisTy, ${
      members.lnIndent()},\n\t: $sign, $inheritedTags, $parentTP)"
  }
  
  
  case class TypedNuMxn(
        level: Level, td: NuTypeDef,
        thisTy: ST, superTy: ST,
        tparams: TyParams,
        params: Ls[Var -> FieldType],
        members: Map[Str, NuMember],
      ) extends TypedNuTypeDef(Mxn) with PolyNuDecl
  {
    def decl: NuTypeDef = td
    def kind: DeclKind = td.kind
    def nme: TypeName = td.nme
    def name: Str = nme.name
    def isImplemented: Bool = true
    def isPublic = true // TODO

    lazy val virtualMembers: Map[Str, NuMember] = members ++ tparams.map {
      case (nme @ TypeName(name), tv, _) => 
        td.nme.name+"#"+name -> NuParam(nme, FieldType(S(tv), tv)(provTODO), isPublic = false)(level)
    }
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, freshened: MutMap[TV,ST])
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
    def isPublic = true // TODO
    def typeSignature: ST = errType
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, freshened: MutMap[TV, ST]) =
      this
    def mapPol(pol: Opt[Bool], smart: Bool)(f: (Opt[Bool], SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      this
    def mapPolMap(pol: PolMap)(f: (PolMap, SimpleType) => SimpleType)
          (implicit ctx: Ctx): TypedNuTermDef =
      this
  }
  
  // Field `thisRef` is defined when the member refers to `this` selecting a field on it
  // e.g., val x = this
  // Field `refs` contains all `Var`s accessed by the member with their possible `this` qualifiers (`None` if it is an unqualified access)
  case class RefMap(thisRef: Opt[Var], refs: Set[(Var, Opt[Var])])
  object RefMap {
    lazy val nothing: RefMap = RefMap(N, Set.empty)
  }
  
  /** Note: the type `bodyType` is stored *without* its polymorphic wrapper! (unlike `typeSignature`) */
  case class TypedNuFun(level: Level, fd: NuFunDef, bodyType: ST)(val isImplemented: Bool)
      extends TypedNuDecl with TypedNuTermDef {
    def kind: DeclKind = Val
    def name: Str = fd.nme.name
    def symbolicName: Opt[Str] = fd.symbolicNme.map(_.name)
    def toLoc: Opt[Loc] = fd.toLoc
    lazy val prov = TypeProvenance(toLoc, "member")
    def isPublic: Bool = !fd.isLetOrLetRec
    lazy val typeSignature: ST =
      if (fd.isMut) bodyType
      else PolymorphicType.mk(level, bodyType)
    
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, freshened: MutMap[TV, ST])
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

    def getFunRefs: RefMap = fd.rhs match {
      case L(term) => getRefs(term)
      case _ => RefMap.nothing
    }
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
          (implicit ctx: Ctx, freshened: MutMap[TV, ST])
          : TypedTypingUnit =
      TypedTypingUnit(implementedMembers.map(_.freshenAbove(lim, rigidify)), result.map(_.freshenAbove(lim, rigidify)))
    override def toString: Str = s"TypedTypingUnit(${(implementedMembers :+ result).lnIndent()})"
  }
  
  
  def typeSignatureOf(usesNew: Bool, loco: Opt[Loc], td: NuTypeDef, level: Level,
      tparams: TyParams, params: Opt[Params], acParams: Opt[Ls[Var -> ST]], selfTy: ST, ihtags: Set[TypeName])
      (implicit raise: Raise)
      : ST = 
    if ((td.kind is Mod) && params.isEmpty)
      if (tparams.isEmpty) 
        TypeRef(td.nme, Nil)(provTODO)
      else PolymorphicType.mk(level,
        TypeRef(td.nme, tparams.map(_._2))(provTODO))
    else if ((td.kind is Cls) || (td.kind is Mod)) {
      if (td.kind is Mod)
        err(msg"Parameterized modules are not yet supported", loco)
      println(s"params: $params $acParams")
      if (!usesNew)
        if (params.isEmpty)
          if (acParams.isEmpty)
            return err(msg"Class ${td.nme.name} cannot be instantiated as it exposes no constructor", loco)
          else err(msg"Construction of unparameterized class ${td.nme.name} should use the `new` keyword", loco)
        else if (acParams.isDefined)
          err(msg"Construction of class with auxiliary constructor should use the `new` keyword", loco)
      val ps: Params = acParams match {
        case S(acParams) => acParams.mapValues(_.toUpper(noProv))
        case N => params.getOrElse(Nil)
      }
      PolymorphicType.mk(level,
        FunctionType(
          TupleType(ps.mapKeys(some))(provTODO),
          TypeRef(td.nme, tparams.map(_._2))(provTODO)
        )(provTODO)
      )
    } else errType // FIXME
  
  
  def getRefs(body: Statement): RefMap = {
    val refs = mutable.HashSet[(Var, Opt[Var])]()

    def visit(s: Located): Opt[Var] = s match {
      case Sel(ths @ Var("this"), v) =>
        refs.add((v, S(ths)))
        N
      case v @ Var(name) =>
        if (name === "this") S(v)
        else {
          refs.add((v, N))
          N
        }
      case _: Type => N
      case _: Term| _: Statement | _: NuDecl | _: IfBody | _: CaseBranches | _: TypingUnit =>
          s.children.foldLeft[Opt[Var]](N)((r, c) => r.orElse(visit(c)))
    }

    RefMap(visit(body), refs.toSet)
  }
  
  /** Type checks a typing unit, which is a sequence of possibly-mutually-recursive type and function definitions
   *  interleaved with plain statements. */
  def typeTypingUnit(tu: TypingUnit, outer: Opt[Outer])
        (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType]): TypedTypingUnit =
      trace(s"${ctx.lvl}. Typing $tu")
  {
    val topLevel: Bool = outer.isEmpty
    
    // println(s"vars ${vars}")
    
    tu.entities.foreach {
      case fd: NuFunDef if fd.isLetRec.isEmpty && outer.exists(_.kind is Block) =>
        err(msg"Cannot use `val` or `fun` in local block; use `let` instead.", fd.toLoc)
      case _ =>
    }
    
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
    val implems = decls.filter {
      case fd @ NuFunDef(_, nme, snme, tparams, R(rhs)) =>
        if (fd.isLetOrLetRec)
          err(s"`let` bindings must have a right-hand side", fd.toLoc)
        funSigs.updateWith(nme.name) {
          case S(s) =>
            err(s"A type signature for '${nme.name}' was already given", fd.toLoc)
            S(s)
          case N => S(fd)
        }
        false // * Explicit signatures will already be typed in DelayedTypeInfo's typedSignatures
      case _ => true
    }
    
    val sigInfos = if (topLevel) funSigs.map { case (nme, decl) =>
      val lti = new DelayedTypeInfo(decl, implicitly)
      
      // TODO check against duplicated symbolic names in same scope...
      decl.symbolicNme.foreach(snme => ctx += snme.name -> lti)
      
      decl.name -> lti
    } else Nil
    
    val infos = implems.map {
      case _decl: NuDecl =>
        val decl = _decl match {
          case fd: NuFunDef =>
            assert(fd.signature.isEmpty)
            funSigs.get(fd.nme.name) match {
              case S(sig) =>
                fd.copy()(fd.declareLoc, fd.virtualLoc, fd.mutLoc, S(sig), outer, fd.genField, fd.annotations)
              case _ =>
                fd.copy()(fd.declareLoc, fd.virtualLoc, fd.mutLoc, fd.signature, outer, fd.genField, fd.annotations)
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
          case fd: NuFunDef =>
            // TODO check against duplicated symbolic names in same scope...
            fd.symbolicNme.foreach(snme => ctx += snme.name -> lti)
        }
        named.updateWith(decl.name) {
          case sv @ S(v) =>
            decl match {
              case NuFunDef(S(_), _, _, _, _) => ()
              case _ =>
                err(msg"Redefinition of '${decl.name}'", decl.toLoc)
            }
            S(lti)
          case N =>
            S(lti)
        }
        decl.name -> lti
    }
    
    ctx ++= infos
    ctx ++= sigInfos
    
    val tpdFunSigs = sigInfos.mapValues(_.complete() match {
      case res: TypedNuFun if res.fd.isDecl =>
        TopType
      case res: TypedNuFun =>
        res.typeSignature
      case _ => die
    }).toMap
    
    // * Complete typing of block definitions and add results to context
    val completedInfos = (infos ++ sigInfos).mapValues(_.complete() match {
      case res: TypedNuFun =>
        tpdFunSigs.get(res.name) match {
          case S(expected) =>
            implicit val prov: TP =
              TypeProvenance(res.fd.toLoc, res.fd.describe)
            subsume(res.typeSignature, expected)
          case _ =>
            // * Generalize functions as they are typed.
            // * Note: eventually we'll want to first reorder their typing topologically so as to maximize polymorphism.
            ctx += res.name -> VarSymbol(res.typeSignature, res.fd.nme)
            res.symbolicName.foreach(ctx += _ -> VarSymbol(res.typeSignature, res.fd.nme))
        }
        CompletedTypeInfo(res)
      case res => CompletedTypeInfo(res)
    })
    ctx ++= completedInfos
    
    val returnsLastExpr = outer.map(_.kind) match {
      case N | S(Block | Val) => true
      case S(_: TypeDefKind) => false
    }
    
    // * Type the block statements
    def go(stmts: Ls[Statement]): Opt[ST] = stmts match {
      case s :: stmts =>
        val res_ty = s match {
          case decl: NuDecl => N
          case t: Term =>
            implicit val genLambdas: GenLambdas = true
            val ty = typeTerm(t)
            if (!topLevel && !(stmts.isEmpty && returnsLastExpr)) {
              t match {
                // * We do not include `_: Var` because references to `fun`s and lazily-initialized
                // * definitions may have side effects.
                case _: Lit | _: Lam =>
                  warn("Pure expression does nothing in statement position.", t.toLoc)
                case _ =>
                  constrain(mkProxy(ty, TypeProvenance(t.toCoveringLoc, "expression in statement position")), UnitType)(
                    raise = err => raise(WarningReport( // Demote constraint errors from this to warnings
                      msg"Expression in statement position should have type `()`." -> N ::
                      msg"Use a comma expression `... , ()` to explicitly discard non-unit values, making your intent clearer." -> N ::
                      err.allMsgs, newDefs)),
                    prov = TypeProvenance(t.toLoc, t.describe), ctx)
              }
            }
            S(ty)
          case s: DesugaredStatement =>
            err(msg"Illegal position for this ${s.describe} statement.", s.toLoc)(raise)
            N
          case _ => die
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
    val name: Str = decl.name
    
    private implicit val prov: TP =
      TypeProvenance(decl.toLoc, decl.describe)
    
    // * TODO should we use this? It could potentially improve error messages
    implicit val newDefsInfo: Map[Str, (TypeDefKind, Int)] = Map.empty // TODO?
    
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
    
    private var typingParents = false
    lazy val typedParents: Ls[TypedParentSpec] = ctx.nest.nextLevel { implicit ctx =>
      
      ctx ++= paramSymbols
      
      if (typingParents === true) {
        err(msg"Unhandled cyclic parent specification", decl.toLoc)
        Nil
      } else
      try {typingParents = true; parentSpecs}.flatMap {
        case (p, v @ Var(parNme), lti, parTargs, parArgs) =>
          trace(s"${lvl}. Typing parent spec $p") {
            val info = lti.complete()
            info match {
              
              case rawMxn: TypedNuMxn =>
                
                // println(s"Raw $rawMxn")
                val (fr, ptp) = refreshHelper(rawMxn, v, if (parTargs.isEmpty) N else S(parTargs)) // type args inferred
                val mxn = {
                  implicit val frenshened: MutMap[TV,ST] = fr
                  implicit val ctx: Ctx = outerCtx
                  rawMxn.freshenAbove(info.level, rigidify = false)
                }
                // println(s"Fresh $mxn")
                
                val argMembs =  {                      
                  if (parArgs.sizeCompare(mxn.params) =/= 0)
                    err(msg"mixin $parNme expects ${
                      mxn.params.size.toString} parameter(s); got ${parArgs.size.toString}", Loc(v :: parArgs.unzip._2))
                  
                  val paramMems = mxn.params.lazyZip(parArgs).flatMap {
                    case (nme -> p, _ -> Fld(FldFlags(mut, spec, get), a)) => // TODO factor this with code for classes:
                      assert(!mut && !spec && !get, "TODO") // TODO check mut, spec, get
                      implicit val genLambdas: GenLambdas = true
                      val a_ty = typeTerm(a)
                      p.lb.foreach(constrain(_, a_ty))
                      constrain(a_ty, p.ub)
                      val isPublic = mxn.members(nme.name).isPublic
                      val fty = if (p.lb.isDefined)
                          // * We don't refine the field type when it's mutable as that could lead to muable updates being rejected
                          FieldType(p.lb, p.ub)(provTODO)
                        else FieldType(p.lb, a_ty)(provTODO)
                      Option.when(isPublic)(NuParam(nme, fty, isPublic = isPublic)(lvl))
                  }
                  
                  paramMems //++ mxn.members.valuesIterator
                  
                }
                println(s"Mixin arg members $argMembs")
                
                S((mxn, argMembs, 
                  Map.empty[Str, NuMember], // TODO add ptp here once we support explicit type args
                  p.toLoc
                ))
                
              case rawTrt: TypedNuTrt =>
                if (parArgs.nonEmpty) err(msg"trait arguments are not yet supported", p.toLoc)

                val (fr, ptp) = refreshHelper(rawTrt, v, if (parTargs.isEmpty) N else S(parTargs))  // infer ty args if not provided
                val trt = {
                  implicit val frenshened: MutMap[TV,ST] = fr
                  implicit val ctx: Ctx = outerCtx
                  rawTrt.freshenAbove(info.level, rigidify = false)
                }
                
                val paramMems = Nil // * Maybe support trait params? (not sure)
                
                S((trt, paramMems, ptp ++ trt.parentTP, p.toLoc))
                
              case rawCls: TypedNuCls =>
                
                // println(s"Raw $rawCls where ${rawCls.showBounds}")
                
                val (fr, ptp) = refreshHelper(rawCls, v, if (parTargs.isEmpty) N else S(parTargs)) // infer ty args if not provided
                val cls = {
                  implicit val frenshened: MutMap[TV,ST] = fr
                  implicit val ctx: Ctx = outerCtx
                  rawCls.freshenAbove(info.level, rigidify = false)
                }
                
                // println(s"Fresh[${ctx.lvl}] $cls where ${cls.showBounds}")
                
                def checkArgsNum(effectiveParamSize: Int) =
                  if (parArgs.sizeCompare(effectiveParamSize) =/= 0)
                    err(msg"class $parNme expects ${
                      effectiveParamSize.toString} parameter(s); got ${parArgs.size.toString
                        }", Loc(v :: parArgs.unzip._2))
                
                val argMembs = {
                  implicit val genLambdas: GenLambdas = true
                  cls.auxCtorParams match {
                    case S(ps) =>
                      checkArgsNum(ps.size)
                      ps.lazyZip(parArgs).map {
                        case (nme -> p_ty, _ -> Fld(FldFlags(mut, spec, get), a)) =>
                          assert(!mut && !spec && !get, "TODO") // TODO check mut, spec, get
                          val a_ty = typeTerm(a)
                          constrain(a_ty, p_ty)
                      }
                      Nil
                    case N => cls.params match {
                        case S(ps) =>
                          checkArgsNum(ps.size)
                          ps.lazyZip(parArgs).flatMap {
                            case (nme -> p, _ -> Fld(FldFlags(mut, spec, get), a)) =>
                              assert(!mut && !spec && !get, "TODO") // TODO check mut, spec, get
                              val a_ty = typeTerm(a)
                              p.lb.foreach(constrain(_, a_ty))
                              constrain(a_ty, p.ub)
                              val isPublic = cls.members(nme.name).isPublic
                              val fty = if (p.lb.isDefined)
                                  // * We don't refine the field type when it's mutable as that could lead to muable updates being rejected
                                  FieldType(p.lb, p.ub)(provTODO)
                                else FieldType(p.lb, a_ty)(provTODO)
                              Option.when(isPublic)(NuParam(nme, fty, isPublic = isPublic)(lvl))
                          }
                        case N =>
                          checkArgsNum(0)
                          Nil
                      }
                  }
                }
                println(s"Class arg members $argMembs")
                
                S((cls, argMembs, ptp ++ cls.parentTP, p.toLoc))
                
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
      } finally { typingParents = false }
      
    }
    
    
    def lookupTags(parents: Ls[ParentSpec], tags: Set[TypeName]): Set[TypeName] = {
      parents match {
        case Nil => tags
        case (p, Var(nm), lti, _, _) :: ps => lti match {
          case lti: DelayedTypeInfo => lti.kind match {
            case Trt | Cls | Mod => lookupTags(ps, Set.single(TypeName(nm)) union lti.inheritedTags union tags)
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

    private var inheritedTagsStartedComputing = false
    lazy val inheritedTags: Set[TypeName] =
      if (inheritedTagsStartedComputing) Set.empty // * Deals with malformed inheritances (cycles)
      else {
        inheritedTagsStartedComputing = true
        lookupTags(parentSpecs, Set.empty)
      }
    
    lazy val tparams: TyParams = ctx.nest.nextLevel { implicit ctx =>
      decl match {
        case td: NuTypeDef =>
          td.tparams.map(tp =>
            (tp._2, freshVar(
              TypeProvenance(tp._2.toLoc, "type parameter",
                S(tp._2.name),
                isType = true),
              N, S(tp._2.name)), tp._1))
        case fd: NuFunDef =>
          fd.tparams.map { tn =>
            (tn, freshVar(
              TypeProvenance(tn.toLoc, "method type parameter",
                originName = S(tn.name),
                isType = true),
              N, S(tn.name)), N)
          }
      }
    }
    lazy val tparamsSkolems: Ls[Str -> SkolemTag] = tparams.map {
      case (tp, tv, vi) => (tp.name, SkolemTag(tv)(tv.prov))
    }
    
    lazy val explicitVariances: VarianceStore =
      MutMap.from(tparams.iterator.map(tp => tp._2 -> tp._3.getOrElse(VarianceInfo.in)))
    
    def varianceOf(tv: TV)(implicit ctx: Ctx): VarianceInfo =
      // TODO make use of inferred vce if result is completed
      explicitVariances.get(tv).getOrElse(VarianceInfo.in)
    
    lazy private implicit val vars: Map[Str, SimpleType] =
      outerVars ++ tparamsSkolems
    
    lazy val typedParams: Opt[Ls[Var -> FieldType]] = ctx.nest.nextLevel { implicit ctx =>
      decl match {
        case td: NuTypeDef =>
          td.params.map(_.fields.flatMap {
            case (S(nme), Fld(FldFlags(mut, spec, getter), value)) =>
              assert(!mut && !spec, "TODO") // TODO
              val tpe = value.toTypeRaise
              val ty = typeType(tpe)
              nme -> FieldType(N, ty)(provTODO) :: Nil
            case (N, Fld(FldFlags(mut, spec, getter), nme: Var)) =>
              assert(!mut && !spec, "TODO") // TODO
              // nme -> FieldType(N, freshVar(ttp(nme), N, S(nme.name)))(provTODO)
              nme -> FieldType(N, err(msg"${td.kind.str.capitalize} parameters currently need type annotations",
                nme.toLoc))(provTODO) :: Nil
            case (_, fld) =>
              err(msg"Unsupported field specification", fld.toLoc)
              Nil
          })
        case fd: NuFunDef => N
      }
    }
    
    lazy val paramSymbols = typedParams.getOrElse(Nil).map(p => p._1.name -> VarSymbol(p._2.ub, p._1))
    
    // TODO also import signatures from base classes and mixins!
    lazy val (typedSignatures, funImplems) : (Ls[(NuFunDef, ST)], Ls[NuFunDef]) = decl match {
      case td: NuTypeDef => ctx.nest.nextLevel { implicit ctx =>
        val (signatures, rest) = td.body.entities.partitionMap {
          case fd @ NuFunDef(_, nme, snme, tparams, R(rhs)) if !fd.isLetOrLetRec =>
            L((fd, rhs))
          // TODO also pick up signature off implems with typed params/results
          case s => R(s)
        }
        val implems = rest.collect { case fd @ NuFunDef(N | S(false), nme, snme, tparams, L(rhs)) => fd }
        
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
    lazy val privateParams: Set[Var] = decl match {
      case td: NuTypeDef =>
        // td.params.dlof(_.fields)(Nil).iterator.collect {
        //   case (S(nme), Fld(flags, _)) if !flags.genGetter => nme
        //   case (N, Fld(flags, nme: Var)) if !flags.genGetter => nme
        //   // case (N, Fld(flags, _)) => die
        // }.toSet
        td.params.dlof(_.fields)(Nil).iterator.flatMap {
          case (S(nme), Fld(flags, _)) => Option.when(!flags.genGetter)(nme)
          case (N, Fld(flags, nme: Var)) => Option.when(!flags.genGetter)(nme)
          case (N, Fld(flags, _)) => die
        }.toSet
      case _: NuFunDef => Set.empty
    }
    
    lazy val allFields: Set[Var] = decl match {
      case td: NuTypeDef =>
        (td.params.getOrElse(Tup(Nil)).fields.iterator.flatMap(_._1) ++ td.body.entities.iterator.collect {
          case fd: NuFunDef if !fd.isLetOrLetRec => fd.nme
        }).toSet ++ inheritedFields ++ tparams.map {
          case (nme @ TypeName(name), tv, _) =>
            Var(td.nme.name+"#"+name).withLocOf(nme)
        }
      case _: NuFunDef => Set.empty
    }
    
    lazy val typedFields: Map[Var, FieldType] = {
      (typedParams.getOrElse(Nil).toMap
        // -- privateFields
        -- inheritedFields /* parameters can be overridden by inherited fields/methods */
      ) ++ typedSignatures.iterator.map(fd_ty => fd_ty._1.nme -> (
            if (fd_ty._1.isMut) FieldType(S(fd_ty._2), fd_ty._2)(
              fd_ty._2.prov) // FIXME prov
            else fd_ty._2.toUpper(noProv)
          )) ++
        typedParents.flatMap(_._3).flatMap {
          case (k, p: NuParam) => Var(k) -> p.ty :: Nil
          case _ => Nil
        }
    }
    
    private lazy val isGeneralized: Bool = decl match {
      case fd: NuFunDef =>
        println(s"Type ${fd.nme.name} polymorphically? ${fd.isGeneralized} && (${ctx.lvl} === 0 || ${
          fd.signature.nonEmpty} || ${fd.outer.exists(_.kind isnt Mxn)})")
        // * We only type polymorphically:
        // * definitions that can be generalized (ie `fun`s or function-valued `let`s and `val`s); and
        fd.isGeneralized && (
              ctx.lvl === 0 // * top-level definitions
          ||  fd.signature.nonEmpty // * definitions with a provided type signature
          ||  fd.outer.exists(_.kind isnt Mxn) // * definitions NOT occurring in mixins
        )
        // * The reason to not type unannotated mixin methods polymorphically is that
        // * doing so yields too much extrusion and cycle check failures,
        // * in the context of inferred precisely-typed open recursion through mixin composition.
      case _ => die
    }
    
    lazy val mutRecTV: TV = decl match {
      case fd: NuFunDef =>
        freshVar(
          TypeProvenance(decl.toLoc, decl.describe, S(decl.name), decl.isInstanceOf[NuTypeDef]),
          N,
          S(decl.name)
        )(if (isGeneralized) level + 1 else level)
      case _ => lastWords(s"Not supposed to use mutRecTV for ${decl.kind}")
    }
    
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
                  if (fd.isLetRec.isDefined) checkNoTyParams()
                  implicit val gl: GenLambdas =
                    // * Don't generalize lambdas if we're already in generalization mode;
                    // * unless the thing is just a simple let binding with functions,
                    // * as in `let r = if true then id else x => x`
                    !isGeneralized && fd.isLetRec.isDefined && !fd.genField
                  val outer_ctx = ctx
                  val body_ty = if (isGeneralized) {
                    // * Note:
                    // * Can't use `ctx.poly` instead of `ctx.nextLevel` here because all the methods
                    // * in the current typing unit are quantified together.
                    // * So instead of inserting an individual `forall` in the type of each method,
                    // * we consider the `forall` to be implicit in the definition of TypedNuFun,
                    // * and that forall is eschewed while typing mutually-recursive methods
                    // * in the same typing unit, which will see the method's type through its mutRecTV.
                    // * This avoids cyclic-looking constraints due to the polymorphic recursion limitation.
                    // * Subnote: in the future, we should type each mutual-recursion-component independently
                    // *  and polymorphically wrt to external uses of them.
                    // *  Currently they are typed in order.
                    ctx.nextLevel { implicit ctx: Ctx =>
                      assert(fd.tparams.sizeCompare(tparamsSkolems) === 0, (fd.tparams, tparamsSkolems))
                      vars ++ tparamsSkolems |> { implicit vars =>
                        typeTerm(body)
                      }
                    }
                  } else {
                    if (fd.isMut) {
                      constrain(typeTerm(body), mutRecTV)
                      mutRecTV
                    }
                    else typeTerm(body)
                  }
                  val tp = TypeProvenance(fd.toLoc, s"definition of ${fd.isLetRec match {
                      case S(_) => if (fd.genField) "value" else "let binding"
                      case N => "method"
                    }} ${fd.nme.name}")
                  TypedNuFun(ctx.lvl, fd, body_ty.withProv(tp))(isImplemented = true)
              }
              ctx.nextLevel { implicit ctx: Ctx => constrain(res_ty.bodyType, mutRecTV) }

              // Check annotations
              fd.annotations.foreach(ann => {
                implicit val gl: GenLambdas = false;
                val annType = typeTerm(ann)
                constrain(annType, AnnType)
              })

              res_ty
              
              
            case td: NuTypeDef =>
              
              /** Check no `this` access in ctor statements or val rhs and reject unqualified accesses to virtual members.. */
              def qualificationCheck(members: Ls[NuMember], stmts: Ls[Statement], base: Ls[NuMember], sigs: Ls[NuMember]): Unit = {
                val cache = mutable.HashMap[Str, Opt[Var]]()
                val sigMap = sigs.map(m => m.name -> m).toMap
                val allMembers = sigMap ++ (base.iterator ++ members).map(m => m.name -> m).toMap

                def isVirtual(nf: TypedNuFun) =
                  nf.fd.isVirtual || (sigMap.get(nf.name) match {
                    case S(sig: TypedNuFun) => sig.fd.virtualLoc.nonEmpty // The signature is virtual by itself, so we need to check the virtual keyword
                    case _ => false
                  })

                // Return S(v) when there is an invalid access to the v.
                def checkThisInCtor(refs: RefMap, name: Opt[Str], stack: Ls[Str])(expection: Bool): Opt[Var] = {
                  def run: Opt[Var] = {
                    refs.thisRef.orElse(
                      refs.refs.foldLeft[Opt[Var]](N)((res, p) => res.orElse(allMembers.get(p._1.name) match {
                        case S(nf: TypedNuFun) if name.fold(true)(name => name =/= p._1.name) && !stack.contains(p._1.name) => // Avoid cycle checking
                          p._2 match {
                            case q @ S(_) if !expection || isVirtual(nf) => q
                            case _ => checkThisInCtor(nf.getFunRefs, S(p._1.name), p._1.name :: stack)(false)
                          }
                        case _ => N // Refer to outer 
                      }))
                    )
                  }

                  name.fold(run)(name => cache.getOrElseUpdate(name, run))
                }

                def checkUnqualifiedVirtual(refs: RefMap, parentLoc: Opt[Loc]) =
                  refs.refs.foreach(p => if (p._2.isEmpty) allMembers.get(p._1.name) match { // unqualified access
                    case S(nf: TypedNuFun) if isVirtual(nf) =>
                      err(msg"Unqualified access to virtual member ${p._1.name}" -> parentLoc ::
                        msg"Declared here:" -> nf.fd.toLoc
                      :: Nil)
                    case _ => ()
                  })

                // If the second error message location is covered by the first one,
                // we show the first error message with more precise location
                def mergeErrMsg(msg1: Message -> Opt[Loc], msg2: Message -> Opt[Loc]) =
                  (msg1._2, msg2._2) match {
                    case (S(loc1), l @ S(loc2)) if loc1 covers loc2 => msg1._1 -> l :: Nil
                    case _ => msg1 :: msg2 :: Nil
                  }

                members.foreach {
                  case tf @ TypedNuFun(_, fd, _) =>
                    val refs = tf.getFunRefs
                    if (fd.isLetRec.isDefined) checkThisInCtor(refs, S(tf.name), tf.name :: Nil)(true) match {
                      case S(v) => // not a function && access `this` in the ctor
                        err(mergeErrMsg(msg"Cannot access `this` while initializing field ${tf.name}" -> fd.toLoc,
                          msg"The access to `this` is here" -> v.toLoc))
                      case N => ()
                    }
                    checkUnqualifiedVirtual(refs, fd.toLoc)
                  case _ => ()
                }
                stmts.foreach{
                  case Asc(Var("this"), _) => ()
                  case s =>
                    val refs = getRefs(s)
                    checkThisInCtor(refs, N, Nil)(false) match {
                      case S(v) =>
                        err(mergeErrMsg(msg"Cannot access `this` during object initialization" -> s.toLoc,
                          msg"The access to `this` is here" -> v.toLoc))
                      case N => ()
                    }
                    checkUnqualifiedVirtual(refs, s.toLoc)
                }
              }
              
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
                    def mkErr(postfix: Ls[Message -> Opt[Loc]]) = err(
                      msg"Member `${m.name}` is declared (or its declaration is inherited) but is not implemented in `${
                          td.nme.name}`" -> td.nme.toLoc ::
                        msg"Declared here:" -> m.toLoc ::
                        postfix)
                    implemsMap.get(m.name) match {
                      case S(impl) =>
                        if (impl.isPrivate) mkErr(
                          msg"Note: ${impl.kind.str} member `${m.name}` is private and cannot be used as a valid implementation" -> impl.toLoc ::
                          Nil)
                      case N =>
                        mkErr(Nil)
                    }
                  }
                }
                
              }
              
              /** Checks overriding members against their parent types. */
              def overrideCheck(newMembers: Ls[NuMember], signatures: Ls[NuMember], clsSigns: Ls[NuMember]): Unit =
                  ctx.nextLevel { implicit ctx: Ctx => // * Q: why exactly do we need `ctx.nextLevel`?
                
                val sigMap = MutMap.empty[Str, NuMember]
                signatures.foreach { m =>
                  sigMap.updateWith(m.name) {
                    case S(_) => die
                    case N => S(m)
                  }
                }
                
                newMembers.foreach { m =>
                  println(s"Checking overriding for ${m} against ${sigMap.get(m.name)}...")
                  (m, sigMap.get(m.name)) match {
                    case (_, N) =>
                    case (m: TypedNuTermDef, S(sig: TypedNuTermDef)) => sig match {
                      // * If the implementation and the declaration are in the same class,
                      // * it does not require to be virtual.
                      case _ if sig.isPrivate => () // * Private members are not actually inherited
                      case td: TypedNuFun if (!td.fd.isVirtual && !clsSigns.contains(sig)) =>
                        err(msg"${m.kind.str.capitalize} member '${m.name
                            }' is not virtual and cannot be overridden" -> m.toLoc ::
                          msg"Originally declared here:" -> sig.toLoc ::
                          Nil)
                      case p: NuParam if (!p.isVirtual && !clsSigns.contains(p)) =>
                        err(msg"Inherited parameter named '${m.name
                            }' is not virtual and cannot be overridden" -> m.toLoc ::
                          msg"Originally declared here:" -> sig.toLoc ::
                          Nil)
                      case _ =>
                        m match {
                          case fun: TypedNuFun if (fun.fd.isLetOrLetRec) =>
                            err(msg"Cannot implement ${m.kind.str} member '${m.name
                                }' with a let binding" -> m.toLoc ::
                              msg"Originally declared here:" -> sig.toLoc ::
                              Nil)
                          case _ =>
                        }
                        val mSign = m.typeSignature
                        implicit val prov: TP = mSign.prov
                        constrain(mSign, sig.typeSignature)
                    }
                    case (_, S(that)) =>
                      err(msg"${m.kind.str.capitalize} member '${m.name}' cannot override ${
                          that.kind.str} member of the same name declared in parent" -> td.toLoc ::
                        msg"Originally declared here:" -> that.toLoc ::
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
                      }, a.fd.nme, N/*no sym name?*/, a.fd.tparams, a.fd.rhs)(
                        a.fd.declareLoc, a.fd.virtualLoc, a.fd.mutLoc,
                        N, a.fd.outer orElse b.fd.outer, a.fd.genField, a.fd.annotations)
                      S(TypedNuFun(a.level, fd, a.bodyType & b.bodyType)(a.isImplemented || b.isImplemented))
                    case (a: NuParam, S(b: NuParam)) => 
                      if (!a.isPublic) S(b) else if (!b.isPublic) S(a)
                      else S(NuParam(a.nme, a.ty && b.ty, isPublic = true)(a.level))
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
              
              // * To type signatures correctly, we need to deal with unbound type variables 'X,
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
                  // case lb :: Nil => TypeBounds.mk(TopType, lb)
                  case lb :: Nil => lb
                  case _ => die
                }
              }

              // Check annotations
              td.annotations.foreach { ann =>
                implicit val gl: GenLambdas = false
                val annType = typeTerm(ann)
                constrain(annType, AnnType)
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
                    
                    def inherit(parents: Ls[TypedParentSpec], tags: ST, members: Ls[NuMember],
                            tparamMembs: Map[Str, NuMember], sig_ty: ST)
                          : (ST, Ls[NuMember], Map[Str, NuMember], ST) =
                        parents match {
                      case (trt: TypedNuTrt, argMembs, tpms, loc) :: ps =>
                        assert(argMembs.isEmpty, argMembs)
                        inherit(ps,
                          tags & trt.sign,
                          membersInter(members, trt.members.values.toList),
                          tparamMembs ++ tpms,   // with type members of parent class
                          sig_ty & trt.sign,
                        )
                      case (_, _, _, loc) :: ps => 
                        err(msg"A trait can only inherit from other traits", loc)
                        inherit(ps, tags, members, tparamMembs, sig_ty)
                      case Nil => (tags, members, tparamMembs, sig_ty)
                    }
                    val (tags, trtMembers, tparamMembs, sig_ty) =
                      inherit(typedParents, trtNameToNomTag(td)(noProv, ctx), Nil, Map.empty,
                        td.sig.fold(TopType: ST)(typeTypeSignature))
                    
                    td.body.entities.foreach {
                      case fd @ NuFunDef(_, _, _, _, L(_)) =>
                        err(msg"Method implementations in traits are not yet supported", fd.toLoc)
                      case _ =>
                    }
                    
                    val ttu = typeTypingUnit(td.body, S(td))
                    
                    val allMembers = (
                      trtMembers.iterator.map(d => d.name -> d)
                      ++ ttu.implementedMembers.map(d => d.name -> d)
                      ++ typedSignatureMembers
                    ).toMap
                    
                    // check trait overriding
                    overrideCheck(typedSignatureMembers.map(_._2), trtMembers, Nil)
                    
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
                      ctx.nextLevel { implicit ctx: Ctx => typeType(sig) }
                    case N =>
                      err(msg"Type alias definition requires a right-hand side", td.toLoc)
                  }
                  
                  TypedNuAls(outerCtx.lvl, td, tparams, body_ty)
                  
                case Cls | Mod =>
                  
                  ctx.nest.nextLevel { implicit ctx =>
                    
                    if ((td.kind is Mod) && typedParams.nonEmpty)
                      // * Can we do better? (Memoization semantics?)
                      err(msg"${td.kind.str.capitalize} parameters are not supported",
                        typedParams.fold(td.nme.toLoc)(tp => Loc(tp.iterator.map(_._1))))
                    
                    if (!td.isAbstract && !td.isDecl) td.sig match {
                      case S(sig) => warn(
                        msg"Self-type annotations have no effects on non-abstract ${td.kind.str} definitions" -> sig.toLoc
                        :: msg"Did you mean to use `extends` and inherit from a parent class?" -> N
                        :: Nil)
                      case N =>
                    }
                    
                    ctx ++= paramSymbols
                    ctx ++= typedSignatures.map(nt => nt._1.name -> VarSymbol(nt._2, nt._1.nme))
                    
                    val sig_ty = td.sig.fold(TopType: ST)(typeTypeSignature)
                    
                    implicit val prov: TP =
                      TypeProvenance(decl.toLoc, decl.describe)
                    
                    val finalType = thisTV
                    
                    val tparamMems = tparams.map { case (tp, tv, vi) => // TODO use vi
                      val fldNme = td.nme.name + "#" + tp.name
                      val skol = SkolemTag(tv)(tv.prov)
                      NuParam(TypeName(fldNme).withLocOf(tp), FieldType(S(skol), skol)(tv.prov), isPublic = true)(lvl)
                    }
                    val tparamFields = tparamMems.map(p => p.nme.toVar -> p.ty)
                    assert(!typedParams.exists(_.keys.exists(tparamFields.keys.toSet)), ???)
                    
                    case class Pack(
                      superType: ST,
                      mxnMembers: Ls[NuMember], 
                      baseClsNme: Opt[Str], 
                      baseClsMembers: Ls[NuMember], 
                      traitMembers: Ls[NuMember],
                      tparamMembers: Map[Str, NuMember],
                      selfSig: ST,
                    )
                    
                    def inherit(parents: Ls[TypedParentSpec], pack: Pack): Pack = parents match {
                      case (p, argMembs, tpms, loc) :: ps => println(s"=> Inheriting from $p"); p match {
                        
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
                                  case m: TypedNuFun =>
                                    // val ty = m.typeSignature
                                    // * ^ Note: this also works and is more precise (some types made more specific),
                                    // *    but it causes duplication of recursive type structures
                                    // *    in typical SuperOOP mixin compositions, so it's better to be less precise
                                    // *    but simpler/more efficient/more concise here.
                                    val ty = m.bodyType
                                    m.fd.nme -> ty.toUpper(provTODO)
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
                            tparamMembers = pack.tparamMembers ++ tpms,
                            selfSig = pack.selfSig & trt.sign
                          ))
                        
                        case cls: TypedNuCls =>
                          val parNme = cls.nme.name
                          
                          pack.baseClsNme.foreach { cls =>
                            err(msg"Cannot inherit from more than one base class: ${
                              cls} and ${parNme}", loc)
                          }
                          
                          val (baseParamMems, otherBaseMems) =
                            // cls.members.toList.partition(_._2.isValueParam)
                            cls.members.valuesIterator.toList.partition(_.isValueParam)
                          
                          println(s"argMembs $argMembs")
                          
                          println(s"selfSig ${cls.sign}")
                          
                          inherit(ps, pack.copy(
                            baseClsNme = S(parNme), 
                            // baseClsMembers = argMembs ++ cls.members.valuesIterator.filterNot(_.isValueParam), 
                            // baseClsMembers = argMembs.filterNot(_.isPrivate) ++ cls.members.valuesIterator.filterNot(_.isValueParam), 
                            // baseClsMembers = cls.members.valuesIterator.filter(_.isValueParam) ++ argMembs ++ cls.members.valuesIterator.filterNot(_.isValueParam), 
                            // baseClsMembers = baseParamMems ::: argMembs ::: otherBaseMems, 
                            baseClsMembers = argMembs ++ cls.members.valuesIterator,
                            tparamMembers = pack.tparamMembers ++ tpms,
                            selfSig = pack.selfSig & cls.sign
                          ))
                          
                        case als: TypedNuAls => // Should be rejected in `typedParents`
                          inherit(ps, pack)
                        
                      }
                      case Nil =>
                        println(s"Done inheriting: $pack")
                        
                        val thisType = WithType(pack.superType,
                            RecordType(typedParams.getOrElse(Nil))(ttp(td.params.getOrElse(Tup(Nil)), isType = true))
                          )(provTODO) &
                            clsNameToNomTag(td)(provTODO, ctx) &
                            RecordType(tparamFields)(TypeProvenance(Loc(td.tparams.map(_._2)), "type parameters", isType = true))
                        
                        trace(s"${lvl}. Finalizing inheritance with $thisType <: $finalType") {
                          assert(finalType.level === lvl)
                          constrain(thisType & sig_ty, finalType)
                          
                        }()
                        
                        if (!td.isAbstract) trace(s"Checking self signature...") {
                          constrain(thisType, pack.selfSig)
                        }()
                        
                        // println(s"${lvl}. Finalized inheritance with $superType ~> $thisType")
                        pack.copy(superType = thisType, selfSig = pack.selfSig & sig_ty)
                    }
                    
                    // * We start from an empty super type.
                    val baseType =
                      RecordType(Nil)(TypeProvenance(Loc(td.parents).map(_.left), "Object"))
                    
                    val paramMems = typedParams.getOrElse(Nil).map(f =>
                      NuParam(f._1, f._2, isPublic = !privateParams.contains(f._1))(lvl))
                    
                    val Pack(thisType, mxnMembers, _, baseClsMembers, traitMembers, tparamMembers, selfSig) =
                      inherit(typedParents, Pack(baseType, tparamMems ++ paramMems, N, Nil, Nil, Map.empty, sig_ty))
                    
                    // println(s"Final self-type: ${selfSig}")
                    
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    ctx += "super" -> VarSymbol(thisType, Var("super"))
                    val ttu = typeTypingUnit(td.body, S(td))
                    
                    // * `baseClsImplemMembers` actually also includes parameter members and their arg-based refinements
                    val (baseClsImplemMembers, baseClsIfaceMembers) =
                      baseClsMembers.partition(_.isImplemented)
                    
                    println(s"baseClsImplemMembers ${baseClsImplemMembers}")
                    
                    val newImplems = ttu.implementedMembers
                    
                    val clsSigns = typedSignatureMembers.map(_._2)
                    
                    trace(s"Checking `this` accesses...") {
                      val toCheckImplems = newImplems.filter(_.isImplemented)
                      qualificationCheck(toCheckImplems, td.body.entities.filter {
                        case _: NuDecl => false
                        case _ => true
                      } ++ td.ctor.fold[Ls[Statement]](Nil)(s => s.body.stmts), baseClsMembers, clsSigns)
                    }()
                    
                    // * Those member implementations we inherit from the base class that are not overridden
                    val implemsInheritedFromBaseCls = {
                      val possiblyOverridingNames = (newImplems.iterator ++ mxnMembers).map(_.name).toSet
                      baseClsImplemMembers.iterator.distinctBy(_.name)
                        .filterNot(possiblyOverridingNames contains _.name)
                        .toList
                    }
                    // * ... must type check against the trait signatures
                    trace(s"Checking base class implementations against inherited signatures...") {
                      overrideCheck(implemsInheritedFromBaseCls, traitMembers, Nil)
                    }()
                    
                    // * The following are type signatures all implementations must satisfy
                    // * (but we already know the base class implems satisfy the baseClsMembers signatures)
                    val ifaceMembers = membersInter(baseClsMembers, traitMembers)
                    
                    // * We now check current and non-overridden mixin implementations against 
                    // * the signatures from the base class and traits
                    val toCheck =
                      (newImplems.iterator ++ mxnMembers).distinctBy(_.name).toList
                    
                    trace(s"Checking new implementations against inherited signatures...") {
                      overrideCheck(toCheck,
                        (clsSigns.iterator ++ ifaceMembers).distinctBy(_.name).toList, clsSigns)
                    }()
                    
                    val impltdMems = (
                      newImplems // local members override mixin members:
                      ++ mxnMembers // local and mixin members override parent members:
                      ++ baseClsImplemMembers
                    ).distinctBy(_.name)
                    
                    trace(s"Checking new signatures against inherited signatures...") {
                      overrideCheck(clsSigns, ifaceMembers, clsSigns)
                    }()
                    
                    trace(s"Checking signature implementations...") {
                      implemCheck(impltdMems,
                        (clsSigns.iterator ++ ifaceMembers.iterator)
                        .distinctBy(_.name).filterNot(_.isImplemented).toList)
                    }()
                    
                    val allMembers =
                      (ifaceMembers ++ impltdMems).map(d => d.name -> d).toMap ++ typedSignatureMembers
                    
                    println(s"allMembers $allMembers")
                    
                    val auxCtorParams = td.ctor match {
                      case S(ctor @ Constructor(ps, bod)) => outerCtx.nest.nextLevel { implicit ctx =>
                        def getterError(loco: Opt[Loc]) =
                          err(msg"Cannot use `val` in constructor parameters", loco)
                        val res = ps.fields.map {
                          case (S(nme), Fld(FldFlags(mut, spec, getter), value)) =>
                            assert(!mut && !spec, "TODO") // TODO
                            if (getter)
                              // TODO we could support this to some extent
                              getterError(nme.toLoc)
                            value.toType match {
                              case R(tpe) =>
                                val ty = typeType(tpe)
                                nme -> ty
                              case _ => ???
                            }
                          case (N, Fld(FldFlags(mut, spec, getter), nme: Var)) =>
                            assert(!mut && !spec, "TODO") // TODO
                            if (getter)
                              getterError(nme.toLoc)
                            nme -> freshVar(ttp(nme), N, S(nme.name))
                          case (N, Fld(_, rhs)) =>
                            Var("<error>") -> err(msg"Unsupported constructor parameter shape", rhs.toLoc)
                        }
                        res.foreach { case (nme, ty) => ctx += nme.name -> VarSymbol(ty, nme) }
                        implicit val gl: GenLambdas = false
                        implicit val prov: TP =
                          TypeProvenance(ctor.toLoc, "auxiliary class constructor")
                        val bodStmts = bod match {
                          case Blk(sts) => sts
                          case _ => bod :: Nil
                        }
                        // * TODO later: for each `typedParams`, first add sthg like `ctx += lhs.name -> UndefinedParam(...)`
                        val classParamsMap = MutMap.from(typedParams.getOrElse(Nil).mapValues(some))
                        bodStmts.foreach {
                          case Eqn(lhs, rhs) =>
                            classParamsMap.updateWith(lhs) {
                              case S(S(p)) =>
                                val rhs_ty = typeTerm(rhs)
                                constrain(rhs_ty, p.ub)
                                ctx += lhs.name -> VarSymbol(rhs_ty, lhs)
                                S(N)
                              case S(N) =>
                                err(msg"Class parameter '${lhs.name}' was already set", lhs.toLoc)
                                N
                              case N =>
                                err(msg"Unknown class parameter '${lhs.name}'", lhs.toLoc)
                                N
                            }
                          case stmt: DesugaredStatement =>
                            typeStatement(stmt, allowPure = false)
                          case _ => die
                        }
                        S(res)
                      }
                      case N => N
                    }
                    
                    // * After a class is type checked, we need to "solidify" the inferred types of its unannotated mutable fields,
                    // * otherwise they would be treated as polymorphic, which would be wrong.
                    allMembers.foreachEntry {
                      case (nme, v: TypedNuFun) if v.fd.isMut =>
                        // * A bit hacky but should work:
                        v.bodyType.unwrapProvs match {
                          case _ if v.fd.rhs.isRight || v.fd.signature.nonEmpty =>
                            // * If the type was annotated, we don't need to do anything.
                          case tv: TV if tv.assignedTo.isEmpty => // * Could this `tv` ever be assigned?
                            val res_ty = tv.lowerBounds.reduceOption(_ | _)
                              .getOrElse(err(msg"Could not infer a type for unused mutable field $nme", v.toLoc))
                            println(s"Setting type of $nme based on inferred lower bounds: $tv := $res_ty")
                            tv.assignedTo = S(res_ty)
                          case ty => lastWords(ty.toString)
                        }
                      case (nme, m) =>
                    }
                    
                    TypedNuCls(outerCtx.lvl, td,
                      tparams,
                      typedParams,
                      auxCtorParams.orElse(Option.when(
                        typedParams.isEmpty && (td.kind is Cls) && !td.isAbstract)(Nil)),
                      allMembers,
                      TopType,
                      if (td.isAbstract) selfSig else sig_ty,
                      inheritedTags,
                      tparamMembers
                    ).tap(_.variances) // * Force variance computation
                  }
                  
                case Mxn =>
                  if (td.parents.nonEmpty)
                    err(msg"mixin definitions cannot yet extend parents" -> Loc(td.parents) :: Nil)
                  val outer = ctx
                  ctx.nest.nextLevel { implicit ctx =>
                    ctx ++= paramSymbols
                    ctx ++= typedSignatures.map(nt => nt._1.name -> VarSymbol(nt._2, nt._1.nme))
                    val paramMems = typedParams.map(_.map(f =>
                      f._1.name -> NuParam(f._1, f._2, !privateParams.contains(f._1))(lvl))).getOrElse(Nil).toMap
                    val thisTV = freshVar(provTODO, N, S("this"))
                    val superTV = freshVar(provTODO, N, S("super"))
                    ctx += "this" -> VarSymbol(thisTV, Var("this"))
                    ctx += "super" -> VarSymbol(superTV, Var("super"))
                    val ttu = typeTypingUnit(td.body, S(td))
                    val impltdMems = ttu.implementedMembers
                    val signs = typedSignatureMembers.map(_._2)
                    overrideCheck(impltdMems, signs, signs)
                    implemCheck(impltdMems, signs)
                    val mems = paramMems ++ impltdMems.map(m => m.name -> m).toMap ++ typedSignatureMembers
                    TypedNuMxn(outer.lvl, td, thisTV, superTV, tparams, typedParams.getOrElse(Nil), mems)
                  }
              }
              
          }
          
        } finally { isComputing = false }
        
        result = S(res)
        res
        
      }(r => s"Completed ${r} where ${r.showBounds}")
    }
    def typeSignature(usesNew: Bool, loco: Opt[Loc])(implicit raise: Raise): ST =
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
          // * We want to avoid forcing completion of types needlessly
          // * OTOH we need the type to be completed to use its aux ctor (whose param types are optional)
          // * TODO: avoid forcing when the aux ctor has type-annotated params
          if (td.ctor.isDefined) complete() match {
            case cls: TypedNuCls =>
              cls.typeSignature(usesNew, loco)
            case _: TypedNuDummy => errType
            case _ => die
          } else typeSignatureOf(usesNew, loco, td, level, tparams, typedParams, N, TopType, inheritedTags)
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
            freshVar(_tv.prov, S(_tv), _tv.nameHint,
              lbs = _tv.lowerBounds,
              ubs = _tv.upperBounds,
              )(targ.level)
          println(s"Set ${tv} ~> ${_tv}")
          assert(tv.assignedTo.isEmpty)
          
          // * Note: no checks that the assigned variable satisfies the bounds...
          // * When we support bounded types, bounds check will be needed at the type definition site
          assert(tv.lowerBounds.isEmpty, tv.lowerBounds)
          assert(tv.upperBounds.isEmpty, tv.upperBounds)
          tv.assignedTo = S(targ)
          
          // println(s"Assigned ${tv.assignedTo}")
          tv
      })
      freshened += _tv -> tv
      rawName+"#"+tn.name -> NuParam(tn, FieldType(S(tv), tv)(provTODO), isPublic = true)(ctx.lvl)
    }
    
    freshened -> parTP.toMap
  }
  
}

