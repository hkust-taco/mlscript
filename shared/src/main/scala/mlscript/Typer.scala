package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

/** A class encapsulating type inference state.
 *  It uses its own internal representation of types and type variables, using mutable data structures.
 *  Inferred SimpleType values are then turned into CompactType values for simplification.
 *  In order to turn the resulting CompactType into a mlscript.Type, we use `expandCompactType`.
 */
class Typer(var dbg: Boolean, var verbose: Bool, var explainErrors: Bool) extends ConstraintSolver with TypeSimplifier {
  
  type Raise = Diagnostic => Unit
  type Binding = Str -> TypeScheme
  type Bindings = Map[Str, TypeScheme]
  
  case class TypeDef(
    kind: TypeDefKind,
    nme: TypeName,
    tparams: List[TypeName],
    targs: List[TypeVariable],
    body: Type,
    mthDecls: List[MethodDef[Right[Term, Type]]],
    mthDefs: List[MethodDef[Left[Term, Type]]],
    baseClasses: Set[Var],
    toLoc: Opt[Loc],
  ) {
    def allBaseClasses(ctx: Ctx)(implicit traversed: Set[Var]): Set[Var] =
      baseClasses.map(v => Var(v.name.toList.mapHead(_.toLower).mkString)) ++
        baseClasses.iterator.filterNot(traversed).flatMap(v =>
          ctx.tyDefs.get(v.name).fold(Set.empty[Var])(_.allBaseClasses(ctx)(traversed + v)))
    val targsMap: Map[Str, TypeVariable] = tparams.map(_.name).zip(targs).toMap
  }
  
  /** targsMaps: stores the map from type parameters to type variables for polymorphic classes and methods
   *    first layer: class name;
   *    second layer: method name or None for top-level class type parameters;
   *    third layer: type parameter.
   *    For "normal" contexts, all innermost values should be `TypeVariable`s.
   *    For the nested context during method typing, the innermost values can also be `TraitTag`s.
   */
  case class Ctx(parent: Opt[Ctx], env: MutMap[Str, TypeScheme], lvl: Int, inPattern: Bool, tyDefs: Map[Str, TypeDef],
      mthDecls: Map[Str, Map[Str, PolymorphicType]], mthDefs: Map[Str, Map[Str, PolymorphicType]],
      methodBase: MutMap[Str, Option[Var]], abcCache: MutMap[Str, Set[Var]]) {
    def +=(b: Binding): Unit = env += b
    def ++=(bs: IterableOnce[Binding]): Unit = bs.iterator.foreach(+=)
    def get(name: Str): Opt[TypeScheme] = env.get(name) orElse parent.dlof(_.get(name))(N)
    def contains(name: Str): Bool = env.contains(name) || parent.exists(_.contains(name))
    def nest: Ctx = copy(Some(this), MutMap.empty)
    def nextLevel: Ctx = copy(lvl = lvl + 1)
    def allBaseClassesOf(name: Str): Set[Var] = abcCache.getOrElse(name,
      tyDefs.get(name).fold(Set.empty[Var])(_.allBaseClasses(this)(Set.empty).tap(abcCache += name -> _)))
    private val thisTyCache = MutMap.empty[Str, TypeRef]
    def thisType(tn: Str)(implicit prov: TypeProvenance): TypeRef = thisTyCache.getOrElse(tn, {
      val td = tyDefs(tn)
      TypeRef(td, td.targs)(prov, this).tap(thisTyCache += tn -> _)
    })
  }
  object Ctx {
    def init: Ctx = Ctx(
      parent = N,
      env = MutMap.from(builtinBindings),
      lvl = 0,
      inPattern = false,
      tyDefs = Map.from(builtinTypes.map(t => t.nme.name -> t)),
      mthDecls = Map.empty,
      mthDefs = Map.empty,
      methodBase = MutMap.empty,
      abcCache = MutMap.empty)
  }
  implicit def lvl(implicit ctx: Ctx): Int = ctx.lvl
  
  import TypeProvenance.{apply => tp}
  def ttp(trm: Term, desc: Str = ""): TypeProvenance =
    TypeProvenance(trm.toLoc, if (desc === "") trm.describe else desc)
  def originProv(loco: Opt[Loc], desc: Str): TypeProvenance = {
    // TODO make a new sort of provenance for where types and type varianles are defined
    // tp(loco, desc)
    // ^ This yields unnatural errors like:
      //│ ╟── expression of type `B` is not a function
      //│ ║  l.6: 	    method Map[B]: B -> A
      //│ ║       	               ^
    // So we should keep the info but not shadow the more relevant later provenances
    noProv
  }
  
  val noProv: TypeProvenance = tp(N, "expression")
  
  val TopType: ExtrType = ExtrType(false)(noProv)
  val BotType: ExtrType = ExtrType(true)(noProv)
  val UnitType: ClassTag = ClassTag(Var("unit"), Set.empty)(noProv)
  val BoolType: ClassTag = ClassTag(Var("bool"), Set.empty)(noProv)
  val TrueType: ClassTag = ClassTag(Var("true"), Set.single(Var("bool")))(noProv)
  val FalseType: ClassTag = ClassTag(Var("false"), Set.single(Var("bool")))(noProv)
  val IntType: ClassTag = ClassTag(Var("int"), Set.single(Var("number")))(noProv)
  val DecType: ClassTag = ClassTag(Var("number"), Set.empty)(noProv)
  val StrType: ClassTag = ClassTag(Var("string"), Set.empty)(noProv)
  
  val ErrTypeId: SimpleTerm = Var("error")
  
  // TODO rm this obsolete definition (was there for the old frontend)
  private val primTypes =
    List("unit" -> UnitType, "bool" -> BoolType, "int" -> IntType, "number" -> DecType, "string" -> StrType,
      "anything" -> TopType, "nothing" -> BotType)
  
  val builtinTypes: Ls[TypeDef] =
    TypeDef(Cls, TypeName("int"), Nil, Nil, Top, List.empty, List.empty, Set.single(Var("number")), N) ::
    TypeDef(Cls, TypeName("number"), Nil, Nil, Top, List.empty, List.empty, Set.empty, N) ::
    TypeDef(Cls, TypeName("bool"), Nil, Nil, Top, List.empty, List.empty, Set.empty, N) ::
    TypeDef(Cls, TypeName("true"), Nil, Nil, Top, List.empty, List.empty, Set.single(Var("bool")), N) ::
    TypeDef(Cls, TypeName("false"), Nil, Nil, Top, List.empty, List.empty, Set.single(Var("bool")), N) ::
    TypeDef(Cls, TypeName("string"), Nil, Nil, Top, List.empty, List.empty, Set.empty, N) ::
    TypeDef(Als, TypeName("anything"), Nil, Nil, Top, List.empty, List.empty, Set.empty, N) ::
    TypeDef(Als, TypeName("nothing"), Nil, Nil, Bot, List.empty, List.empty, Set.empty, N) ::
    TypeDef(Cls, TypeName("error"), Nil, Nil, Top, List.empty, List.empty, Set.empty, N) ::
    TypeDef(Cls, TypeName("unit"), Nil, Nil, Top, List.empty, List.empty, Set.empty, N) ::
    Nil
  val primitiveTypes: Set[Str] =
    builtinTypes.iterator.filter(_.kind is Cls).map(_.nme.name).toSet
  val builtinBindings: Bindings = {
    val tv = freshVar(noProv)(1)
    import FunctionType.{ apply => fun }
    val intBinOpTy = fun(IntType, fun(IntType, IntType)(noProv))(noProv)
    val intBinPred = fun(IntType, fun(IntType, BoolType)(noProv))(noProv)
    Map(
      "true" -> TrueType,
      "false" -> FalseType,
      "document" -> BotType,
      "window" -> BotType,
      "not" -> fun(BoolType, BoolType)(noProv),
      "succ" -> fun(IntType, IntType)(noProv),
      "log" -> PolymorphicType(0, fun(tv, UnitType)(noProv)),
      "discard" -> PolymorphicType(0, fun(tv, UnitType)(noProv)),
      "add" -> intBinOpTy,
      "sub" -> intBinOpTy,
      "mul" -> intBinOpTy,
      "div" -> intBinOpTy,
      "sqrt" -> fun(IntType, IntType)(noProv),
      "lt" -> intBinPred,
      "le" -> intBinPred,
      "gt" -> intBinPred,
      "ge" -> intBinPred,
      "concat" -> fun(StrType, fun(StrType, StrType)(noProv))(noProv),
      "eq" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(v, fun(v, BoolType)(noProv))(noProv))
      },
      "ne" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(v, fun(v, BoolType)(noProv))(noProv))
      },
      "error" -> BotType,
      "+" -> intBinOpTy,
      "-" -> intBinOpTy,
      "*" -> intBinOpTy,
      "/" -> intBinOpTy,
      "<" -> intBinPred,
      ">" -> intBinPred,
      "<=" -> intBinPred,
      ">=" -> intBinPred,
      "==" -> intBinPred,
      "&&" -> fun(BoolType, fun(BoolType, BoolType)(noProv))(noProv),
      "||" -> fun(BoolType, fun(BoolType, BoolType)(noProv))(noProv),
      "id" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(v, v)(noProv))
      },
      "if" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(BoolType, fun(v, fun(v, v)(noProv))(noProv))(noProv))
      },
    ) ++ primTypes ++ primTypes.map(p => "" + p._1.capitalize -> p._2) // TODO settle on naming convention...
  }
  
  def tparamField(clsNme: TypeName, tparamNme: TypeName): Var =
    Var(clsNme.name + "#" + tparamNme.name)
  
  def clsNameToNomTag(td: TypeDef)(prov: TypeProvenance, ctx: Ctx): SimpleType = {
    require(td.kind is Cls)
    ClassTag(Var(td.nme.name.head.toLower.toString + td.nme.name.tail),
      td.allBaseClasses(ctx)(Set.single(Var(td.nme.name))))(prov)
  }
  def trtNameToNomTag(td: TypeDef)(prov: TypeProvenance, ctx: Ctx): SimpleType = {
    require(td.kind is Trt)
    TraitTag(Var(td.nme.name.head.toLower.toString + td.nme.name.tail))(prov)
  }
  
  def baseClassesOf(tyd: mlscript.TypeDef): Set[Var] =
    if (tyd.kind === Als) Set.empty else baseClassesOf(tyd.body)
  
  private def baseClassesOf(ty: Type): Set[Var] = ty match {
      case Inter(l, r) => baseClassesOf(l) ++ baseClassesOf(r)
      case TypeName(nme) => Set.single(Var(nme))
      case AppliedType(b, _) => baseClassesOf(b)
      case Record(_) => Set.empty
      case _: Union => Set.empty
      case _ => Set.empty // TODO TupleType?
    }
  
  /** Extract the mapping of type arguments applied to the base classes and traits from the body of a type definition.
   *  Only inheritance from a conjunction of `TypeName`s, `AppliedType`s and `Record`s are legal. */
  def targsAppOf(tyDef: TypeDef)(implicit ctx: Ctx, raise: Raise,
      vars: Map[Str, SimpleType] = Map.empty): Map[Str, Map[Str, SimpleType]] = {
    def rec(ty: Type): Map[Str, Map[Str, SimpleType]] = ty match {
      case Inter(l, r) => rec(l) ++ rec(r)
      case AppliedType(TypeName(bn), ts) => ctx.tyDefs.get(bn).fold(Map(bn -> Map.empty[Str, SimpleType])) {
        td => Map(bn -> td.tparams.map(_.name).zip(ts.map(typeType(_)(ctx.nextLevel, raise, vars))).toMap)
      }
      case Record(_) => Map.empty
      case TypeName(_) => Map.empty
      case _ => Map.empty
    }
    rec(tyDef.body)
  }

  def wrapMethod(tn: Str, bodyTy: PolymorphicType)(implicit prov: TypeProvenance, ctx: Ctx): PolymorphicType =
    PolymorphicType(bodyTy.level, FunctionType(ctx.thisType(tn), bodyTy.body)(prov))

  
  /** Only supports getting the fields of a valid base class type.
   * Notably, does not traverse type variables. */
  def fieldsOf(ty: SimpleType, paramTags: Bool)(implicit raise: Raise): Map[Var, ST] =
  // trace(s"Fields of $ty {${travsersed.mkString(",")}}")
  {
    ty match {
      case tr @ TypeRef(td, targs) => fieldsOf(tr.expandWith(paramTags), paramTags)
      case ComposedType(false, l, r) =>
        mergeMap(fieldsOf(l, paramTags), fieldsOf(r, paramTags))(_ & _)
      case RecordType(fs) => fs.toMap
      case p: ProxyType => fieldsOf(p.underlying, paramTags)
      case Without(base, ns) => fieldsOf(base, paramTags).filter(ns contains _._1)
      case TypeBounds(lb, ub) => fieldsOf(ub, paramTags)
      case _: ObjectTag | _: FunctionType | _: TupleType | _: TypeVariable
        | _: NegType | _: ExtrType | _: ComposedType => Map.empty
    }
  }
  // ()
  
  def processTypeDefs(newDefs0: List[mlscript.TypeDef])(implicit ctx: Ctx, raise: Raise): Ctx = {
    var allDefs = ctx.tyDefs
    var allEnv = ctx.env.clone
    val newDefs = newDefs0.map { td =>
      implicit val prov: TypeProvenance = tp(td.toLoc, "type definition")
      val n = td.nme
      allDefs.get(n.name).foreach { other =>
        err(msg"Type '$n' is already defined.", td.nme.toLoc)
      }
      if (!n.name.head.isUpper) err(
        msg"Type names must start with a capital letter", n.toLoc)
      td.tparams.groupBy(_.name).foreach { case s -> tps if tps.size > 1 => err(
          msg"Multiple declarations of type parameter ${s} in ${td.kind.str} definition" -> td.toLoc
            :: tps.map(tp => msg"Declared at" -> tp.toLoc))
        case _ =>
      }
      val dummyTargs = td.tparams.map(p =>
        freshVar(originProv(p.toLoc, s"${td.kind.str} type parameter"), S(p.name))(ctx.lvl + 1))
      val td1 = TypeDef(td.kind, td.nme, td.tparams, dummyTargs, td.body, td.mthDecls, td.mthDefs, 
        baseClassesOf(td), td.toLoc)
      allDefs += n.name -> td1
      td1
    }
    import ctx.{tyDefs => oldDefs}
    val subsMapCache = MutMap.empty[Str, Map[Str, Map[SimpleType, SimpleType]]]
    def getSubsMap(tn: Str)(implicit ctx: Ctx): Map[Str, Map[SimpleType, SimpleType]] = subsMapCache.getOrElse(tn,
      (ctx.tyDefs.get(tn) match {
        case S(td) =>
          val targsApp = targsAppOf(td)(ctx, raise, ctx.tyDefs(tn).targsMap)
          td.baseClasses.flatMap { case Var(bn) => ctx.tyDefs.get(bn).map(_.targsMap).map(bn -> _) }.map { case bn -> m =>
            bn -> m.map[SimpleType, SimpleType] {
              case targ -> (tv: TypeVariable) => tv -> targsApp(bn).getOrElse(targ,
                freshVar(noProv)(tv.level)) // Q: Is this `freshVar` legit? Seems it should never happen
              case _ => die
            }
          }.toMap
        case N => Map.empty[Str, Map[SimpleType, SimpleType]]
      }).tap(subsMapCache += tn -> _)
    )
    /* Type the bodies of type definitions, ensuring the correctness of parent types
     * and the regularity of the definitions, then register the constructors and types in the context. */
    def typeTypeDefs(implicit ctx: Ctx): Ctx =
      ctx.copy(tyDefs = oldDefs ++ newDefs.flatMap { td =>
        implicit val prov: TypeProvenance = tp(td.toLoc, "type definition")
        val n = td.nme
        val body_ty = typeType(td.body, simplify = false)(ctx.nextLevel, raise, td.targsMap)
        def allDeclMths(td: TypeDef): Set[Str] = td.baseClasses.flatMap(bc => ctx.mthDecls.get(bc.name).map(_.keySet)
          .getOrElse(allDeclMths(ctx.tyDefs(bc.name)))) ++ td.mthDecls.map(_.nme.name)
        def allDefMths(td: TypeDef): Set[Str] = td.baseClasses.flatMap(bc => ctx.mthDefs.get(bc.name).map(_.keySet)
          .getOrElse(allDefMths(ctx.tyDefs(bc.name)))) ++ td.mthDefs.map(_.nme.name)
        def checkCycle(ty: SimpleType)(implicit travsersed: Set[TypeDef \/ TV]): Bool =
            // trace(s"Cycle? $ty {${travsersed.mkString(",")}}") {
            ty match {
          case TypeRef(td, _) if travsersed(L(td)) =>
            err(msg"illegal cycle involving type ${td.nme.name}", prov.loco)
            false
          case tr @ TypeRef(td, targs) => checkCycle(tr.expand)(travsersed + L(td))
          case ComposedType(_, l, r) => checkCycle(l) && checkCycle(r)
          case NegType(u) => checkCycle(u)
          case p: ProxyType => checkCycle(p.underlying)
          case Without(base, _) => checkCycle(base)
          case TypeBounds(lb, ub) => checkCycle(lb) && checkCycle(ub)
          case tv: TypeVariable => travsersed(R(tv)) || {
            val t2 = travsersed + R(tv)
            tv.lowerBounds.forall(checkCycle(_)(t2)) && tv.upperBounds.forall(checkCycle(_)(t2))
          }
          case _: ExtrType | _: ObjectTag | _: FunctionType | _: RecordType | _: TupleType => true
        }
        // }()
        val rightParents = td.kind match {
          case Als => checkCycle(body_ty)(Set.single(L(td)))
          case k: ObjDefKind =>
            val parentsClasses = MutSet.empty[TypeRef]
            def checkParents(ty: SimpleType): Bool = ty match {
              // case ClassTag(Var("string"), _) => true // Q: always?
              case _: ObjectTag => true // Q: always? // FIXME actually no
              case tr @ TypeRef(td2, _) =>
                td2.kind match {
                  case Cls =>
                    if (td.kind is Cls) {
                      parentsClasses.isEmpty || {
                        err(msg"${td.kind.str} $n cannot inherit from class ${tr.defn.nme
                            } as it already inherits from class ${parentsClasses.head.defn.nme}",
                          prov.loco)
                        false
                      } tap (_ => parentsClasses += tr)
                    } else
                       checkParents(tr.expand)
                  case Trt => checkParents(tr.expand)
                  case Als => 
                    err(msg"cannot inherit from a type alias", prov.loco)
                    false
                }
              case ComposedType(false, l, r) => checkParents(l) && checkParents(r)
              case ComposedType(true, l, r) =>
                err(msg"cannot inherit from a type union", prov.loco)
                false
              case tv: TypeVariable =>
                err(msg"cannot inherit from a type variable", prov.loco)
                false
              case _: FunctionType =>
                err(msg"cannot inherit from a function type", prov.loco)
                false
              case _: NegType =>
                err(msg"cannot inherit from a type negation", prov.loco)
                false
              case _: TupleType =>
                err(msg"cannot inherit from a tuple type", prov.loco)
                false
              case _: Without =>
                err(msg"cannot inherit from a field removal type", prov.loco)
                false
              case _: TypeBounds =>
                err(msg"cannot inherit from type bounds", prov.loco)
                false
              case _: RecordType | _: ExtrType => true
              case p: ProxyType => checkParents(p.underlying)
            }
            lazy val isAbstract = (allDeclMths(td) -- allDefMths(td)).nonEmpty
            checkParents(body_ty) && checkCycle(body_ty)(Set.single(L(td))) && isAbstract.||{
              val fields = fieldsOf(body_ty, true)
              val tparamTags = td.tparams.lazyZip(td.targs).map((tp, tv) =>
                tparamField(td.nme, tp) -> FunctionType(tv, tv)(noProv)).toList
              val ctor = k match {
                case Cls =>
                  val nomTag = clsNameToNomTag(td)(originProv(td.nme.toLoc, "class"), ctx)
                  val fieldsRefined = fields.iterator.map(f =>
                    if (f._1.name.isCapitalized) f
                    else f._1 ->
                      freshVar(noProv,
                        S(f._1.name.drop(f._1.name.indexOf('#') + 1)) // strip any "...#" prefix
                      )(1).tap(_.upperBounds ::= f._2)
                    ).toList
                  PolymorphicType(0, FunctionType(
                    RecordType.mk(fieldsRefined.filterNot(_._1.name.isCapitalized))(noProv),
                    nomTag & RecordType.mk(
                      fieldsRefined ::: tparamTags
                    )(noProv))(originProv(td.nme.toLoc, "class constructor")))
                case Trt =>
                  val nomTag = trtNameToNomTag(td)(originProv(td.nme.toLoc, "trait"), ctx)
                  val tv = freshVar(noProv)(1)
                  tv.upperBounds ::= body_ty
                  PolymorphicType(0, FunctionType(
                    tv, tv & nomTag & RecordType.mk(tparamTags)(noProv)
                  )(originProv(td.nme.toLoc, "trait constructor")))
              }
              ctx += n.name -> ctor
              true
            }
        }
        def checkRegular(ty: SimpleType)(implicit reached: Map[Str, Ls[SimpleType]]): Bool = ty match {
          case tr @ TypeRef(defn, targs) => reached.get(defn.nme.name) match {
            case None => checkRegular(tr.expand)(reached + (defn.nme.name -> targs))
            case Some(tys) =>
              // TODO less syntactic check...
              if (defn.nme === td.nme && tys =/= targs) {
                if (defn.nme.name === td.nme.name)
                  err(msg"Type definition is not regular: it occurs within itself as ${
                    expandType(tr, true).show
                  }, but is defined as ${
                    expandType(TypeRef(defn, td.targs)(noProv, ctx), true).show
                  }", td.toLoc)(raise, noProv)
                false
              } else true
          }
          case _ => ty.children.forall(checkRegular)
        }
        // Note: this will end up going through some types several times... We could make sure to
        //    only go through each type once, but the error messages would be worse.
        if (rightParents && checkRegular(body_ty)(Map(n.name -> td.targs)))
          td.nme.name -> td :: Nil
        else Nil
      })
    /* Type the bodies of method definitions by rigidifying class type parameters,
     * back-substitute with type variables, then register the method signatures in the context. */
    def typeMethods(implicit ctx: Ctx): Ctx = {
      val newMthDecls = MutMap.from(ctx.mthDecls)
      val newMthDefs = MutMap.from(ctx.mthDefs)
      newDefs.filter(td => ctx.tyDefs.isDefinedAt(td.nme.name)).foreach { td =>
        implicit val prov: TypeProvenance = tp(td.toLoc, "type definition")
        val tn = td.nme
        val decls = MutMap.empty[Str, PolymorphicType]
        val defs = MutMap.empty[Str, PolymorphicType]
        val thisCtx = ctx.nest
        val targsMap = td.targsMap.map { 
          case s -> (tv: TypeVariable) => s -> freshenAbove(ctx.lvl, tv, true)
          case _ => die
        }
        val rigid = td.targsMap.map { case pn -> tv => tv -> targsMap(pn) }.toMap[SimpleType, SimpleType]
        val reverseRigid = rigid.map(_.swap).toMap
        thisCtx += "this" -> subst(thisCtx.thisType(tn.name), rigid)
        (td.mthDecls ++ td.mthDefs).foreach { case md @ MethodDef(rec, prt, nme, tparams, rhs) =>
          implicit val prov: TypeProvenance = tp(md.toLoc, rhs.fold(_ => "method definition", _ => "method declaration"))
          tparams.groupBy(_.name).foreach { case s -> tps if tps.size > 1 => err(
              msg"Multiple declarations of type parameter ${s} in ${prov.desc}" -> md.toLoc
                :: tps.map(tp => msg"Declared at" -> tp.toLoc))
            case _ =>
          }
          val dummyTargs2 = tparams.map(p =>
            TraitTag(Var(p.name))(originProv(p.toLoc, "method type parameter")))
          val targsMap2 = tparams.map(_.name).zip(dummyTargs2).toMap
          val reverseRigid2 = reverseRigid ++ dummyTargs2.map(t =>
            t -> freshVar(t.prov, S(t.id.idStr))(thisCtx.lvl + 1))
          if (!nme.name.head.isUpper)
            err(msg"Method names must start with a capital letter", nme.toLoc)
          if (defs.isDefinedAt(nme.name))
            err(msg"Method '${tn}.${nme.name}' is already defined.", nme.toLoc)
          val tp1s = td.tparams.map(tp => tp.name -> tp).toMap
          tparams.foreach(tp2 => tp1s.get(tp2.name) match {
            case S(tp1) => warn((msg"Method type parameter ${tp1}" -> tp1.toLoc)
              :: (msg"shadows class type parameter ${tp2}" -> tp2.toLoc)
              :: Nil)
            case N =>
          })
          val bodyTy = rhs.fold(
            term =>
              subst(typeLetRhs(rec, nme.name, term)(thisCtx, raise, targsMap ++ targsMap2), reverseRigid2),
            ty => PolymorphicType(thisCtx.lvl, subst(
              typeType(ty)(thisCtx.nextLevel, raise, targsMap ++ targsMap2),
              // ^ Note: we need to go to the next level here,
              //    which is also done automatically by `typeLetRhs` in the case above
              reverseRigid2))
          )
          rhs.fold(_ => defs, _ => decls) += nme.name -> (bodyTy match {
            case PolymorphicType(level, body) => PolymorphicType(level, ProvType(body)(prov))
          })
          thisCtx.env += "." + nme.name -> wrapMethod(tn.name, bodyTy)
        }
        val subsMap = getSubsMap(tn.name)
        newMthDecls += tn.name ->
          ((td.baseClasses.flatMap(t => newMthDecls.getOrElse(t.name, Map.empty).view.mapValues(subst(_, subsMap(t.name)))))
            .groupMapReduce(_._1)(_._2){ case PolymorphicType(_, body1) -> PolymorphicType(_, body2) => 
              PolymorphicType(thisCtx.lvl, ComposedType(false, body1, body2)(prov)) } ++ decls.toMap)
        newMthDefs += tn.name ->
          ((td.baseClasses.flatMap(t => newMthDefs.getOrElse(t.name, Map.empty).view.mapValues(subst(_, subsMap(t.name)))))
            .groupMapReduce(_._1)(_._2){ case PolymorphicType(_, body1) -> PolymorphicType(_, body2) => 
              PolymorphicType(thisCtx.lvl, ComposedType(false, body1, body2)(prov)) } ++ defs.toMap)
        allEnv ++= (newMthDefs(tn.name) ++ newMthDecls(tn.name)).flatMap{ case mn -> bodyTy => 
          val m_ty = wrapMethod(tn.name, bodyTy)
          s"${tn.name}.${mn}" -> m_ty ::
            (ctx.methodBase.get(mn) match {
              case S(S(v)) if ctx.allBaseClassesOf(tn.name).contains(v) => Nil
              case S(S(v)) if ctx.allBaseClassesOf(v.name.toList.mapHead(_.toUpper).mkString)
                  .contains(Var(tn.name.toList.mapHead(_.toLower).mkString)) =>
                ctx.methodBase += mn -> S(Var(tn.name.toList.mapHead(_.toLower).mkString))
                ("." + mn) -> m_ty :: Nil
              case S(S(v)) =>
                ctx.methodBase += mn -> N
                allEnv -= "." + mn
                Nil
              case S(N) => Nil
              case N =>
                ctx.methodBase += mn -> S(Var(tn.name.toList.mapHead(_.toLower).mkString))
                ("." + mn) -> m_ty :: Nil
            })
        }
      }
      ctx.copy(mthDecls = newMthDecls.toMap, mthDefs = newMthDefs.toMap).tap(checkSubsume(_))
    }
    /* Perform subsumption checking on method declarations and definitions
     * by applying type arguments to method signatures of the parents and rigidifying class type variables. */
    def checkSubsume(implicit ctx: Ctx): Unit = {
      newDefs.filter(td => ctx.tyDefs.isDefinedAt(td.nme.name)).foreach { td =>
        implicit val prov: TypeProvenance = tp(td.toLoc, "type definition")
        val tn = td.nme
        val decls = ctx.mthDecls(tn.name)
        val defs = ctx.mthDefs(tn.name)
        val rigidSubsMap = td.targsMap.map { 
          case s -> (tv: TypeVariable) => tv -> freshenAbove(ctx.lvl, tv, true)
          case _ => die
        }.toMap[SimpleType, SimpleType]
        val subsMap = getSubsMap(tn.name)
        def ss(mt: PolymorphicType, bmt: TypeScheme, bno: Option[Str] = N)(implicit raise: Raise, prov: TypeProvenance) = bmt match {
          case pt: PolymorphicType => constrain(subst(mt, rigidSubsMap).instantiate,
            subst(bno.fold(pt)(bn => subst(pt, subsMap(bn))), rigidSubsMap).rigidify)(raise, prov, ctx)
          case st: SimpleType => constrain(subst(mt, rigidSubsMap).instantiate,
            subst(bno.fold(st)(bn => subst(st, subsMap(bn))), rigidSubsMap))(raise, prov, ctx)
        }
        decls.foreach { case nme -> mt => 
          implicit val prov: TypeProvenance = mt.prov
          println(s">> Checking subsumption for declared type of $nme : $mt")
          td.baseClasses.foreach { case Var(bn) => ctx.mthDecls.get(bn).foreach(_.get(nme).foreach(ss(mt, _, S(bn)))) }
        }
        defs.foreach { case nme -> mt => 
          implicit val prov: TypeProvenance = mt.prov
          println(s">> Checking subsumption for inferred type of $nme : $mt")
          ctx.mthDecls.get(tn.name).foreach(_.get(nme).foreach(ss(mt, _)))
        }
        (td.mthDecls ++ td.mthDefs).foreach { case md @ MethodDef(rec, prt, nme, tparams, rhs) =>
          implicit val prov: TypeProvenance = tp(md.toLoc, rhs.fold(_ => "method definition", _ => "method declaration"))
          val mt = rhs.fold(_ => defs(nme.name), _ => decls(nme.name))
          td.baseClasses.foreach { case Var(bn) => 
            ctx.mthDefs.get(bn).foreach(_.get(nme.name).foreach { bmt =>
              if (!ctx.mthDecls.get(bn).exists(_.isDefinedAt(nme.name))) {
                err(msg"Overriding method ${bn}.${nme.name} without explicit declaration is not allowed.", md.toLoc)
                println(s">> Checking subsumption (against inferred type) for inferred type of $nme : $mt")
                ss(mt, bmt)
              }
            })
          }
        }
      }
    }
    typeMethods(typeTypeDefs(ctx.copy(env = allEnv, tyDefs = allDefs)))
  }
  // TODO better record type provenances!
  def typeType(ty: Type, simplify: Bool = true)(implicit ctx: Ctx, raise: Raise,
      vars: Map[Str, SimpleType] = Map.empty): SimpleType = {
    val typeType = ()
    def typeNamed(loc: Opt[Loc], name: Str): (() => ST) \/ TypeDef =
      ctx.tyDefs.get(name).toRight(() =>
        err("type identifier not found: " + name, loc)(raise, tp(loc, "missing type")))
    val localVars = mutable.Map.empty[TypeVar, TypeVariable]
    def rec(ty: Type)(implicit ctx: Ctx, recVars: Map[TypeVar, TypeVariable]): SimpleType = ty match {
      case Top => ExtrType(false)(tp(ty.toLoc, "top type"))
      case Bot => ExtrType(true)(tp(ty.toLoc, "bottom type"))
      case Bounds(lb, ub) => TypeBounds(rec(lb), rec(ub))(tp(ty.toLoc,
        if (lb === Bot && ub === Top) "type wildcard" else "type bounds"))
      case Tuple(fields) => TupleType(fields.map(f => f._1 -> rec(f._2)))(tp(ty.toLoc, "tuple type"))
      case Inter(lhs, rhs) => (if (simplify) rec(lhs) & (rec(rhs), _: TypeProvenance)
          else ComposedType(false, rec(lhs), rec(rhs)) _
        )(tp(ty.toLoc, "intersection type"))
      case Union(lhs, rhs) => (if (simplify) rec(lhs) | (rec(rhs), _: TypeProvenance)
          else ComposedType(true, rec(lhs), rec(rhs)) _
        )(tp(ty.toLoc, "union type"))
      case Neg(t) => NegType(rec(t))(tp(ty.toLoc, "type negation"))
      case Record(fs) => 
        val prov = tp(ty.toLoc, "record type")
        fs.groupMap(_._1.name)(_._1).foreach { case s -> fieldNames if fieldNames.size > 1 => err(
            msg"Multiple declarations of field name ${s} in ${prov.desc}" -> ty.toLoc
              :: fieldNames.map(tp => msg"Declared at" -> tp.toLoc))(raise, prov)
          case _ =>
        }
        RecordType.mk(fs.map { nt =>
          if (nt._1.name.head.isUpper)
            err(msg"Field identifiers must start with a small letter", nt._1.toLoc)(raise, prov)
          nt._1 -> rec(nt._2)
        })(prov)
      case Function(lhs, rhs) => FunctionType(rec(lhs), rec(rhs))(tp(ty.toLoc, "function type"))
      case WithExtension(b, r) => WithType(rec(b),
        RecordType(r.fields.mapValues(rec))(tp(r.toLoc, "extension record")))(tp(ty.toLoc, "extension type"))
      case Literal(lit) => ClassTag(lit, Set.single(lit.baseClass))(tp(ty.toLoc, "literal type"))
      case TypeName(name) =>
        val tyLoc = ty.toLoc
        val tpr = tp(tyLoc, "type reference")
        vars.get(name).getOrElse {
          typeNamed(tyLoc, name) match {
            case R(td) =>
              if (td.tparams.nonEmpty) {
                err(msg"Type $name takes parameters", tyLoc)(raise, tpr)
              } else TypeRef(td, Nil)(tpr, ctx)
            case L(e) =>
              if (name.isEmpty || !name.head.isLower) e()
              else typeNamed(tyLoc, name.capitalize) match {
                case R(td) => td.kind match {
                  case Cls => clsNameToNomTag(td)(tp(tyLoc, "class tag"), ctx)
                  case Trt => trtNameToNomTag(td)(tp(tyLoc, "trait tag"), ctx)
                  case Als => err(msg"Type alias $name cannot be used as a type tag", tyLoc)(raise, tpr)
                }
                case L(_) => e()
              }
          }
        }
      case tv: TypeVar =>
        // assert(ty.toLoc.isDefined)
        recVars.getOrElse(tv,
          localVars.getOrElseUpdate(tv, new TypeVariable(ctx.lvl, Nil, Nil, tv.identifier.toOption)(noProv))
            .withProv(tp(ty.toLoc, "type variable")))
      case AppliedType(base, targs) =>
        val prov = tp(ty.toLoc, "applied type reference")
        typeNamed(ty.toLoc, base.name) match {
          case R(td) =>
            val tpnum = td.tparams.size
            val realTargs = if (targs.size === tpnum) targs.map(rec) else {
              err(msg"Wrong number of type arguments – expected ${tpnum.toString}, found ${
                  targs.size.toString}", ty.toLoc)(raise, prov)
              (targs.iterator.map(rec) ++ Iterator.continually(freshVar(noProv))).take(tpnum).toList
            }
            TypeRef(td, realTargs)(prov, ctx)
          case L(e) => e()
        }
      case Recursive(uv, body) =>
        val tv = freshVar(tp(ty.toLoc, "local type binding"), uv.identifier.toOption)
        val bod = rec(body)(ctx, recVars + (uv -> tv))
        tv.upperBounds ::= bod
        tv.lowerBounds ::= bod
        tv
      case Rem(base, fs) => Without(rec(base), fs
        .toSet)(tp(ty.toLoc, "function type")) // TODO use ty's prov
    }
    rec(ty)(ctx, Map.empty)
  }
  
  def typePattern(pat: Term)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType] = Map.empty): SimpleType =
    typeTerm(pat)(ctx.copy(inPattern = true), raise, vars)
  
  
  def typeStatement(s: DesugaredStatement, allowPure: Bool)
        (implicit ctx: Ctx, raise: Raise): PolymorphicType \/ Ls[Binding] = s match {
    case Def(isrec, nme, L(rhs)) => // TODO reject R(..)
      val ty_sch = typeLetRhs(isrec, nme, rhs)
      ctx += nme -> ty_sch
      R(nme -> ty_sch :: Nil)
    case t @ Tup(fs) if !allowPure => // Note: not sure this is still used!
      val thing = fs match {
        case (S(_), _) :: Nil => "field"
        case Nil => "empty tuple"
        case _ => "tuple"
      }
      warn(s"Useless $thing in statement position.", t.toLoc)
      L(PolymorphicType(0, typeTerm(t)))
    case t: Term =>
      val ty = typeTerm(t)
      if (!allowPure) {
        if (t.isInstanceOf[Var] || t.isInstanceOf[Lit])
          warn("Pure expression does nothing in statement position.", t.toLoc)
        else
          constrain(mkProxy(ty, TypeProvenance(t.toCoveringLoc, "expression in statement position")), UnitType)(
            raise = err => raise(Warning( // Demote constraint errors from this to warnings
              msg"Expression in statement position should have type `unit`." -> N ::
              msg"Use the `discard` function to discard non-unit values, making the intent clearer." -> N ::
              err.allMsgs)),
            prov = TypeProvenance(t.toLoc, t.describe), ctx)
      }
      L(PolymorphicType(0, ty))
    case _ =>
      err(msg"Illegal position for this ${s.describe} statement.", s.toLoc)(raise, noProv)
      R(Nil)
  }
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: Str, rhs: Term)(implicit ctx: Ctx, raise: Raise,
      vars: Map[Str, SimpleType] = Map.empty): PolymorphicType = {
    val res = if (isrec) {
      val e_ty = freshVar(TypeProvenance(rhs.toLoc, "let-bound value"))(lvl + 1)
      ctx += nme -> e_ty
      val ty = typeTerm(rhs)(ctx.nextLevel, raise, vars)
      constrain(ty, e_ty)(raise, TypeProvenance(rhs.toLoc, "binding of " + rhs.describe), ctx)
      e_ty
    } else typeTerm(rhs)(ctx.nextLevel, raise, vars)
    PolymorphicType(lvl, res)
  }
  
  def mkProxy(ty: SimpleType, prov: TypeProvenance): SimpleType = {
    ProvType(ty)(prov)
    // TODO switch to return this in perf mode:
    // ty
  }
  
  // TODO also prevent rebinding of "not"
  val reservedNames: Set[Str] = Set("|", "&", "~", ",", "neg", "and", "or")
  
  object ValidVar {
    def unapply(v: Var)(implicit raise: Raise): S[Str] = S {
      if (reservedNames(v.name))
        err(s"Illegal use of ${if (v.name.head.isLetter) "keyword" else "operator"}: " + v.name,
          v.toLoc)(raise, ttp(v))
      v.name
    }
  }
  object ValidPatVar {
    def unapply(v: Var)(implicit ctx: Ctx, raise: Raise): Opt[Str] =
      if (ctx.inPattern && v.isPatVar) {
        ctx.parent.dlof(_.get(v.name))(N).map(_.instantiate(0).unwrapProxies) |>? {
          case S(ClassTag(Var(v.name), _)) =>
            warn(msg"Variable name '${v.name}' already names a symbol in scope. " +
              s"If you want to refer to that symbol, you can use `scope.${v.name}`; " +
              s"if not, give your future readers a break and use another name :^)", v.toLoc)
        }
        ValidVar.unapply(v)
      } else N
  }
  
  /** Infer the type of a term. */
  def typeTerm(term: Term)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType] = Map.empty): SimpleType
        = trace(s"$lvl. Typing ${if (ctx.inPattern) "pattern" else "term"} $term") {
    implicit val prov: TypeProvenance = ttp(term)
    
    def con(lhs: SimpleType, rhs: SimpleType, res: SimpleType): SimpleType = {
      var alreadyReportedAnError = false
      constrain(lhs, rhs)({
        case err: TypeError if alreadyReportedAnError => () // silence further errors from this location
        case err: TypeError =>
          alreadyReportedAnError = true
          constrain(errType, res)(_ => (), noProv, ctx) // This is just to get error types leak into the result
          raise(err)
        case diag => raise(diag)
      }, prov, ctx)
      res
    }
    term match {
      case v @ Var("_") => // TODO parse this differently... or handle consistently everywhere
        freshVar(tp(v.toLoc, "wildcard"))
      case Asc(trm, ty) =>
        val trm_ty = typeTerm(trm)
        val ty_ty = typeType(ty)(ctx.copy(inPattern = false), raise, vars)
        con(trm_ty, ty_ty, ty_ty)
        if (ctx.inPattern)
          con(ty_ty, trm_ty, ty_ty) // In patterns, we actually _unify_ the pattern and ascribed type 
        else ty_ty
      case (v @ ValidPatVar(nme)) =>
        val prov = tp(if (verboseConstraintProvenanceHints) v.toLoc else N, "variable")
        ctx.env.get(nme).map(_.instantiate) // Note: only look at ctx.env, and not the outer ones!
          .getOrElse(new TypeVariable(lvl, Nil, Nil)(prov).tap(ctx += nme -> _))
      case v @ ValidVar(name) =>
        val ty = ctx.get(name).getOrElse {
          // TODO: delay type expansion to message display and show the expected type here!
          (ctx.tyDefs.get(name), ctx.mthDecls.get(name).map(_ -- ctx.mthDefs(name).keys)) match {
            case (S(td), S(abstMths)) if abstMths.nonEmpty => err(
              (msg"Instantiation of an abstract type is forbidden" -> term.toLoc)
              :: (msg"Note that ${td.kind.str} ${td.nme} is abstract:" -> td.toLoc)
              :: abstMths.map { case mn -> mthTy => msg"Hint: method $mn is abstract" -> mthTy.prov.loco }.toList)
            case _ => err("identifier not found: " + name, term.toLoc)
          }
        }.instantiate
        mkProxy(ty, prov)
        // ^ TODO maybe use a description passed in param?
        // currently we get things like "flows into variable reference"
        // but we used to get the better "flows into object receiver" or "flows into applied expression"...
      case lit: Lit => ClassTag(lit, Set.single(lit.baseClass))(prov)
      case App(Var("neg" | "~"), trm) => typeTerm(trm).neg(prov)
      case App(App(Var("|"), lhs), rhs) =>
        typeTerm(lhs) | (typeTerm(rhs), prov)
      case App(App(Var("&"), lhs), rhs) =>
        typeTerm(lhs) & (typeTerm(rhs), prov)
      case Rcd(fs) => // TODO rm: no longer used?
        val prov = tp(term.toLoc, "record literal")
        fs.groupMap(_._1.name)(_._1).foreach { case s -> fieldNames if fieldNames.size > 1 => err(
            msg"Multiple declarations of field name ${s} in ${prov.desc}" -> term.toLoc
              :: fieldNames.map(tp => msg"Declared at" -> tp.toLoc))(raise, prov)
          case _ =>
        }
        RecordType.mk(fs.map { case (n, t) => 
          if (n.name.head.isUpper)
            err(msg"Field identifiers must start with a small letter", term.toLoc)(raise, prov)
          (n, typeTerm(t))
        })(prov)
      case tup: Tup =>
        typeTerms(tup :: Nil, false, Nil)
      case Bra(false, trm: Blk) => typeTerm(trm)
      case Bra(rcd, trm @ (_: Tup | _: Blk)) => typeTerms(trm :: Nil, rcd, Nil)
      case Bra(_, trm) => typeTerm(trm)
      case Blk((s: Term) :: Nil) => typeTerm(s)
      case Blk(Nil) => UnitType
      case pat if ctx.inPattern =>
        err(msg"Unsupported pattern shape${
          if (dbg) " ("+pat.getClass.toString+")" else ""}:", pat.toLoc)(raise, ttp(pat))
      case Lam(pat, body) =>
        val newBindings = mutable.Map.empty[Str, TypeVariable]
        val newCtx = ctx.nest
        val param_ty = typePattern(pat)(newCtx, raise, vars)
        newCtx ++= newBindings
        val body_ty = typeTerm(body)(newCtx, raise, vars)
        FunctionType(param_ty, body_ty)(tp(term.toLoc, "function"))
      case App(App(Var("and"), lhs), rhs) =>
        val lhs_ty = typeTerm(lhs)
        val newCtx = ctx.nest // TODO use
        val rhs_ty = typeTerm(lhs)
        ??? // TODO
      case App(f, a) =>
        val f_ty = typeTerm(f)
        val a_ty = typeTerm(a)
        val res = freshVar(prov)
        val arg_ty = mkProxy(a_ty, tp(a.toCoveringLoc, "argument"))
        val appProv = tp(f.toCoveringLoc, "applied expression")
        val fun_ty = mkProxy(f_ty, appProv)
        val resTy = con(fun_ty, FunctionType(arg_ty, res)(prov), res)
        val raw_fun_ty = fun_ty.unwrapProxies
        resTy
      case Sel(obj, fieldName) =>
        def rcdSel(obj: Term, fieldName: Var) = {
          val o_ty = typeTerm(obj)
          val res = freshVar(prov)
          val obj_ty = mkProxy(o_ty, tp(obj.toCoveringLoc, "receiver"))
          con(obj_ty, RecordType.mk((fieldName, res) :: Nil)(prov), res)
        }
        def mthCall(obj: Term, fieldName: Var) =
          ctx.get(if (fieldName.name.contains('.')) fieldName.name else "." + fieldName.name) match {
            case S(mth_ty) => 
              val o_ty = typeTerm(obj)
              val res = freshVar(prov)
              con(mth_ty.instantiate, FunctionType(o_ty, res)(prov), res)
            case N =>
              if (fieldName.name.isCapitalized) {
                if (ctx.methodBase.isDefinedAt(fieldName.name))
                  err(msg"Implicit call to method ${fieldName.name} is forbidden because it is ambiguous." -> term.toLoc ::
                    msg"Unrelated methods named ${fieldName.name} are defined by:" -> N ::
                    ctx.tyDefs.valuesIterator.filter(td => (td.mthDecls ++ td.mthDefs).exists(_.nme.name === fieldName.name))
                      .map { td => msg"• ${td.kind.str} ${td.nme}" -> td.nme.toLoc }.toList)
                else err(msg"Method ${fieldName.name} not found", term.toLoc)
              } else rcdSel(obj, fieldName)
          }
        obj match {
          case Var(name) if name.isCapitalized && ctx.tyDefs.isDefinedAt(name) =>
            ctx.get(s"${name}.${fieldName.name}") match {
              case S(mth_ty) => mth_ty.instantiate
              case N =>
                err(msg"Class ${name} has no method ${fieldName.name}", term.toLoc)
                mthCall(obj, fieldName)
            }
          case _ => mthCall(obj, fieldName)
        }
      case Let(isrec, nme, rhs, bod) =>
        val n_ty = typeLetRhs(isrec, nme, rhs)
        val newCtx = ctx.nest
        newCtx += nme -> n_ty
        typeTerm(bod)(newCtx, raise)
      // case Blk(s :: stmts) =>
      //   val (newCtx, ty) = typeStatement(s)
      //   typeTerm(Blk(stmts))(newCtx, lvl, raise)
      case Blk(stmts) => typeTerms(stmts, false, Nil)(ctx.nest, raise, prov)
      case Bind(l, r) =>
        val l_ty = typeTerm(l)
        val newCtx = ctx.nest // so the pattern's context don't merge with the outer context!
        val r_ty = typePattern(r)(newCtx, raise)
        ctx ++= newCtx.env
        con(l_ty, r_ty, r_ty)
      case Test(l, r) =>
        val l_ty = typeTerm(l)
        val newCtx = ctx.nest
        val r_ty = typePattern(r)(newCtx, raise) // TODO make these bindings flow
        con(l_ty, r_ty, TopType)
        BoolType
      case With(t, rcd) =>
        val t_ty = typeTerm(t)
        val rcd_ty = typeTerm(rcd)
        (t_ty without rcd.fields.iterator.map(_._1).toSet) & (rcd_ty, prov)
      case CaseOf(s, cs) =>
        val s_ty = typeTerm(s)
        val (tys, cs_ty) = typeArms(s |>? {
          case v: Var => v
          case Asc(v: Var, _) => v
        }, cs)
        val req = tys.foldRight(BotType: SimpleType) {
          case ((a_ty, tv), req) => a_ty & tv | req & a_ty.neg()
        }
        con(s_ty, req, cs_ty)
    }
  }(r => s"$lvl. : ${r}")
  
  def typeArms(scrutVar: Opt[Var], arms: CaseBranches)
      (implicit ctx: Ctx, raise: Raise, lvl: Int)
      : Ls[SimpleType -> SimpleType] -> SimpleType = arms match {
    case NoCases => Nil -> BotType
    case Wildcard(b) =>
      val fv = freshVar(tp(arms.toLoc, "wildcard pattern"))
      val newCtx = ctx.nest
      scrutVar match {
        case Some(v) =>
          newCtx += v.name -> fv
          val b_ty = typeTerm(b)(newCtx, raise)
          (fv -> TopType :: Nil) -> b_ty
        case _ =>
          (fv -> TopType :: Nil) -> typeTerm(b)
      }
    case Case(pat, bod, rest) =>
      val patTy = pat match {
        case lit: Lit =>
          ClassTag(lit, Set.single(lit.baseClass))(tp(pat.toLoc, "literal pattern"))
        case Var(nme) =>
          val tpr = tp(pat.toLoc, "type pattern")
          ctx.tyDefs.get(nme) match {
            case None =>
              err("type identifier not found: " + nme, pat.toLoc)(raise, tpr)
              val e = ClassTag(ErrTypeId, Set.empty)(tpr)
              return ((e -> e) :: Nil) -> e
            case Some(td) =>
              td.kind match {
                case Als => err(msg"can only match on classes and traits", pat.toLoc)(raise, tpr)
                case Cls => clsNameToNomTag(td)(tp(pat.toLoc, "class pattern"), ctx)
                case Trt => trtNameToNomTag(td)(tp(pat.toLoc, "trait pattern"), ctx)
              }
          }
      }
      val newCtx = ctx.nest
      val (req_ty, bod_ty, (tys, rest_ty)) = scrutVar match {
        case S(v) =>
          val tv = freshVar(tp(v.toLoc, "refined scrutinee"))
          newCtx += v.name -> tv
          val bod_ty = typeTerm(bod)(newCtx, raise)
          (patTy -> tv, bod_ty, typeArms(scrutVar, rest))
        case N =>
          val bod_ty = typeTerm(bod)(newCtx, raise)
          (patTy -> TopType, bod_ty, typeArms(scrutVar, rest))
      }
      (req_ty :: tys) -> (bod_ty | rest_ty)
  }
  
  def typeTerms(term: Ls[Statement], rcd: Bool, fields: List[Opt[Var] -> SimpleType])
        (implicit ctx: Ctx, raise: Raise, prov: TypeProvenance): SimpleType
      = term match {
    case (trm @ Var(nme)) :: sts if rcd => // field punning
      typeTerms(Tup(S(trm) -> trm :: Nil) :: sts, rcd, fields)
    case Blk(sts0) :: sts1 => typeTerms(sts0 ::: sts1, rcd, fields)
    case Tup(Nil) :: sts => typeTerms(sts, rcd, fields)
    case Tup((no, trm) :: ofs) :: sts =>
      val ty = {
        trm match  {
          case Bra(false, t) if ctx.inPattern => // we use syntax `(x: (p))` to type `p` as a pattern and not a type...
            typePattern(t)
          case _ => ctx.copy(inPattern = ctx.inPattern && no.isEmpty) |> { implicit ctx => // TODO change this?
            if (ofs.isEmpty) typeTerm(Bra(rcd, trm))
            // ^ This is to type { a: ... } as { a: { ... } } to facilitate object literal definitions;
            //   not sure that's a good idea...
            else typeTerm(trm)
          }
        }
      }
      val res_ty = no |> {
        case S(nme) if ctx.inPattern =>
          // TODO in 'opaque' definitions we should give the exact specified type and not something more precise
          // as in `(x: Int) => ...` should not try to refine the type of `x` further
          
          val prov = tp(trm.toLoc, "parameter type")
          val t_ty =
            // TODO in positive position, this should create a new VarType instead! (i.e., an existential)
            new TypeVariable(lvl, Nil, Nil)(prov)//.tap(ctx += nme -> _)
          
          // constrain(ty, t_ty)(raise, prov)
          constrain(t_ty, ty)(raise, prov, ctx)
          ctx += nme.name -> t_ty
          
          t_ty
          // ty
          // ComposedType(false, t_ty, ty)(prov)
          // ComposedType(true, t_ty, ty)(prov) // loops!
          
        case S(nme) =>
          ctx += nme.name -> ty
          ty
        case _ =>
          ty
      }
      typeTerms(Tup(ofs) :: sts, rcd, (no, res_ty) :: fields)
    case (trm: Term) :: Nil =>
      if (fields.nonEmpty)
        warn("Previous field definitions are discarded by this returned expression.", trm.toLoc)
      typeTerm(trm)
    // case (trm: Term) :: Nil =>
    //   assert(!rcd)
    //   val ty = typeTerm(trm)
    //   typeBra(Nil, rcd, (N, ty) :: fields)
    case s :: sts =>
      val (diags, desug) = s.desugared
      diags.foreach(raise)
      val newBindings = desug.flatMap(typeStatement(_, allowPure = false).toOption)
      ctx ++= newBindings.flatten
      typeTerms(sts, rcd, fields)
    case Nil =>
      if (rcd) {
        val fs = fields.reverseIterator.zipWithIndex.map {
          case ((S(n), t), i) =>
            n -> t
          case ((N, t), i) =>
            // err("Missing name for record field", t.prov.loco)
            warn("Missing name for record field", t.prov.loco)
            (Var("_" + (i + 1)), t)
        }.toList
        RecordType.mk(fs)(prov)
      } else TupleType(fields.reverse)(prov)
  }
  
  
  /** Convert an inferred SimpleType into the immutable Type representation. */
  def expandType(st: SimpleType, polarity: Bool, stopAtTyVars: Bool = false): Type = {
    val expandType = ()
    
    // TODO improve/simplify? (take inspiration from other impls?)
    //    see: duplication of recursive.get(st_pol) logic
    
    val recursive = mutable.Map.empty[SimpleType -> Bool, TypeVar]
    def go(st: SimpleType, polarity: Boolean)(implicit inProcess: Set[SimpleType -> Bool]): Type = {
      val st_pol = st -> polarity
      if (inProcess(st_pol)) recursive.getOrElseUpdate(st_pol, freshVar(st.prov, st |>?? {
        case tv: TypeVariable => tv.nameHint
      })(0).asTypeVar)
      else (inProcess + st_pol) pipe { implicit inProcess => st match {
        case tv: TypeVariable if stopAtTyVars => tv.asTypeVar
        case tv: TypeVariable =>
          val bounds = if (polarity) tv.lowerBounds else tv.upperBounds
          val bound =
            if (polarity) bounds.foldLeft(BotType: SimpleType)(_ | _)
            else bounds.foldLeft(TopType: SimpleType)(_ & _)
          if (inProcess(bound -> polarity))
            recursive.getOrElseUpdate(bound -> polarity, freshVar(st.prov, tv.nameHint)(0).asTypeVar)
          else {
            val boundTypes = bounds.map(go(_, polarity))
            val mrg = if (polarity) Union else Inter
            recursive.get(st_pol) match {
              case Some(variable) =>
                Recursive(variable, boundTypes.reduceOption(mrg).getOrElse(if (polarity) Bot else Top))
              case None => boundTypes.foldLeft[Type](tv.asTypeVar)(mrg)
            }
          }
        case _ =>
          val res = st match {
            case FunctionType(l, r) => Function(go(l, !polarity), go(r, polarity))
            case ComposedType(true, l, r) => Union(go(l, polarity), go(r, polarity))
            case ComposedType(false, l, r) => Inter(go(l, polarity), go(r, polarity))
            case RecordType(fs) => Record(fs.map(nt => nt._1 -> go(nt._2, polarity)))
            case TupleType(fs) => Tuple(fs.map(nt => nt._1 -> go(nt._2, polarity)))
            case NegType(t) => Neg(go(t, !polarity))
            case ExtrType(true) => Bot
            case ExtrType(false) => Top
            case WithType(base, rcd) => WithExtension(go(base, polarity),
              Record(rcd.fields.mapValues(go(_, polarity))))
            case ProxyType(und) => go(und, polarity)
            case tag: ObjectTag => tag.id match {
              case Var(n) => TypeName(n)
              case lit: Lit => Literal(lit)
            }
            case TypeRef(td, Nil) => TypeName(td.nme.name)
            case TypeRef(td, targs) =>
              AppliedType(TypeName(td.nme.name), targs.map { t =>
                val l = go(t, false)
                val u = go(t, true)
                if (l === u) l else Bounds(l, u)
              })
            case TypeBounds(lb, ub) => if (polarity) go(ub, true) else go(lb, false)
            case Without(base, names) => Rem(go(base, polarity), names.toList)
            case _: TypeVariable => die
          }
          recursive.get(st_pol) match {
            case Some(variable) =>
              Recursive(variable, res)
            case None => res
          }
      }
    }}
    
    go(st, polarity)(Set.empty)
  }
  
}
