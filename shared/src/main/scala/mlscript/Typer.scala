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
  
  def funkyTuples: Bool = false
  
  type Raise = Diagnostic => Unit
  type Binding = Str -> TypeScheme
  type Bindings = Map[Str, TypeScheme]

  case class TypeDef(
    kind: TypeDefKind,
    nme: TypeName,
    tparamsargs: List[(TypeName, TypeVariable)],
    tvars: Iterable[TypeVariable], // "implicit" type variables. instantiate every time a `TypeRef` is expanded
    bodyTy: SimpleType,
    mthDecls: List[MethodDef[Right[Term, Type]]],
    mthDefs: List[MethodDef[Left[Term, Type]]],
    baseClasses: Set[Var],
    toLoc: Opt[Loc],
  ) {
    def allBaseClasses(ctx: Ctx)(implicit traversed: Set[Var]): Set[Var] =
      baseClasses.map(v => Var(v.name.decapitalize)) ++
        baseClasses.iterator.filterNot(traversed).flatMap(v =>
          ctx.tyDefs.get(v.name).fold(Set.empty[Var])(_.allBaseClasses(ctx)(traversed + v)))
    val tparams: List[TypeName] = tparamsargs.map(_._1)
    val targs: List[TypeVariable] = tparamsargs.map(_._2)
    def thisTy(implicit prov: TypeProvenance): TypeRef = TypeRef(nme, targs)(prov)
    def wrapMethod(bodyTy: PolymorphicType)(implicit prov: TypeProvenance): MethodType =
      MethodType(bodyTy.level, FunctionType(singleTup(thisTy), bodyTy.body)(prov), nme)
  }

  private case class MethodDefs(
    tn: TypeName,
    prts: List[MethodDefs],
    decls: Map[Str, MethodType],
    defns: Map[Str, MethodType],
  ) {
    private def &(that: MethodDefs, tn: TypeName)(newdefns: Set[Str])(implicit raise: Raise): MethodDefs =
      MethodDefs(
        tn,
        this.prts ::: that.prts,
        mergeMap(this.decls, that.decls)(_.&(_, tn)(TypeProvenance(tn.toLoc, "inherited method declaration"))),
        (this.defns.iterator ++ that.defns.iterator).toSeq.groupMap(_._1)(_._2).flatMap {
          case _ -> Nil => die
          case mn -> (defn :: Nil) => S(mn -> defn)
          case mn -> defns if newdefns(mn) => N
          case mn -> defns =>
            implicit val prov: TypeProvenance = TypeProvenance(tn.toLoc, "inherited method declaration")
            S(mn -> MethodType(defns.head.level,
              err(msg"A method definition must be given when inheriting multiple method definitions" -> tn.toLoc
                :: msg"Definitions of method $mn inherited from:" -> N
                :: defns.iterator.map(mt => msg"• ${mt.prts.head}" -> mt.prov.loco).toList),
              tn :: Nil
            ))
        }
      )
    private def ++(that: MethodDefs): MethodDefs = {
      require(prts.isEmpty)
      MethodDefs(
        that.tn,
        that.prts,
        this.decls ++ that.decls,
        this.defns ++ that.defns
      )
    }
    def propagate(top: Bool)(implicit raise: Raise): MethodDefs =
      prts.map(_.propagate(false)).reduceOption(_.&(_, tn)(defns.keySet))
        .foldRight(if (top) copy(prts = Nil, decls = Map.empty, defns = Map.empty) else copy(prts = Nil))(_ ++ _)
  }
  
  case class Ctx(parent: Opt[Ctx], env: MutMap[Str, TypeScheme], mthenv: MutMap[Str, MethodType],
      lvl: Int, inPattern: Bool, tyDefs: Map[Str, TypeDef]) {
    def +=(b: Binding): Unit = env += b
    def ++=(bs: IterableOnce[Binding]): Unit = bs.iterator.foreach(+=)
    def get(name: Str): Opt[TypeScheme] = env.get(name) orElse parent.dlof(_.get(name))(N)
    def getmth(name: Str): Opt[MethodType] = mthenv.get(name) orElse parent.dlof(_.getmth(name))(N)
    def contains(name: Str): Bool = env.contains(name) || parent.exists(_.contains(name))
    def containsmth(name: Str): Bool = mthenv.contains(name) || parent.exists(_.containsmth(name))
    def nest: Ctx = copy(Some(this), MutMap.empty, MutMap.empty)
    def nextLevel: Ctx = copy(lvl = lvl + 1)
    private val abcCache: MutMap[Str, Set[Var]] = MutMap.empty
    def allBaseClassesOf(name: Str): Set[Var] = abcCache.getOrElseUpdate(name,
      tyDefs.get(name).fold(Set.empty[Var])(_.allBaseClasses(this)(Set.empty)))
  }
  object Ctx {
    def init: Ctx = Ctx(
      parent = N,
      env = MutMap.from(builtinBindings),
      mthenv = MutMap.empty,
      lvl = 0,
      inPattern = false,
      tyDefs = Map.from(builtinTypes.map(t => t.nme.name -> t)),
    )
    val empty: Ctx = init
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
    TypeDef(Cls, TypeName("int"), Nil, Nil, TopType, Nil, Nil, Set.single(Var("number")), N) ::
    TypeDef(Cls, TypeName("number"), Nil, Nil, TopType, Nil, Nil, Set.empty, N) ::
    TypeDef(Cls, TypeName("bool"), Nil, Nil, TopType, Nil, Nil, Set.empty, N) ::
    TypeDef(Cls, TypeName("true"), Nil, Nil, TopType, Nil, Nil, Set.single(Var("bool")), N) ::
    TypeDef(Cls, TypeName("false"), Nil, Nil, TopType, Nil, Nil, Set.single(Var("bool")), N) ::
    TypeDef(Cls, TypeName("string"), Nil, Nil, TopType, Nil, Nil, Set.empty, N) ::
    TypeDef(Als, TypeName("anything"), Nil, Nil, TopType, Nil, Nil, Set.empty, N) ::
    TypeDef(Als, TypeName("nothing"), Nil, Nil, BotType, Nil, Nil, Set.empty, N) ::
    TypeDef(Cls, TypeName("error"), Nil, Nil, TopType, Nil, Nil, Set.empty, N) ::
    TypeDef(Cls, TypeName("unit"), Nil, Nil, TopType, Nil, Nil, Set.empty, N) ::
    Nil
  val primitiveTypes: Set[Str] =
    builtinTypes.iterator.filter(_.kind is Cls).map(_.nme.name).toSet
  def singleTup(ty: ST): ST =
    if (funkyTuples) ty else TupleType((N, ty) :: Nil)(noProv)
  val builtinBindings: Bindings = {
    val tv = freshVar(noProv)(1)
    import FunctionType.{ apply => fun }
    val intBinOpTy = fun(singleTup(IntType), fun(singleTup(IntType), IntType)(noProv))(noProv)
    val intBinPred = fun(singleTup(IntType), fun(singleTup(IntType), BoolType)(noProv))(noProv)
    Map(
      "true" -> TrueType,
      "false" -> FalseType,
      "document" -> BotType,
      "window" -> BotType,
      "not" -> fun(singleTup(BoolType), BoolType)(noProv),
      "succ" -> fun(singleTup(IntType), IntType)(noProv),
      "log" -> PolymorphicType(0, fun(singleTup(tv), UnitType)(noProv)),
      "discard" -> PolymorphicType(0, fun(singleTup(tv), UnitType)(noProv)),
      "negate" -> fun(singleTup(IntType), IntType)(noProv),
      "add" -> intBinOpTy,
      "sub" -> intBinOpTy,
      "mul" -> intBinOpTy,
      "div" -> intBinOpTy,
      "sqrt" -> fun(singleTup(IntType), IntType)(noProv),
      "lt" -> intBinPred,
      "le" -> intBinPred,
      "gt" -> intBinPred,
      "ge" -> intBinPred,
      "concat" -> fun(singleTup(StrType), fun(singleTup(StrType), StrType)(noProv))(noProv),
      "eq" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(singleTup(v), fun(singleTup(v), BoolType)(noProv))(noProv))
      },
      "ne" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(singleTup(v), fun(singleTup(v), BoolType)(noProv))(noProv))
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
      "&&" -> fun(singleTup(BoolType), fun(singleTup(BoolType), BoolType)(noProv))(noProv),
      "||" -> fun(singleTup(BoolType), fun(singleTup(BoolType), BoolType)(noProv))(noProv),
      "id" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(singleTup(v), v)(noProv))
      },
      "if" -> {
        val v = freshVar(noProv)(1)
        // PolymorphicType(0, fun(singleTup(BoolType), fun(singleTup(v), fun(singleTup(v), v)(noProv))(noProv))(noProv))
        PolymorphicType(0, fun(BoolType, fun(v, fun(v, v)(noProv))(noProv))(noProv))
      },
    ) ++ primTypes ++ primTypes.map(p => "" + p._1.capitalize -> p._2) // TODO settle on naming convention...
  }
  
  def tparamField(clsNme: TypeName, tparamNme: TypeName): Var =
    Var(clsNme.name + "#" + tparamNme.name)
  
  def clsNameToNomTag(tn: Str)(prov: TypeProvenance, ctx: Ctx): SimpleType = ctx.tyDefs.get(tn) match {
    case S(td) =>
      require(td.kind is Cls)
      ClassTag(Var(td.nme.name.decapitalize),
        ctx.allBaseClassesOf(td.nme.name))(prov)
    case N => errType(prov)
  }
  def trtNameToNomTag(tn: Str)(prov: TypeProvenance, ctx: Ctx): SimpleType = ctx.tyDefs.get(tn) match {
    case S(td) =>
      require(td.kind is Trt)
      TraitTag(Var(td.nme.name.decapitalize))(prov)
    case N => errType(prov)
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
  def targsAppOf(tn: Str)(implicit ctx: Ctx): Map[Str, Map[Str, SimpleType]] = {
    def rec(ty: SimpleType): Map[Str, Map[Str, SimpleType]] = ty match {
      case ComposedType(false, l, r) => rec(l) ++ rec(r)
      case TypeRef(bn, ts) => ctx.tyDefs.get(bn.name).fold(Map(bn.name -> Map.empty[Str, SimpleType])) {
        td => Map(bn.name -> td.tparams.iterator.map(_.name).zip(ts).toMap)
      }
      case RecordType(_) => Map.empty
      case _: ObjectTag => Map.empty
      case _ => Map.empty
    }
    ctx.tyDefs.get(tn) match { 
      case S(td) => rec(td.bodyTy)
      case N => Map.empty
    }
  }

  
  /** Only supports getting the fields of a valid base class type.
   * Notably, does not traverse type variables. */
  def fieldsOf(ty: SimpleType, paramTags: Bool)(implicit ctx: Ctx): Map[Var, ST] =
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
    var allMthEnv = ctx.mthenv.clone
    val newDefsInfo = newDefs0.iterator.map { case td => td.nme.name -> (td.kind, td.tparams.size) }.toMap
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
      val tparamsargs = td.tparams.lazyZip(dummyTargs)
      val (bodyTy, tvars) = 
        typeType2(td.body, simplify = false)(ctx.nextLevel, raise, tparamsargs.map(_.name -> _).toMap, newDefsInfo)
      val td1 = TypeDef(td.kind, td.nme, tparamsargs.toList, tvars, bodyTy,
        td.mthDecls, td.mthDefs, baseClassesOf(td), td.toLoc)
      allDefs += n.name -> td1
      td1
    }
    import ctx.{tyDefs => oldDefs}
    /* Type the bodies of type definitions, ensuring the correctness of parent types
     * and the regularity of the definitions, then register the constructors and types in the context. */
    def typeTypeDefs(implicit ctx: Ctx): Ctx =
      ctx.copy(tyDefs = oldDefs ++ newDefs.flatMap { td =>
        implicit val prov: TypeProvenance = tp(td.toLoc, "type definition")
        val n = td.nme
        def gatherMthNames(td: TypeDef): (Set[TypeName], Set[TypeName]) =
          td.baseClasses.iterator.flatMap(bn => ctx.tyDefs.get(bn.name)).map(gatherMthNames(_)).fold(
            (td.mthDecls.iterator.map(md => md.nme.copy().withLocOf(md)).toSet,
            td.mthDefs.iterator.map(md => md.nme.copy().withLocOf(md)).toSet)
          ) { case ((decls1, defns1), (decls2, defns2)) => (
            (decls1.toSeq ++ decls2.toSeq).groupMapReduce(identity)(identity)((mn, _) =>
              TypeName(mn.name).withLoc(td.toLoc)).valuesIterator.toSet, defns1 ++ defns2
          )}
        def checkCycle(ty: SimpleType)(implicit travsersed: Set[TypeName \/ TV]): Bool =
            // trace(s"Cycle? $ty {${travsersed.mkString(",")}}") {
            ty match {
          case TypeRef(tn, _) if travsersed(L(tn)) =>
            err(msg"illegal cycle involving type ${tn}", prov.loco)
            false
          case tr @ TypeRef(tn, targs) => checkCycle(tr.expand)(travsersed + L(tn))
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
          case Als => checkCycle(td.bodyTy)(Set.single(L(td.nme)))
          case k: ObjDefKind =>
            val parentsClasses = MutSet.empty[TypeRef]
            def checkParents(ty: SimpleType): Bool = ty match {
              // case ClassTag(Var("string"), _) => true // Q: always?
              case _: ObjectTag => true // Q: always? // FIXME actually no
              case tr @ TypeRef(tn2, _) =>
                val td2 = ctx.tyDefs(tn2.name)
                td2.kind match {
                  case Cls =>
                    if (td.kind is Cls) {
                      parentsClasses.isEmpty || {
                        err(msg"${td.kind.str} $n cannot inherit from class ${tn2
                            } as it already inherits from class ${parentsClasses.head.defn}",
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
            lazy val checkAbstract = {
              val (decls, defns) = gatherMthNames(td)
              (decls -- defns) match {
                case absMths if absMths.nonEmpty =>
                  if (ctx.get(n.name).isEmpty) ctx += n.name -> AbstractConstructor(absMths)
                case _ =>
                  val fields = fieldsOf(td.bodyTy, true)
                  val tparamTags = td.tparamsargs.map { case (tp, tv) =>
                    tparamField(td.nme, tp) -> FunctionType(tv, tv)(noProv) }
                  val ctor = k match {
                    case Cls =>
                      val nomTag = clsNameToNomTag(n.name)(originProv(td.nme.toLoc, "class"), ctx)
                      val fieldsRefined = fields.iterator.map(f =>
                        if (f._1.name.isCapitalized) f
                        else f._1 ->
                          freshVar(noProv,
                            S(f._1.name.drop(f._1.name.indexOf('#') + 1)) // strip any "...#" prefix
                          )(1).tap(_.upperBounds ::= f._2)
                        ).toList
                      PolymorphicType(0, FunctionType(
                        singleTup(RecordType.mk(fieldsRefined.filterNot(_._1.name.isCapitalized))(noProv)),
                        nomTag & RecordType.mk(
                          fieldsRefined ::: tparamTags
                        )(noProv))(originProv(td.nme.toLoc, "class constructor")))
                    case Trt =>
                      val nomTag = trtNameToNomTag(n.name)(originProv(td.nme.toLoc, "trait"), ctx)
                      val tv = freshVar(noProv)(1)
                      tv.upperBounds ::= td.bodyTy
                      PolymorphicType(0, FunctionType(
                        singleTup(tv), tv & nomTag & RecordType.mk(tparamTags)(noProv)
                      )(originProv(td.nme.toLoc, "trait constructor")))
                  }
                  ctx += n.name -> ctor
              }
              true
            }
            checkParents(td.bodyTy) && checkCycle(td.bodyTy)(Set.single(L(td.nme))) && checkAbstract
        }
        def checkRegular(ty: SimpleType)(implicit reached: Map[Str, Ls[SimpleType]]): Bool = ty match {
          case tr @ TypeRef(defn, targs) => reached.get(defn.name) match {
            case None => checkRegular(tr.expandWith(false))(reached + (defn.name -> targs))
            case Some(tys) =>
              // TODO less syntactic check...
              if (defn === td.nme && tys =/= targs) {
                err(msg"Type definition is not regular: it occurs within itself as ${
                  expandType(tr, true).show
                }, but is defined as ${
                  expandType(TypeRef(defn, td.targs)(noProv), true).show
                }", td.toLoc)(raise, noProv)
                false
              } else true
          }
          case _ => ty.children.forall(checkRegular)
        }
        // Note: this will end up going through some types several times... We could make sure to
        //    only go through each type once, but the error messages would be worse.
        if (rightParents && checkRegular(td.bodyTy)(Map(n.name -> td.targs)))
          td.nme.name -> td :: Nil
        else Nil
      })
    def typeMethods(implicit ctx: Ctx): Ctx = {
      /* Recursive traverse the type definition and type the bodies of method definitions 
       * by applying the targs in `TypeRef` and rigidifying class type parameters. */
      def typeMethod(td: TypeDef): Unit = {
        implicit val prov: TypeProvenance = tp(td.toLoc, "type definition")
        val rigidtargs = td.targs.map(freshenAbove(ctx.lvl, _, true))
        val reverseRigid = rigidtargs.lazyZip(td.targs).toMap
        def rec(tr: TypeRef, top: Bool = false)(ctx: Ctx): MethodDefs = {
          implicit val thisCtx: Ctx = ctx.nest
          thisCtx += "this" -> tr
          val td2 = ctx.tyDefs(tr.defn.name)
          val targsMap = td2.tparams.iterator.map(_.name).zip(tr.targs).toMap
          val declared = MutMap.empty[Str, Opt[Loc]]
          val defined = MutMap.empty[Str, Opt[Loc]]
          
          def filterTR(ty: SimpleType): List[TypeRef] = ty match {
            case tr: TypeRef => tr :: Nil
            case ComposedType(false, l, r) => filterTR(l) ::: filterTR(r)
            case _ => Nil
          }
          def go(md: MethodDef[_]): (Str, MethodType) = md match { case MethodDef(rec, prt, nme, tparams, rhs) =>
            implicit val prov: TypeProvenance = tp(md.toLoc, (if (!top) "inherited " else "") + "method "
              + rhs.fold(_ => "definition", _ => "declaration"))
            val fullName = s"${td.nme.name}.${nme.name}"
            if (top) {
              if (!nme.name.isCapitalized)
                err(msg"Method names must start with a capital letter", nme.toLoc)
              rhs.fold(_ => defined, _ => declared).get(nme.name) match {
                case S(loco) => err(
                  msg"Method '$fullName' is already ${rhs.fold(_ => "defined", _ => "declared")}" -> nme.toLoc ::
                  msg"at" -> loco :: Nil)
                case N =>
              }
              tparams.groupBy(_.name).foreach {
                case s -> tps if tps.size > 1 => err(
                  msg"Multiple declarations of type parameter ${s} in ${prov.desc}" -> md.toLoc ::
                  tps.map(tp => msg"Declared at" -> tp.toLoc))
                case _ =>
              }
              val tp1s = td2.tparams.iterator.map(tp => tp.name -> tp).toMap
              tparams.foreach(tp2 => tp1s.get(tp2.name) match {
                case S(tp1) => warn(
                  msg"Method type parameter ${tp1}" -> tp1.toLoc ::
                  msg"shadows class type parameter ${tp2}" -> tp2.toLoc :: Nil)
                case N =>
              })
            }
            rhs.fold(_ => defined, _ => declared) += nme.name -> nme.toLoc
            val dummyTargs2 = tparams.map(p =>
              TraitTag(Var(p.name))(originProv(p.toLoc, "method type parameter")))
            val targsMap2 = targsMap ++ tparams.iterator.map(_.name).zip(dummyTargs2).toMap
            val reverseRigid2 = reverseRigid ++ dummyTargs2.map(t =>
              t -> freshVar(t.prov, S(t.id.idStr))(thisCtx.lvl + 1))
            val bodyTy = subst(rhs.fold(
              term =>
                typeLetRhs(rec, nme.name, term)(thisCtx, raise, targsMap2),
              ty => PolymorphicType(thisCtx.lvl,
                typeType(ty)(thisCtx.nextLevel, raise, targsMap2))
                // ^ Note: we need to go to the next level here,
                //    which is also done automatically by `typeLetRhs` in the case above
            ), reverseRigid2)
            val mthTy = td2.wrapMethod(bodyTy)
            if (rhs.isRight || !declared.isDefinedAt(nme.name)) {
              if (top) thisCtx.mthenv += fullName -> mthTy
              thisCtx.mthenv += nme.name -> mthTy
            }
            nme.name -> MethodType(thisCtx.lvl, ProvType(bodyTy.body)(prov), td2.nme)
          }
          MethodDefs(td2.nme, filterTR(tr.expand).map(rec(_)(thisCtx)),
            td2.mthDecls.iterator.map(go).toMap, td2.mthDefs.iterator.map(go).toMap)
        }
        val mds = rec(TypeRef(td.nme, rigidtargs)(prov), true)(ctx)
        checkSubsume(td, mds)
      }
      /* Perform subsumption checking on method declarations and definitions by rigidifying class type variables,
       * then register the method signitures in the context */
      def checkSubsume(td: TypeDef, mds: MethodDefs): Unit = {
        implicit val prov: TypeProvenance = tp(td.toLoc, "type definition")
        val tn = td.nme
        val MethodDefs(_, _, decls, defns) = mds
        val MethodDefs(_, _, declsInherit, defnsInherit) = mds.propagate(true)
        val rigidtargs = td.targs.map(freshenAbove(ctx.lvl, _, true))
        val targsMap = td.targs.lazyZip(rigidtargs).toMap[SimpleType, SimpleType]
        def ss(mt: PolymorphicType, bmt: PolymorphicType)(implicit prov: TypeProvenance) =
          constrain(subst(mt, targsMap).instantiate, subst(bmt, targsMap).rigidify)
        def registerImplicit(nme: Str, mthTy: MethodType) = ctx.getmth(nme) match {
          case S(MethodType(_, _, prts)) if prts.iterator.map(prt => Var(prt.name.decapitalize)).toSet
              .subsetOf(ctx.allBaseClassesOf(tn.name)) =>
          case S(MethodType(_, _, prts)) if prts.forall(prt =>
              ctx.allBaseClassesOf(prt.name).contains(Var(tn.name.decapitalize))) =>
            ctx.mthenv += nme -> mthTy
          case S(mt2) => ctx.mthenv += nme -> (mt2 + mthTy)
          case N => ctx.mthenv += nme -> mthTy
        }
        declsInherit.foreach { case nme -> mt =>
          implicit val prov: TypeProvenance = mt.prov
          val fullName = s"${tn.name}.${nme}"
          val mthTy = td.wrapMethod(mt)
          ctx.mthenv += fullName -> mthTy
        }
        defnsInherit.foreach { case nme -> mt => 
          implicit val prov: TypeProvenance = mt.prov
          val fullName = s"${tn.name}.${nme}"
          println(s">> Checking subsumption for inferred type of $nme : $mt")
          (if (decls.isDefinedAt(nme) && !defns.isDefinedAt(nme)) decls.get(nme) else N).orElse(declsInherit.get(nme))
            .foreach(ss(mt, _))
          val mthTy = td.wrapMethod(mt)
          if (!declsInherit.get(nme).exists(_.prts === mt.prts))
            ctx.mthenv += fullName -> ctx.getmth(fullName).getOrElse(mthTy)
          if (!decls.isDefinedAt(nme) && !declsInherit.isDefinedAt(nme)) registerImplicit(nme, mthTy)
        }
        decls.foreach { case nme -> mt =>
          implicit val prov: TypeProvenance = mt.prov
          val fullName = s"${tn.name}.${nme}"
          println(s">> Checking subsumption for declared type of $nme : $mt")
          declsInherit.get(nme).orElse(defnsInherit.get(nme).tap(_.foreach { mt2 =>
            err(msg"Overriding method ${mt2.prts.headOption.fold("")(_.name)}.${nme} without explicit declaration is not allowed."
                -> mt.prov.loco ::
              msg"Note: method definition inherited from" -> mt2.prov.loco :: Nil)(raise, noProv)
            println(s">> Checking subsumption (against inferred type) for inferred type of $nme : $mt")
          })).foreach(ss(mt, _))
          val mthTy = td.wrapMethod(mt)
          ctx.mthenv += fullName -> mthTy
          registerImplicit(nme, mthTy)
        }
        defns.foreach { case nme -> mt => 
          implicit val prov: TypeProvenance = mt.prov
          val fullName = s"${tn.name}.${nme}"
          println(s">> Checking subsumption for inferred type of $nme : $mt")
          decls.get(nme).orElse((declsInherit.get(nme), defnsInherit.get(nme)) match {
            case (S(decl), S(defn)) if decl.prts === defn.prts ||
                defn.prts.forall(bn => decl.prts.iterator.map(bn2 => Var(bn2.name.decapitalize)).toSet
                .subsetOf(ctx.allBaseClassesOf(bn.name))) =>
              S(decl)
            case (_, S(defn)) =>
              err(msg"Overriding method ${defn.prts.headOption.fold("")(_.name)}.${nme} without explicit declaration is not allowed."
                  -> mt.prov.loco ::
                msg"Note: method definition inherited from" -> defn.prov.loco :: Nil)(raise, noProv)
              println(s">> Checking subsumption (against inferred type) for inferred type of $nme : $mt")
              S(defn)
            case (S(decl), N) => S(decl)
            case (N, N) => N
          }).foreach(ss(mt, _))
          val mthTy = td.wrapMethod(mt)
          ctx.mthenv += fullName -> ctx.getmth(fullName).fold(mthTy)(if (decls.isDefinedAt(nme)) _ else mthTy)
          ctx.mthenv += s"${tn.name}#${nme}" -> mthTy
          if (!decls.isDefinedAt(nme) && !declsInherit.isDefinedAt(nme)) registerImplicit(nme, mthTy)
        }
      }
      newDefs.foreach(td => if (ctx.tyDefs.isDefinedAt(td.nme.name)) typeMethod(td))
      ctx
    }
    typeMethods(typeTypeDefs(ctx.copy(env = allEnv, mthenv = allMthEnv, tyDefs = allDefs)))
  }
  /* Parameters `vars` and `newDefsInfo` are used for typing `TypeName`s.
   * If the key is found in `vars`, the type is typed as the associated value. Use case: type arguments.
   * If the key is found in `newDefsInfo`, the type is typed as a `TypeRef`, where the associated value
   *   is used to check the kind of the definition and the number of type arguments expected. Use case:
   *   for typing bodies of type definitions with mutually recursive references. */
  def typeType(ty: Type, simplify: Bool = true)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType] = Map.empty,
      newDefsInfo: Map[Str, (TypeDefKind, Int)] = Map.empty): SimpleType = 
    typeType2(ty, simplify)._1
  /* Also returns an iterable of `TypeVariable`s instantiated when typing `TypeVar`s.
   * Useful for instantiating them by substitution when expanding a `TypeRef`. */
  // TODO better record type provenances!
  def typeType2(ty: Type, simplify: Bool = true)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType] = Map.empty,
      newDefsInfo: Map[Str, (TypeDefKind, Int)] = Map.empty): (SimpleType, Iterable[TypeVariable]) = {
    val typeType = ()
    def typeNamed(loc: Opt[Loc], name: Str): (() => ST) \/ (TypeDefKind, Int) =
      newDefsInfo.get(name).orElse(ctx.tyDefs.get(name).map(td => (td.kind, td.tparamsargs.size))).toRight(() =>
        err("type identifier not found: " + name, loc)(raise, tp(loc, "missing type")))
    val localVars = mutable.Map.empty[TypeVar, TypeVariable]
    def rec(ty: Type)(implicit ctx: Ctx, recVars: Map[TypeVar, TypeVariable]): SimpleType = ty match {
      case Top => ExtrType(false)(tp(ty.toLoc, "top type"))
      case Bot => ExtrType(true)(tp(ty.toLoc, "bottom type"))
      case Bounds(lb, ub) => TypeBounds(rec(lb), rec(ub))(tp(ty.toLoc,
        if (lb === Bot && ub === Top) "type wildcard" else "type bounds"))
      // case Tuple(fields) => TupleType(fields.map(f => f._1 -> rec(f._2)))(tp(ty.toLoc, "tuple type"))
      case Tuple(fields) => TupleType(fields.map(f => f._1 -> rec(f._2)))(fields match {
        case Nil | ((N, _) :: Nil) => noProv
        case _ => tp(ty.toLoc, "tuple type")
      })
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
      case Literal(lit) => ClassTag(lit, lit.baseClasses)(tp(ty.toLoc, "literal type"))
      case tn @ TypeName(name) =>
        val tyLoc = ty.toLoc
        val tpr = tp(tyLoc, "type reference")
        vars.get(name).getOrElse {
          typeNamed(tyLoc, name) match {
            case R((_, tpnum)) =>
              if (tpnum =/= 0) {
                err(msg"Type $name takes parameters", tyLoc)(raise, tpr)
              } else TypeRef(tn, Nil)(tpr)
            case L(e) =>
              if (name.isEmpty || !name.head.isLower) e()
              else typeNamed(tyLoc, name.capitalize) match {
                case R((kind, _)) => kind match {
                  case Cls => clsNameToNomTag(name.capitalize)(tp(tyLoc, "class tag"), ctx)
                  case Trt => trtNameToNomTag(name.capitalize)(tp(tyLoc, "trait tag"), ctx)
                  case Als => err(
                    msg"Type alias ${name.capitalize} cannot be used as a type tag", tyLoc)(raise, tpr)
                }
                case L(_) => e()
              }
          }
        }
      case tv: TypeVar =>
        // assert(ty.toLoc.isDefined)
        recVars.getOrElse(tv,
          localVars.getOrElseUpdate(tv, freshVar(noProv, tv.identifier.toOption))
            .withProv(tp(ty.toLoc, "type variable")))
      case AppliedType(base, targs) =>
        val prov = tp(ty.toLoc, "applied type reference")
        typeNamed(ty.toLoc, base.name) match {
          case R((_, tpnum)) =>
            val realTargs = if (targs.size === tpnum) targs.map(rec) else {
              err(msg"Wrong number of type arguments – expected ${tpnum.toString}, found ${
                  targs.size.toString}", ty.toLoc)(raise, prov)
              (targs.iterator.map(rec) ++ Iterator.continually(freshVar(noProv))).take(tpnum).toList
            }
            TypeRef(base, realTargs)(prov)
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
    (rec(ty)(ctx, Map.empty), localVars.values)
  }
  
  def typePattern(pat: Term)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType] = Map.empty): SimpleType =
    typeTerm(pat)(ctx.copy(inPattern = true), raise, vars)
  
  
  def typeStatement(s: DesugaredStatement, allowPure: Bool)
        (implicit ctx: Ctx, raise: Raise): PolymorphicType \/ Ls[Binding] = s match {
    case Def(false, Var("_"), L(rhs)) => typeStatement(rhs, allowPure)
    case Def(isrec, nme, L(rhs)) => // TODO reject R(..)
      if (nme.name === "_")
        err(msg"Illegal definition name: ${nme.name}", nme.toLoc)(raise, noProv)
      val ty_sch = typeLetRhs(isrec, nme.name, rhs)
      ctx += nme.name -> ty_sch
      R(nme.name -> ty_sch :: Nil)
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
      var errorsCount = 0
      constrain(lhs, rhs)({
        case err: TypeError =>
          // Note that we do not immediately abort constraining because we still
          //  care about getting the non-erroneous parts of the code return meaningful types.
          // In other words, this is so that errors do not interfere too much
          //  with the rest of the (hopefully good) code.
          if (errorsCount === 0) {
            constrain(errType, res)(_ => (), noProv, ctx)
            // ^ This is just to get error types leak into the result
            raise(err)
          } else if (errorsCount < 3) {
            // Silence further errors from this location.
          } else {
            return res
            // ^ Stop constraining, at this point.
            //    This is to avoid rogue (explosive) constraint solving from badly-behaved error cases.
            //    For instance see the StressTraits.mls test.
          }
          errorsCount += 1
        case diag => raise(diag)
      }, prov, ctx)
      res
    }
    term match {
      case v @ Var("_") =>
        if (ctx.inPattern || funkyTuples) freshVar(tp(v.toLoc, "wildcard"))
        else err(msg"Widlcard in expression position.", v.toLoc)
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
        val ty = ctx.get(name).fold(err("identifier not found: " + name, term.toLoc): TypeScheme) {
          // TODO: delay type expansion to message display and show the expected type here!
          case AbstractConstructor(absMths) =>
            val td = ctx.tyDefs(name)
            err((msg"Instantiation of an abstract type is forbidden" -> term.toLoc)
              :: (msg"Note that ${td.kind.str} ${td.nme} is abstract:" -> td.toLoc)
              :: absMths.map { case mn => msg"Hint: method $mn is abstract" -> mn.toLoc }.toList)
          case ty => ty
        }.instantiate
        mkProxy(ty, prov)
        // ^ TODO maybe use a description passed in param?
        // currently we get things like "flows into variable reference"
        // but we used to get the better "flows into object receiver" or "flows into applied expression"...
      case lit: Lit => ClassTag(lit, lit.baseClasses)(prov)
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
      case tup: Tup if funkyTuples =>
        typeTerms(tup :: Nil, false, Nil)
      case Tup(fs) =>
        TupleType(fs.map(f => f._1 -> typeTerm(f._2)))(fs match {
          case Nil | ((N, _) :: Nil) => noProv
          case _ => tp(term.toLoc, "tuple literal")
        })
      case Bra(false, trm: Blk) => typeTerm(trm)
      case Bra(rcd, trm @ (_: Tup | _: Blk)) if funkyTuples => typeTerms(trm :: Nil, rcd, Nil)
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
          // ^ Note: this no longer really makes a difference, due to tupled arguments by default
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
          ctx.getmth(fieldName.name) match {
            case S(mth_ty) =>
              if (mth_ty.prts.size > 1)
                err(msg"Implicit call to method ${fieldName.name} is forbidden because it is ambiguous." -> term.toLoc
                  :: msg"Unrelated methods named ${fieldName.name} are defined by:" -> N
                  :: mth_ty.prts.iterator.map(prt => ctx.tyDefs(prt.name))
                    .map(td => msg"• ${td.kind.str} ${td.nme}" -> td.nme.toLoc).toList)
              val o_ty = typeTerm(obj)
              val res = freshVar(prov)
              con(mth_ty.instantiate, FunctionType(singleTup(o_ty), res)(prov), res)
            case N =>
              if (fieldName.name.isCapitalized) err(msg"Method ${fieldName.name} not found", term.toLoc)
              else rcdSel(obj, fieldName) // TODO: no else?
          }
        obj match {
          case Var(name) if name.isCapitalized && ctx.tyDefs.isDefinedAt(name) =>
            ctx.getmth(s"${name}.${fieldName.name}") match {
              case S(mth_ty) => mth_ty.instantiate
              case N =>
                err(msg"Class ${name} has no method ${fieldName.name}", term.toLoc)
                mthCall(obj, fieldName)
            }
          case _ => mthCall(obj, fieldName)
        }
      case Let(isrec, nme, rhs, bod) =>
        val n_ty = typeLetRhs(isrec, nme.name, rhs)
        val newCtx = ctx.nest
        newCtx += nme.name -> n_ty
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
          ClassTag(lit, lit.baseClasses)(tp(pat.toLoc, "literal pattern"))
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
                case Cls => clsNameToNomTag(td.nme.name)(tp(pat.toLoc, "class pattern"), ctx)
                case Trt => trtNameToNomTag(td.nme.name)(tp(pat.toLoc, "trait pattern"), ctx)
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
            case TypeRef(td, Nil) => td
            case TypeRef(td, targs) =>
              AppliedType(td, targs.map { t =>
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
