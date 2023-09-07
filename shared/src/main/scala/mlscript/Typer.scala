package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import Set.{empty => semp}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

/** A class encapsulating type inference state.
 *  It uses its own internal representation of types and type variables, using mutable data structures.
 *  Inferred SimpleType values are then turned into CompactType values for simplification.
 *  In order to turn the resulting CompactType into a mlscript.Type, we use `expandCompactType`.
 */
class Typer(var dbg: Boolean, var verbose: Bool, var explainErrors: Bool, var newDefs: Bool = false)
    extends ucs.Desugarer with TypeSimplifier {
  
  def funkyTuples: Bool = false
  def doFactorize: Bool = false
  def showAllErrors: Bool = false // TODO enable?
  def maxSuccessiveErrReports: Int = 3
  
  var generalizeCurriedFunctions: Boolean = false
  var approximateNegativeFunction: Boolean = false
  var preciselyTypeRecursion: Bool = false
  var distributeForalls: Boolean = false
  var generalizeArguments: Boolean = false
  
  var noCycleCheck: Boolean = false
  var noRecursiveTypes: Boolean = false
  var irregularTypes: Boolean = false
  var constrainedTypes: Boolean = false
  
  var recordProvenances: Boolean = true
  
  type Binding = Str -> SimpleType
  type Bindings = Map[Str, SimpleType]
  
  type Level = Int
  val MinLevel: Int = 0
  val MaxLevel: Int = 1024
  
  type Pol = Opt[Bool]
  
  type GenLambdas >: Bool
  def doGenLambdas(implicit gl: GenLambdas): Bool = gl === true
  
  /**  `env`: maps the names of all global and local bindings to their types
    *  Keys of `mthEnv`:
    * `L` represents the inferred types of method definitions. The first value is the parent name,
    *   and the second value is the method name.
    * `R` represents the actual method types.
    *   The first optional value is the parent name, with `N` representing implicit calls,
    *   and the second value is the method name.
    *   (See the case for `Sel` in `typeTerm` for documentation on explicit vs. implicit calls.)
    * The public helper functions should be preferred for manipulating `mthEnv`
   */
  case class Ctx(
      parent: Opt[Ctx],
      env: MutMap[Str, TypeInfo],
      mthEnv: MutMap[(Str, Str) \/ (Opt[Str], Str), MethodType],
      lvl: Int,
      inPattern: Bool,
      tyDefs: Map[Str, TypeDef],
      tyDefs2: MutMap[Str, DelayedTypeInfo],
      inRecursiveDef: Opt[Var], // TODO rm
      extrCtx: ExtrCtx,
  ) {
    def +=(b: Str -> TypeInfo): Unit = env += b
    def ++=(bs: IterableOnce[Str -> TypeInfo]): Unit = bs.iterator.foreach(+=)
    def get(name: Str): Opt[TypeInfo] = env.get(name) orElse parent.dlof(_.get(name))(N)
    def contains(name: Str): Bool = env.contains(name) || parent.exists(_.contains(name))
    def addMth(parent: Opt[Str], nme: Str, ty: MethodType): Unit = mthEnv += R(parent, nme) -> ty
    def addMthDefn(parent: Str, nme: Str, ty: MethodType): Unit = mthEnv += L(parent, nme) -> ty
    private def getMth(key: (Str, Str) \/ (Opt[Str], Str)): Opt[MethodType] =
      mthEnv.get(key) orElse parent.dlof(_.getMth(key))(N)
    def getMth(parent: Opt[Str], nme: Str): Opt[MethodType] = getMth(R(parent, nme))
    def getMthDefn(parent: Str, nme: Str): Opt[MethodType] = getMth(L(parent, nme))
    private def containsMth(key: (Str, Str) \/ (Opt[Str], Str)): Bool = mthEnv.contains(key) || parent.exists(_.containsMth(key))
    def containsMth(parent: Opt[Str], nme: Str): Bool = containsMth(R(parent, nme))
    def nest: Ctx = copy(Some(this), MutMap.empty, MutMap.empty)
    def nextLevel[R](k: Ctx => R)(implicit raise: Raise, prov: TP, shadows: Shadows=Shadows.empty): R = { // TODO rm implicits here and in freshen functions
      val newCtx = copy(lvl = lvl + 1, extrCtx = MutMap.empty)
      val res = k(newCtx)
      val ec = newCtx.extrCtx
      assert(constrainedTypes || newCtx.extrCtx.isEmpty)
      trace(s"UNSTASHING... (out)") {
        implicit val ctx: Ctx = this
        ec.foreach { case (tv, bs) => bs.foreach {
          case (true, b) => constrain(b, tv)
          case (false, b) => constrain(tv, b)
        }}
        ec.clear()
      }()
      res
    }
    def poly(k: Ctx => ST)(implicit raise: Raise, prov: TP, shadows: Shadows=Shadows.empty): ST = {
      nextLevel { newCtx =>
        
        val innerTy = k(newCtx)
        assert(constrainedTypes || newCtx.extrCtx.isEmpty)
        
        implicit val ctx: Ctx = newCtx
        implicit val freshened: MutMap[TV, ST] = MutMap.empty
        
        val cty = ConstrainedType.mk(newCtx.extrCtx.iterator.flatMap { case (tv, bs) =>
          bs.iterator
            // .filter(_._2.level > lvl) // does not seem to change anything!
            .map { case (p, b) =>
              assert(b.level > lvl)
              if (p) (b, tv) else (tv, b) }
          }.toList, innerTy)
        
        println(s"Inferred poly constr: $cty  —— where ${cty.showBounds}")
        
        val cty_fresh =
          // * Samnity check: uncommenting this should change nothing (modulo type simplification randomness)
          // cty.freshenAbove(lvl, false)
          cty
        
        if (dbg) if (cty_fresh =/= cty) println(s"Refreshed:            $cty_fresh  —— where ${cty_fresh.showBounds}")
        
        val poly = PolymorphicType.mk(lvl, cty_fresh)
        
        /* 
        newCtx.extrCtx.valuesIterator.foreach { buff =>
          val filtered = buff.filter(_._2.level <= lvl)
          if (filtered.nonEmpty) println(s"FILTER $filtered")
          assert(filtered.isEmpty)
          buff.clear()
        }
        */
        newCtx.extrCtx.clear()
        
        poly
      }
    }
    private val abcCache: MutMap[Str, Set[TypeName]] = MutMap.empty
    def allBaseClassesOf(name: Str): Set[TypeName] = abcCache.getOrElseUpdate(name,
      tyDefs.get(name).fold(Set.empty[TypeName])(_.allBaseClasses(this)(Set.empty)))
  }
  object Ctx {
    private val initBase: Ctx = Ctx(
      parent = N,
      env = MutMap.from(builtinBindings.iterator.map(nt => nt._1 -> VarSymbol(nt._2, Var(nt._1)))),
      mthEnv = MutMap.empty,
      lvl = MinLevel,
      inPattern = false,
      tyDefs = Map.from(builtinTypes.map(t => t.nme.name -> t)),
      tyDefs2 = MutMap.empty,
      inRecursiveDef = N,
      MutMap.empty,
    )
    def init: Ctx = if (!newDefs) initBase else {
      val res = initBase.copy(
        tyDefs2 = MutMap.from(nuBuiltinTypes.map { t =>
          val lti = new DelayedTypeInfo(t, Map.empty)(initBase, e => lastWords(e.theMsg))
          initBase.env += t.nme.name -> lti
          t.nme.name -> lti
        }),
      )
      implicit val raise: Raise = throw _
      res.tyDefs2.valuesIterator.foreach(_.complete())
      res
    }
    val empty: Ctx = init
  }
  implicit def lvl(implicit ctx: Ctx): Int = ctx.lvl
  
  import TypeProvenance.{apply => tp}
  def ttp(trm: Term, desc: Str = "", isType: Bool = false): TypeProvenance =
    TypeProvenance(trm.toLoc, if (desc === "") trm.describe else desc, isType = isType)
  def originProv(loco: Opt[Loc], desc: Str, name: Str): TypeProvenance = {
    tp(loco, desc, S(name), isType = true)
    // ^ If we did not treat "origin provenances" differently,
    //    it would yields unnatural errors like:
      //│ ╟── expression of type `B` is not a function
      //│ ║  l.6: 	    method Map[B]: B -> A
      //│ ║       	               ^
    // So we should keep the info but not shadow the more relevant later provenances
  }
  
  object NoProv extends TypeProvenance(N, "expression") {
    override def toString: Str = "[NO PROV]"
  }
  def noProv: TypeProvenance = NoProv
  def provTODO: TypeProvenance = noProv
  def noTyProv: TypeProvenance = TypeProvenance(N, "type", isType = true)
  
  private def sing[A](x: A): Set[A] = Set.single(x)
  
  val TopType: ExtrType = ExtrType(false)(noTyProv)
  val BotType: ExtrType = ExtrType(true)(noTyProv)
  
  val UnitType: ClassTag = if (newDefs) ClassTag(UnitLit(true), semp)(noTyProv)
    else ClassTag(Var("unit"), semp)(noTyProv)
  
  val BoolType: ST = if (newDefs) TR(TN("Bool"), Nil)(noTyProv)
    else ClassTag(Var("bool"), semp)(noTyProv)
  val ObjCls: ClassTag = ClassTag(Var("Object"), semp)(noTyProv)
  val ObjType: ST = if (newDefs) TR(TN("Object"), Nil)(noTyProv)
    else TopType
  val IntType: ST = if (newDefs) TR(TN("Int"), Nil)(noTyProv)
    else ClassTag(Var("int"), sing(TN("number")))(noTyProv)
  val DecType: ST = if (newDefs) TR(TN("Num"), Nil)(noTyProv)
    else ClassTag(Var("number"), semp)(noTyProv)
  val StrType: ST = if (newDefs) TR(TN("Str"), Nil)(noTyProv)
    else ClassTag(Var("string"), semp)(noTyProv)
  val TrueType: ST = if (newDefs) TR(TN("true"), Nil)(noTyProv)
    else ClassTag(Var("true"), sing(TN("bool")))(noTyProv)
  val FalseType: ST = if (newDefs) TR(TN("false"), Nil)(noTyProv)
    else ClassTag(Var("false"), sing(TN("bool")))(noTyProv)
  
  val EqlTag: TraitTag = TraitTag(Var("Eql"), Set.empty)(noProv)
  
  val ErrTypeId: SimpleTerm = Var("error")
  
  // TODO rm this obsolete definition (was there for the old frontend)
  private val primTypes =
    List("unit" -> UnitType, "bool" -> BoolType, "int" -> IntType, "number" -> DecType, "string" -> StrType,
      "anything" -> TopType, "nothing" -> BotType)
  
  private val preludeLoc = Loc(0, 0, Origin("<prelude>", 0, new FastParseHelpers("")))
  
  val nuBuiltinTypes: Ls[NuTypeDef] = Ls(
    NuTypeDef(Cls, TN("Object"), Nil, N, N, N, Nil, N, N, TypingUnit(Nil))(N, N),
    NuTypeDef(Trt, TN("Eql"), (S(VarianceInfo.contra), TN("A")) :: Nil, N, N, N, Nil, N, N, TypingUnit(Nil))(N, S(preludeLoc)),
    NuTypeDef(Cls, TN("Num"), Nil, N, N, N, Nil, N, N, TypingUnit(Nil))(N, S(preludeLoc)),
    NuTypeDef(Cls, TN("Int"), Nil, N, N, N, Var("Num") :: Nil, N, N, TypingUnit(Nil))(N, S(preludeLoc)),
    NuTypeDef(Cls, TN("Bool"), Nil, N, N, S(Union(TN("true"), TN("false"))), Nil, N, N, TypingUnit(Nil))(N, S(preludeLoc)),
    NuTypeDef(Mod, TN("true"), Nil, N, N, N, Var("Bool") :: Nil, N, N, TypingUnit(Nil))(N, N),
    NuTypeDef(Mod, TN("false"), Nil, N, N, N, Var("Bool") :: Nil, N, N, TypingUnit(Nil))(N, N),
    NuTypeDef(Cls, TN("Str"), Nil, N, N, N, Nil, N, N, TypingUnit(Nil))(N, S(preludeLoc)),
    NuTypeDef(Als, TN("undefined"), Nil, N, N, S(Literal(UnitLit(true))), Nil, N, N, TypingUnit(Nil))(N, S(preludeLoc)),
    NuTypeDef(Als, TN("null"), Nil, N, N, S(Literal(UnitLit(false))), Nil, N, N, TypingUnit(Nil))(N, S(preludeLoc)),
  )
  val builtinTypes: Ls[TypeDef] =
    TypeDef(Cls, TN("int"), Nil, TopType, Nil, Nil, sing(TN("number")), N, Nil) ::
    TypeDef(Cls, TN("number"), Nil, TopType, Nil, Nil, semp, N, Nil) ::
    TypeDef(Cls, TN("bool"), Nil, TopType, Nil, Nil, semp, N, Nil) ::
    TypeDef(Cls, TN("true"), Nil, TopType, Nil, Nil, sing(TN("bool")), N, Nil) ::
    TypeDef(Cls, TN("false"), Nil, TopType, Nil, Nil, sing(TN("bool")), N, Nil) ::
    TypeDef(Cls, TN("string"), Nil, TopType, Nil, Nil, semp, N, Nil) ::
    TypeDef(Als, TN("undefined"), Nil, ClassTag(UnitLit(true), semp)(noProv), Nil, Nil, semp, N, Nil) ::
    TypeDef(Als, TN("null"), Nil, ClassTag(UnitLit(false), semp)(noProv), Nil, Nil, semp, N, Nil) ::
    TypeDef(Als, TN("anything"), Nil, TopType, Nil, Nil, semp, N, Nil) ::
    TypeDef(Als, TN("nothing"), Nil, BotType, Nil, Nil, semp, N, Nil) ::
    TypeDef(Cls, TN("error"), Nil, TopType, Nil, Nil, semp, N, Nil) ::
    TypeDef(Cls, TN("unit"), Nil, TopType, Nil, Nil, semp, N, Nil) ::
    {
      val tv = freshVar(noTyProv, N)(1)
      val tyDef = TypeDef(Als, TN("Array"), List(TN("A") -> tv),
        ArrayType(FieldType(None, tv)(noTyProv))(noTyProv), Nil, Nil, semp, N, Nil)
        // * ^ Note that the `noTyProv` here is kind of a problem
        // *    since we currently expand primitive types eagerly in DNFs.
        // *  For instance, see `inn2 v1` in test `Yicong.mls`.
        // *  We could instead treat these primitives like any other TypeRef,
        // *    but that currently requires more simplifier work
        // *    to get rid of things like `1 & int` and `T | nothing`.
      tyDef.tvarVariances = S(MutMap(tv -> VarianceInfo.co))
      tyDef
    } ::
    {
      val tv = freshVar(noTyProv, N)(1)
      val tyDef = TypeDef(Als, TN("MutArray"), List(TN("A") -> tv),
        ArrayType(FieldType(Some(tv), tv)(noTyProv))(noTyProv), Nil, Nil, semp, N, Nil)
      tyDef.tvarVariances = S(MutMap(tv -> VarianceInfo.in))
      tyDef
    } ::
    Nil
  val primitiveTypes: Set[Str] =
    builtinTypes.iterator.map(_.nme.name).flatMap(n => n.decapitalize :: n.capitalize :: Nil).toSet +
      "Object" + "Num" + "Str"
  val reservedTypeNames: Set[Str] = primitiveTypes + "Eql"
  def singleTup(ty: ST): ST =
    if (funkyTuples) ty else TupleType((N, ty.toUpper(ty.prov) ) :: Nil)(noProv)
  val builtinBindings: Bindings = {
    val tv = freshVar(noProv, N)(1)
    import FunctionType.{ apply => fun }
    val intBinOpTy = fun(singleTup(IntType), fun(singleTup(IntType), IntType)(noProv))(noProv)
    val numberBinOpTy = fun(singleTup(DecType), fun(singleTup(DecType), DecType)(noProv))(noProv)
    val numberBinPred = fun(singleTup(DecType), fun(singleTup(DecType), BoolType)(noProv))(noProv)
    val stringBinPred = fun(singleTup(StrType), fun(singleTup(StrType), BoolType)(noProv))(noProv)
    Map(
      "true" -> TrueType,
      "false" -> FalseType,
      "True" -> TypeRef(TN("True"), Nil)(noProv),
      "False" -> TypeRef(TN("False"), Nil)(noProv),
      "NaN" -> DecType,
      "document" -> BotType,
      "window" -> BotType,
      "typeof" -> fun(singleTup(TopType), StrType)(noProv),
      "toString" -> fun(singleTup(TopType), StrType)(noProv),
      "not" -> fun(singleTup(BoolType), BoolType)(noProv),
      "succ" -> fun(singleTup(IntType), IntType)(noProv),
      "log" -> PolymorphicType(MinLevel, fun(singleTup(tv), UnitType)(noProv)),
      "discard" -> PolymorphicType(MinLevel, fun(singleTup(tv), UnitType)(noProv)),
      "negate" -> fun(singleTup(IntType), IntType)(noProv),
      "round" -> fun(singleTup(DecType), IntType)(noProv),
      "add" -> intBinOpTy,
      "sub" -> intBinOpTy,
      "mul" -> intBinOpTy,
      "div" -> intBinOpTy,
      "sqrt" -> fun(singleTup(IntType), IntType)(noProv),
      "lt" -> numberBinPred,
      "le" -> numberBinPred,
      "gt" -> numberBinPred,
      "ge" -> numberBinPred,
      "slt" -> stringBinPred,
      "sle" -> stringBinPred,
      "sgt" -> stringBinPred,
      "sge" -> stringBinPred,
      "length" -> fun(singleTup(StrType), IntType)(noProv),
      "concat" -> fun(singleTup(StrType), fun(singleTup(StrType), StrType)(noProv))(noProv),
      "eq" -> {
        val v = freshVar(noProv, N)(1)
        PolymorphicType(MinLevel, fun(singleTup(v), fun(singleTup(v), BoolType)(noProv))(noProv))
      },
      "ne" -> {
        val v = freshVar(noProv, N)(1)
        PolymorphicType(MinLevel, fun(singleTup(v), fun(singleTup(v), BoolType)(noProv))(noProv))
      },
      "error" -> BotType,
      "+" -> intBinOpTy,
      "-" -> intBinOpTy,
      "*" -> intBinOpTy,
      "%" -> intBinOpTy,
      "/" -> numberBinOpTy,
      "<" -> numberBinPred,
      ">" -> numberBinPred,
      "<=" -> numberBinPred,
      ">=" -> numberBinPred,
      "==" -> numberBinPred,
      "===" -> {
        val v = freshVar(noProv, N)(1)
        val eq = TypeRef(TypeName("Eql"), v :: Nil)(noProv)
        PolymorphicType(MinLevel, fun(singleTup(eq), fun(singleTup(v), BoolType)(noProv))(noProv))
      },
      "&&" -> fun(singleTup(BoolType), fun(singleTup(BoolType), BoolType)(noProv))(noProv),
      "||" -> fun(singleTup(BoolType), fun(singleTup(BoolType), BoolType)(noProv))(noProv),
      "id" -> {
        val v = freshVar(noProv, N)(1)
        PolymorphicType(MinLevel, fun(singleTup(v), v)(noProv))
      },
      "if" -> {
        val v = freshVar(noProv, N)(1)
        // PolymorphicType(MinLevel, fun(singleTup(BoolType), fun(singleTup(v), fun(singleTup(v), v)(noProv))(noProv))(noProv))
        PolymorphicType(MinLevel, fun(singleTup(BoolType), fun(singleTup(v), fun(singleTup(v), v)(noProv))(noProv))(noProv))
      },
      "emptyArray" -> {
        val v = freshVar(noProv, N)(1)
        PolymorphicType(0, ArrayType(FieldType(S(v), v)(noProv))(noProv))
      },
    ) ++ primTypes ++ primTypes.map(p => "" + p._1.capitalize -> p._2) // TODO settle on naming convention...
  }
  
  
  /* Parameters `vars` and `newDefsInfo` are used for typing `TypeName`s.
   * If the key is found in `vars`, the type is typed as the associated value. Use case: type arguments.
   * If the key is found in `newDefsInfo`, the type is typed as a `TypeRef`, where the associated value
   *   is used to check the kind of the definition and the number of type arguments expected. Use case:
   *   for typing bodies of type definitions with mutually recursive references. */
  def typeType(ty: Type, simplify: Bool = true)
        (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType], newDefsInfo: Map[Str, (TypeDefKind, Int)] = Map.empty): SimpleType = {
    typeType2(ty, simplify)._1
  }
  def typePolyType(ty: Type, simplify: Bool = true)
        (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType], newDefsInfo: Map[Str, (TypeDefKind, Int)] = Map.empty): SimpleType = {
    implicit val prov: TP = tp(ty.toLoc, "type")
    val baseLevel = vars.valuesIterator.map(_.level).maxOption.getOrElse(MinLevel)
    ctx.copy(lvl = baseLevel).poly { implicit ctx => typeType2(ty, simplify)._1 }
  }
  
  /* Also returns an iterable of `TypeVariable`s instantiated when typing `TypeVar`s.
   * Useful for instantiating them by substitution when expanding a `TypeRef`. */
  def typeType2(ty: Type, simplify: Bool = true)
        (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType],
        newDefsInfo: Map[Str, (TypeDefKind, Int)]): (SimpleType, Iterable[TypeVariable]) = // TODO rm _2 result?
      // trace(s"$lvl. Typing type $ty") {
      trace(s"Typing type ${ty.showDbg}") {
    println(s"vars=$vars newDefsInfo=$newDefsInfo")
    val typeType2 = ()
    // val outerCtxLvl = MinLevel + 1
    val outerCtxLvl = ctx.lvl
    def checkKind(k: DeclKind, nme: Str, loc: Opt[Loc]): Unit = k match {
      case Cls | Mod | Als | Trt => ()
      case _ => err(msg"${k.str} ${nme} cannot be used as a type", loc); ()
    }
    def typeNamed(loc: Opt[Loc], name: Str): (() => ST) \/ (TypeDefKind, Int) =
      newDefsInfo.get(name)
        .orElse(ctx.tyDefs.get(name).map(td => (td.kind, td.tparamsargs.size)))
        .orElse(ctx.get(name).flatMap {
          case CompletedTypeInfo(mem: TypedNuTypeDef) =>
            checkKind(mem.decl.kind, mem.nme.name, loc)
            S(mem.td.kind, mem.tparams.size)
          case ti: DelayedTypeInfo =>
            checkKind(ti.decl.kind, ti.decl.name, loc)
            ti.decl match {
              case NuTypeDef(k @ (Cls | Mod | Als | Trt), _, tps, _,  _, _, _, _, _, _) =>
                S(k, tps.size)
              case NuTypeDef(k @ Mxn, nme, tps,  _, _, _, _, _, _, _) =>
                S(k, tps.size)
              case fd: NuFunDef =>
                N
            }
          case _ => N
        })
        .toRight(() => err("type identifier not found: " + name, loc)(raise))
    val localVars = mutable.Map.empty[TypeVar, TypeVariable]
    def tyTp(loco: Opt[Loc], desc: Str, originName: Opt[Str] = N) =
      TypeProvenance(loco, desc, originName, isType = true)
    def rec(ty: Type)(implicit ctx: Ctx, recVars: Map[TypeVar, TypeVariable]): SimpleType = trace(s"$lvl. type ${ty.showDbg}") { ty match {
      case Top => ExtrType(false)(tyTp(ty.toLoc, "top type"))
      case Bot => ExtrType(true)(tyTp(ty.toLoc, "bottom type"))
      case Bounds(Bot, Top) =>
        val p = tyTp(ty.toLoc, "type wildcard")
        TypeBounds(ExtrType(true)(p), ExtrType(false)(p))(p)
      case Bounds(lb, ub) =>
        val lb_ty = rec(lb)
        val ub_ty = rec(ub)
        implicit val prov: TP = tyTp(ty.toLoc, "type bounds")
        constrain(lb_ty, ub_ty)
        TypeBounds(lb_ty, ub_ty)(prov)
      case Tuple(fields) =>
        TupleType(fields.mapValues(f =>
            FieldType(f.in.map(rec), rec(f.out))(tp(f.toLoc, "tuple field"))
          ))(tyTp(ty.toLoc, "tuple type"))
      case Splice(fields) => 
        SpliceType(fields.map{ 
          case L(l) => {
            val t = rec(l)
            val res = ArrayType(freshVar(t.prov, N).toUpper(t.prov))(t.prov)
            constrain(t, res)(raise, t.prov, ctx)
            L(t)
          }
          case R(f) => {
            R(FieldType(f.in.map(rec), rec(f.out))(tp(f.toLoc, "splice field")))
          }
          })(tyTp(ty.toLoc, "splice type"))
      case Inter(lhs, rhs) => (if (simplify) rec(lhs) & (rec(rhs), _: TypeProvenance)
          else ComposedType(false, rec(lhs), rec(rhs)) _
        )(tyTp(ty.toLoc, "intersection type"))
      case Union(lhs, rhs) => (if (simplify) rec(lhs) | (rec(rhs), _: TypeProvenance)
          else ComposedType(true, rec(lhs), rec(rhs)) _
        )(tyTp(ty.toLoc, "union type"))
      case Neg(t) => NegType(rec(t))(tyTp(ty.toLoc, "type negation"))
      case Record(fs) => 
        val prov = tyTp(ty.toLoc, "record type")
        fs.groupMap(_._1.name)(_._1).foreach { case s -> fieldNames if fieldNames.sizeIs > 1 => err(
            msg"Multiple declarations of field name ${s} in ${prov.desc}" -> ty.toLoc
              :: fieldNames.map(tp => msg"Declared at" -> tp.toLoc))(raise)
          case _ =>
        }
        RecordType.mk(fs.map { nt =>
          if (nt._1.name.isCapitalized)
            err(msg"Field identifiers must start with a small letter", nt._1.toLoc)(raise)
          nt._1 -> FieldType(nt._2.in.map(rec), rec(nt._2.out))(
            tp(App(nt._1, Var("").withLocOf(nt._2)).toCoveringLoc,
              (if (nt._2.in.isDefined) "mutable " else "") + "record field"))
        })(prov)
      case Function(lhs, rhs) => FunctionType(rec(lhs), rec(rhs))(tyTp(ty.toLoc, "function type"))
      case WithExtension(b, r) => WithType(rec(b),
        RecordType(
            r.fields.map { case (n, f) => n -> FieldType(f.in.map(rec), rec(f.out))(
              tyTp(App(n, Var("").withLocOf(f)).toCoveringLoc, "extension field")) }
          )(tyTp(r.toLoc, "extension record")))(tyTp(ty.toLoc, "extension type"))
      case Literal(lit) =>
        ClassTag(lit, if (newDefs) lit.baseClassesNu
          else lit.baseClassesOld)(tyTp(ty.toLoc, "literal type"))
      case TypeName("this") =>
        ctx.env.get("this") match {
          case S(_: AbstractConstructor | _: LazyTypeInfo) => die
          case S(VarSymbol(t: SimpleType, _)) => t
          case N => err(msg"undeclared `this`" -> ty.toLoc :: Nil)
        }
      case tn @ TypeTag(name) => rec(TypeName(name.decapitalize)) // TODO rm this hack
      // case tn @ TypeTag(name) => rec(TypeName(name))
      case tn @ TypeName(name) =>
        val tyLoc = ty.toLoc
        val tpr = tyTp(tyLoc, "type reference")
        vars.getOrElse(name, {
          typeNamed(tyLoc, name) match {
            case R((_, tpnum)) =>
              if (tpnum === 0) TypeRef(tn, Nil)(tpr)
              else ctx.tyDefs2.get(name) match {
                case S(lti) =>
                  lti.decl match {
                    case NuTypeDef(Cls | Mod, _, _, _, _, _, _, _, _, _) =>
                      clsNameToNomTag(ctx.tyDefs2(name).decl.asInstanceOf[NuTypeDef])(tyTp(tyLoc, "class tag"), ctx)
                    case NuTypeDef(Trt, _, _, _, _, _, _, _, _, _) =>
                      trtNameToNomTag(ctx.tyDefs2(name).decl.asInstanceOf[NuTypeDef])(tyTp(tyLoc, "class tag"), ctx)
                    case NuTypeDef(Als, _, _, _, _, _, _, _, _, _) =>
                      TypeRef(tn, List.fill(tpnum)(freshVar(noProv, N, N)))(tpr)
                    case _ => die // TODO
                  }
                case _ => err(msg"Type $name takes parameters", tyLoc)(raise)
              }
            case L(e) =>
              if (name.isEmpty || !name.head.isLower) e()
              else (typeNamed(tyLoc, name.capitalize), ctx.tyDefs.get(name.capitalize)) match {
                case (R((kind, _)), S(td)) => kind match {
                  case Cls => clsNameToNomTag(td)(tyTp(tyLoc, "class tag"), ctx)
                  case Trt => trtNameToNomTag(td)(tyTp(tyLoc, "trait tag"), ctx)
                  case Als => err(
                    msg"Type alias ${name.capitalize} cannot be used as a type tag", tyLoc)(raise)
                  case Mod => err(
                    msg"Module ${name.capitalize} cannot be used as a type tag", tyLoc)(raise)
                  case Mxn => err(
                    msg"Mixin ${name.capitalize} cannot be used as a type tag", tyLoc)(raise)
                }
                case _ => e()
              }
          }
        })
      case tv: TypeVar => vars.getOrElse(tv.identifier.toOption.getOrElse(""), {
        recVars.getOrElse(tv,
          localVars.getOrElseUpdate(tv, freshVar(noProv, N, tv.name)
              (outerCtxLvl)) // * Type variables not explicily bound are assigned the widest (the outer context's) level
          ).withProv(tyTp(ty.toLoc, "type variable"))
      })
      case AppliedType(base, targs) =>
        val prov = tyTp(ty.toLoc, "applied type reference")
        typeNamed(ty.toLoc, base.name) match {
          case R((_, tpnum)) =>
            val realTargs = if (targs.size === tpnum) targs.map(rec) else {
              err(msg"Wrong number of type arguments – expected ${tpnum.toString}, found ${
                  targs.size.toString}", ty.toLoc)(raise)
              (targs.iterator.map(rec) ++ Iterator.continually(freshVar(noProv, N))).take(tpnum).toList
            }
            TypeRef(base, realTargs)(prov)
          case L(e) => e()
        }
      case Selection(base, nme) =>
        implicit val gl: GenLambdas = false
        // val base_ty = typeTerm(base)
        val base_ty = rec(base)
        def go(b_ty: ST, rfnt: Var => Opt[FieldType]): ST = b_ty.unwrapAll match {
          case ct: TypeRef => die // TODO actually
          case ClassTag(Var(clsNme), _) =>
            // TODO we should still succeed even if the member is not completed...
            lookupMember(clsNme, rfnt, nme.toVar) match {
              case R(cls: TypedNuCls) =>
                if (cls.tparams.nonEmpty) ??? // TODO
                clsNameToNomTag(cls.td)(TypeProvenance(ty.toLoc, "type selection", isType = true), ctx)
              case R(als: TypedNuAls) =>
                if (als.tparams.nonEmpty) ??? // TODO
                als.body
              case R(m) => err(msg"Illegal selection of ${m.kind.str} member in type position", nme.toLoc)
              case L(d) => err(d)
            }
          case _ =>
            err(msg"Illegal prefix of type selection: ${b_ty.expPos}", base.toLoc)
        }
        go(base_ty, _ => N)
      case Recursive(uv, body) =>
        val tv = freshVar(tyTp(ty.toLoc, "local type binding"), N, uv.name)
        val bod = rec(body)(ctx, recVars + (uv -> tv))
        tv.assignedTo = S(bod)
        tv
      case Rem(base, fs) => Without(rec(base), fs.toSortedSet)(tyTp(ty.toLoc, "field removal type"))
      case Constrained(base, tvbs, where) =>
        val res = rec(base match {
          case ty: Type => ty
          case _ => die
        })
        tvbs.foreach { case (tv, Bounds(lb, ub)) =>
          constrain(rec(lb), tv)(raise, tp(lb.toLoc, "lower bound specifiation"), ctx)
          constrain(tv, rec(ub))(raise, tp(ub.toLoc, "upper bound specifiation"), ctx)
        }
        where.foreach { case Bounds(lo, hi) =>
          constrain(rec(lo), rec(hi))(raise,
            tp(mergeOptions(lo.toLoc, hi.toLoc)(_ ++ _), "constraint specifiation"), ctx)
        }
        res
      case PolyType(vars, ty) =>
        val oldLvl = ctx.lvl
        implicit val prov: TP = TypeProvenance(ty.toLoc, "polymorphic type")
        ctx.poly { implicit ctx =>
          var newVars = recVars
          val tvs = vars.map {
            case L(tn) =>
              die // this probably never happens...
              freshVar(tyTp(tn.toLoc, "quantified type name"), N, S(tn.name))
            case R(tv) =>
              val nv = freshVar(tyTp(
                    tv.toLoc,
                    // N, // * Here we choose to omit this location,
                    // * because pointing to the binding place of forall TVs in error messages
                    // * is often redundant, as these forall types are usually self-contained.
                    "quantified type variable",
                  tv.name
                ), N, tv.name)
              newVars += tv -> nv
              nv
          }
          rec(ty)(ctx, newVars)
        }
    }}(r => s"=> $r")
    (rec(ty)(ctx, Map.empty), localVars.values)
  }(r => s"=> ${r._1} ——— ${r._2.mkString(", ")}")
  
  def typePattern(pat: Term)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType] = Map.empty): SimpleType =
    typeTerm(pat)(ctx.copy(inPattern = true), raise, vars, genLambdas = false)
  
  
  def typeStatement(s: DesugaredStatement, allowPure: Bool)
        (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType], genLambdas: GenLambdas): ST \/ Opt[Binding] = s match {
    case Def(false, Var("_"), L(rhs), isByname) => typeStatement(rhs, allowPure)
    case Def(isrec, nme, L(rhs), isByname) => // TODO reject R(..)
      if (nme.name === "_")
        err(msg"Illegal definition name: ${nme.name}", nme.toLoc)(raise)
      val ty_sch = typeLetRhs(isrec, nme.name, rhs)
      nme.uid = S(nextUid)
      ctx += nme.name -> VarSymbol(ty_sch, nme)
      R(S(nme.name -> ty_sch))
    case t @ Tup(fs) if !allowPure => // Note: not sure this is still used!
      val thing = fs match {
        case (S(_), _) :: Nil => "field"
        case Nil => "empty tuple"
        case _ => "tuple"
      }
      warn(s"Useless $thing in statement position.", t.toLoc)
      L(PolymorphicType(MinLevel, typeTerm(t)))
    case t: Term =>
      val ty = typeTerm(t)
      if (!allowPure) {
        if (t.isInstanceOf[Var] || t.isInstanceOf[Lit])
          warn("Pure expression does nothing in statement position.", t.toLoc)
        else
          constrain(mkProxy(ty, TypeProvenance(t.toCoveringLoc, "expression in statement position")), UnitType)(
            raise = err => raise(WarningReport( // Demote constraint errors from this to warnings
              msg"Expression in statement position should have type `unit`." -> N ::
              msg"Use the `discard` function to discard non-unit values, making the intent clearer." -> N ::
              err.allMsgs)),
            prov = TypeProvenance(t.toLoc, t.describe), ctx)
      }
      L(ty)
    case _ =>
      err(msg"Illegal position for this ${s.describe} statement.", s.toLoc)(raise)
      R(N)
  }
  
  /** Like `typeLetRhs` but removes unnecessary polymorphic type wrappers. */
  def typeLetRhs2(isrec: Boolean, nme: Str, rhs: Term)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType]): ST = {
    val res = typeLetRhs(isrec: Boolean, nme: Str, rhs: Term)(ctx, raise, vars, genLambdas = true)
    def stripPoly(ty: ST): ST = ty match {
      case pt: PolymorphicType =>
        PolymorphicType.mk(pt.polymLevel, stripPoly(pt.body))
      case _ => ty
    }
    stripPoly(res)
  }
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: Str, rhs: Term)(implicit ctx: Ctx, raise: Raise,
      vars: Map[Str, SimpleType], genLambdas: GenLambdas): PolymorphicType = {
    
    implicit val prov: TP = TypeProvenance(rhs.toLoc, "binding of " + rhs.describe)
    
    // * TODO eventually these should NOT introduce PolymorphicType-s on their own
    // * (don't use `nextLevel`)
    
    val res = if (isrec) {
      val e_ty = freshVar(
        // It turns out it is better to NOT store a provenance here,
        //    or it will obscure the true provenance of constraints causing errors
        //    across recursive references.
        noProv,
        // TypeProvenance(rhs.toLoc, "let-bound value"),
        N,
        S(nme),
        recPlaceholder = true
      )(lvl + 1)
      ctx += nme -> VarSymbol(e_ty, Var(nme))
      
      ctx.copy(inRecursiveDef = S(Var(nme))).nextLevel { implicit ctx: Ctx =>
        implicit val extrCtx: Opt[ExtrCtx] = N
        implicit val genLambdas: GenLambdas = preciselyTypeRecursion
        
        val ty = typeTerm(rhs)
        
        constrain(ty, e_ty)(raise, prov, ctx)
        e_ty.assignedTo = S(ty)
      }
      e_ty
    } else ctx.nextLevel { ctx => // * Note: let polymorphism (`ctx.nextLevel`)
      typeTerm(rhs)(ctx, raise, vars, genLambdas = true)
    }
    PolymorphicType(lvl, res)
    // * ^ TODO change: this only needs to be done in the rec case;
    // *    and in that case, only for functions!
  }
  
  def mkProxy(ty: SimpleType, prov: TypeProvenance): SimpleType = {
    if (recordProvenances) ProvType(ty)(prov)
    else ty // TODO don't do this when debugging errors
    // TODO switch to return this in perf mode:
    // ty
  }
  
  // TODO also prevent rebinding of "not"
  val reservedVarNames: Set[Str] = Set("|", "&", "~", ",", "neg", "and", "or", "is")
  
  object ValidVar {
    def unapply(v: Var)(implicit raise: Raise): S[Str] = S {
      if (reservedVarNames(v.name))
        err(s"Illegal use of reserved operator: " + v.name,
          v.toLoc)(raise)
      v.name
    }
  }
  object ValidPatVar {
    def unapply(v: Var)(implicit ctx: Ctx, raise: Raise): Opt[Str] =
      if (ctx.inPattern && v.isPatVar) {
        ctx.parent.dlof(_.get(v.name))(N) |>? { case S(VarSymbol(ts: SimpleType, _)) =>
          ts.unwrapProxies } |>? {
            case S(ClassTag(Var(v.name), _)) =>
              warn(msg"Variable name '${v.name}' already names a symbol in scope. " +
                s"If you want to refer to that symbol, you can use `scope.${v.name}`; " +
                s"if not, give your future readers a break and use another name :^)", v.toLoc)
        }
        ValidVar.unapply(v)
      } else N
  }
  
  def typeMonomorphicTerm(term: Term)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType]): SimpleType = {
    implicit val genLambdas: GenLambdas = false
    typeTerm(term)
  }
  
  def typePolymorphicTerm(term: Term)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType]): SimpleType = {
      implicit val genLambdas: GenLambdas = true
      typeTerm(term)
    }
  
  def notifyMoreErrors(action_ing: Str, prov: TypeProvenance)(implicit raise: Raise): Unit = {
    err(msg"Note: further errors omitted while ${action_ing} ${prov.desc}", prov.loco)
    ()
  }
  
  /** Infer the type of a term.
    * genLambdas: whether to generalize lambdas that are found immediately in the term.
    * Note that the generalization of inner/nested lambdas is determined by other parameters; eg:
    *   - we never generalize lambdas on the LHS of an application
    *     (since they will be instantiated immediately anyweay)
    *   - we don't generalize curried lambdas by default
    *     (since we can always distribute the quantification of the inferred type variables later)
    *     UNLESS generalizeCurriedFunctions or constrainedTypes are enabled
    *     NOTE: when distrib. is disabled, we typically enable generalizeCurriedFunctions to make up for it
    *   - we always generalize lambdas found in arguments, record/tuple fields, etc.
    */
  def typeTerm(term: Term)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType], genLambdas: GenLambdas): SimpleType
        = trace[ST](s"$lvl. Typing ${if (ctx.inPattern) "pattern" else "term"} $term") {
        // = trace[ST](s"$lvl. Typing ${if (ctx.inPattern) "pattern" else "term"} $term   ${extrCtx.map(_.size)}") {
    implicit val prov: TypeProvenance = ttp(term)
    
    def con(lhs: SimpleType, rhs: SimpleType, res: SimpleType)(implicit ctx: Ctx): SimpleType = {
      var errorsCount = 0
      constrain(lhs, rhs)({
        case err: ErrorReport =>
          // Note that we do not immediately abort constraining because we still
          //  care about getting the non-erroneous parts of the code return meaningful types.
          // In other words, this is so that errors do not interfere too much
          //  with the rest of the (hopefully good) code.
          if (errorsCount === 0) {
            constrain(errType, res)(_ => (), noProv, ctx)
            // ^ This is just to get error types leak into the result
            raise(err)
          } else if (errorsCount < maxSuccessiveErrReports) {
            // * Silence further errors from this location.
            if (showAllErrors) raise(err)
          } else {
            if (showAllErrors) notifyMoreErrors("typing", prov)
            return res
            // ^ Stop constraining, at this point.
            //    This is to avoid rogue (explosive) constraint solving from badly-behaved error cases.
            //    For instance see the StressTraits.mls test.
          }
          errorsCount += 1
        case diag => raise(diag)
      }, prov, ctx) // Q: extrCtx here?
      res
    }
    
    term match {
        
      case v @ Var("_") =>
        if (ctx.inPattern || funkyTuples) freshVar(tp(v.toLoc, "wildcard"), N)
        else err(msg"Widlcard in expression position.", v.toLoc)
        
      case Asc(v @ ValidPatVar(nme), ty) =>
        val ty_ty = typeType(ty)(ctx.copy(inPattern = false), raise, vars)
        val prov = tp(if (verboseConstraintProvenanceHints) v.toLoc else N, "variable")
        ctx.env.get(nme) match {
          case S(_) => err(s"Duplicate use of annotated pattern variable $nme", v.toLoc)
          case N =>
            ctx += nme -> VarSymbol(ty_ty, v)
            ty_ty
        }
        
      case Asc(trm, ty) =>
        val trm_ty = typePolymorphicTerm(trm)
        val ty_ty = typeType(ty)(ctx.copy(inPattern = false), raise, vars)
        if (ctx.inPattern) { unify(trm_ty, ty_ty); ty_ty } // * In patterns, we actually _unify_ the pattern and ascribed type 
        else con(trm_ty, ty_ty, ty_ty)
      case (v @ ValidPatVar(nme)) =>
        val prov = tp(if (verboseConstraintProvenanceHints) v.toLoc else N, "variable")
        // * Note: only look at ctx.env, and not the outer ones!
        ctx.env.get(nme).collect { case VarSymbol(ts, dv) => assert(v.uid.isDefined); v.uid = dv.uid; ts }
          .getOrElse {
            val res = new TypeVariable(lvl, Nil, Nil, N, Option.when(dbg)(nme))(prov)
            v.uid = S(nextUid)
            ctx += nme -> VarSymbol(res, v)
            res
          }
      case v @ ValidVar(name) =>
        val ty = ctx.get(name).fold(err("identifier not found: " + name, term.toLoc): ST) {
          case AbstractConstructor(absMths, traitWithMths) =>
            val td = ctx.tyDefs(name)
            err((msg"Instantiation of an abstract type is forbidden" -> term.toLoc)
              :: (
                if (traitWithMths) {
                  assert(td.kind is Trt)
                  msg"Note that traits with methods are always considered abstract" -> td.toLoc :: Nil
                } else
                  msg"Note that ${td.kind.str} ${td.nme} is abstract:" -> td.toLoc
                  :: absMths.map { case mn => msg"Hint: method ${mn.name} is abstract" -> mn.toLoc }.toList
              )
            )
          case VarSymbol(ty, _) => ty
          case lti: LazyTypeInfo =>
            // TODO deal with classes without parameter lists (ie needing `new`)
            def checkNotAbstract(decl: NuDecl) =
              if (decl.isAbstract)
                err(msg"Class ${decl.name} is abstract and cannot be instantiated", term.toLoc)
            lti match {
              case ti: CompletedTypeInfo =>
                ti.member match {
                  case ti: TypedNuFun =>
                    ti.typeSignature
                  case p: NuParam =>
                    p.typeSignature
                  case ti: TypedNuCls =>
                    checkNotAbstract(ti.decl)
                    ti.typeSignature
                  case ti: TypedNuDecl =>
                    err(msg"${ti.kind.str} ${ti.name} cannot be used in term position", prov.loco)
                }
              case ti: DelayedTypeInfo =>
                checkNotAbstract(ti.decl)
                ti.typeSignature
            }
        }
        mkProxy(ty, prov)
        // ^ TODO maybe use a description passed in param?
        // currently we get things like "flows into variable reference"
        // but we used to get the better "flows into object receiver" or "flows into applied expression"...
      case lit: Lit => ClassTag(lit, if (newDefs) lit.baseClassesNu else lit.baseClassesOld)(prov)
      case Super() =>
        err(s"Illegal use of `super`", term.toLoc)(raise)
        typeTerm(Var("super").withLocOf(term))
      case App(Var("neg" | "~"), trm) if funkyTuples => typeTerm(trm).neg(prov)
      case App(App(Var("|"), lhs), rhs) if funkyTuples =>
        typeTerm(lhs) | (typeTerm(rhs), prov)
      case App(App(Var("&"), lhs), rhs) if funkyTuples =>
        typeTerm(lhs) & (typeTerm(rhs), prov)
      case Rcd(fs) =>
        val prov = tp(term.toLoc, "record literal")
        fs.groupMap(_._1.name)(_._1).foreach { case s -> fieldNames if fieldNames.sizeIs > 1 => err(
            msg"Multiple declarations of field name ${s} in ${prov.desc}" -> term.toLoc
              :: fieldNames.map(tp => msg"Declared at" -> tp.toLoc))(raise)
          case _ =>
        }
        RecordType.mk(fs.map { case (n, Fld(mut, _, t)) => 
          if (n.name.isCapitalized)
            err(msg"Field identifiers must start with a small letter", term.toLoc)(raise)
          val tym = typePolymorphicTerm(t)
          val fprov = tp(App(n, t).toLoc, (if (mut) "mutable " else "") + "record field")
          if (mut) {
            val res = freshVar(fprov, N, S(n.name))
            val rs = con(tym, res, res)
            (n, FieldType(Some(rs), rs)(fprov))
          } else (n, tym.toUpper(fprov))
        })(prov)
      case tup: Tup if funkyTuples =>
        typeTerms(tup :: Nil, false, Nil)
      case Tup(fs) =>
        TupleType(fs.mapConserve { case e @ (n, Fld(mut, spec, t)) =>
          n match {
            case S(v) if ctx.inPattern =>
              (n, Fld(mut, spec,
                Asc(v, t.toTypeRaise).withLoc(v.toLoc.fold(t.toLoc)(_ ++ t.toLoc |> some))))
            case _ => e
          }
        }.map { case (n, Fld(mut, _, t)) =>
          val tym = typePolymorphicTerm(t)
          // val tym = if (n.isDefined) typeType(t.toTypeRaise)
          //   else typePolymorphicTerm(t)
          val fprov = tp(t.toLoc, (if (mut) "mutable " else "") + "tuple field")
          if (mut) {
            val res = freshVar(fprov, N, n.map(_.name))
            val rs = con(tym, res, res)
            (n, FieldType(Some(rs), rs)(fprov))
          } else (n, tym.toUpper(fprov))
        })(fs match {
          case Nil | ((N, _) :: Nil) => noProv // TODO rm?
          case _ => tp(term.toLoc, "tuple literal")
        })
      case Subs(a, i) =>
        val t_a = typeMonomorphicTerm(a)
        val t_i = typeMonomorphicTerm(i)
        con(t_i, IntType, TopType)
        val elemType = freshVar(prov, N)
        elemType.upperBounds ::=
          // * We forbid using [⋅] indexing to access elements that possibly have `undefined` value,
          // *  which could result in surprising behavior and bugs in the presence of parametricity!
          // * Note that in modern JS, `undefined` is arguably not a value you're supposed to use explicitly;
          // *  `null` should be used instead for those willing to indulge in the Billion Dollar Mistake.
          TypeRef(TypeName("undefined"), Nil)(noProv).neg(
            prov.copy(desc = "prohibited undefined element")) // TODO better reporting for this; the prov isn't actually used
        con(t_a, ArrayType(elemType.toUpper(tp(i.toLoc, "array element")))(prov), elemType) |
          TypeRef(TypeName("undefined"), Nil)(prov.copy(desc = "possibly-undefined array access"))
      case Assign(s @ Sel(r, f), rhs) =>
        val o_ty = typeMonomorphicTerm(r)
        val sprov = tp(s.toLoc, "assigned selection")
        val fieldType = freshVar(sprov, N, Opt.when(!f.name.startsWith("_"))(f.name))
        val obj_ty =
          // Note: this proxy does not seem to make any difference:
          mkProxy(o_ty, tp(r.toCoveringLoc, "receiver"))
        con(obj_ty, RecordType.mk((f, FieldType(Some(fieldType), TopType)(
          tp(f.toLoc, "assigned field")
        )) :: Nil)(sprov), fieldType)
        val vl = typeMonomorphicTerm(rhs)
        con(vl, fieldType, UnitType.withProv(prov))
      case Assign(s @ Subs(a, i), rhs) => 
        val a_ty = typeMonomorphicTerm(a)
        val sprov = tp(s.toLoc, "assigned array element")
        val elemType = freshVar(sprov, N)
        val arr_ty =
            // Note: this proxy does not seem to make any difference:
            mkProxy(a_ty, tp(a.toCoveringLoc, "receiver"))
        con(arr_ty, ArrayType(FieldType(Some(elemType), elemType)(sprov))(prov), TopType)
        val i_ty = typeMonomorphicTerm(i)
        con(i_ty, IntType, TopType)
        val vl = typeMonomorphicTerm(rhs)
        con(vl, elemType, UnitType.withProv(prov))
      case Assign(lhs, rhs) =>
        err(msg"Illegal assignment" -> prov.loco
          :: msg"cannot assign to ${lhs.describe}" -> lhs.toLoc :: Nil)
      case Splc(es) => 
        SpliceType(es.map{
          case L(l) => L({
            val t_l = typeMonomorphicTerm(l)
            val t_a = ArrayType(freshVar(prov, N).toUpper(prov))(prov)
            con(t_l, t_a, t_l)
          }) 
          case R(Fld(mt, sp, r)) => {
            val t = typeMonomorphicTerm(r)
            if (mt) { R(FieldType(Some(t), t)(t.prov)) } else {R(t.toUpper(t.prov))}
          }
        })(prov)
      case Bra(false, trm: Blk) => typeTerm(trm)
      case Bra(rcd, trm @ (_: Tup | _: Blk)) if funkyTuples => typeTerms(trm :: Nil, rcd, Nil)
      case Bra(_, trm) => typeTerm(trm)
      case Blk((s: Term) :: Nil) => typeTerm(s)
      case Blk(Nil) => UnitType.withProv(prov)
      case pat if ctx.inPattern =>
        err(msg"Unsupported pattern shape${
          if (dbg) " ("+pat.getClass.toString+")" else ""}:", pat.toLoc)(raise)
      case Lam(pat, body) if doGenLambdas =>
        println(s"TYPING POLY LAM")
        ctx.nest.poly { newCtx =>
          val param_ty = typePattern(pat)(newCtx, raise, vars)
          val midCtx = newCtx
          val body_ty = typeTerm(body)(newCtx, raise, vars,
            doGenLambdas && (generalizeCurriedFunctions || constrainedTypes))
          FunctionType(param_ty, body_ty)(tp(term.toLoc, "function"))
        }
      case Lam(pat, body) =>
        val newCtx = ctx.nest
        val param_ty = typePattern(pat)(newCtx, raise, vars)
        assert(!doGenLambdas)
        val body_ty = typeTerm(body)(newCtx, raise, vars, genLambdas)
        FunctionType(param_ty, body_ty)(tp(term.toLoc, "function"))
      case App(App(Var("is"), _), _) =>
        val desug = If(IfThen(term, Var("true")), S(Var("false")))
        term.desugaredTerm = S(desug)
        typeTerm(desug)
      case App(App(Var("and"), Tup(_ -> Fld(_, _, lhs) :: Nil)), Tup(_ -> Fld(_, _, rhs) :: Nil)) =>
        val desug = If(IfThen(lhs, rhs), S(Var("false")))
        term.desugaredTerm = S(desug)
        typeTerm(desug)
      case App(f: Term, a @ Tup(fields)) if (fields.exists(x => x._1.isDefined)) =>
        val f_ty = typeTerm(f)
        val fun_ty: SimpleType = f_ty.unwrapProxies match {
          case tv: TypeVariable =>
            def getLowerboundFuns(tv: TypeVariable): List[FunctionType] = {
              val res: List[FunctionType] = tv.lowerBounds.map(x => 
                x.unwrapProvs match {
                  case PolymorphicType(_, AliasOf(fun_ty @ FunctionType(_, _))) =>
                    List(fun_ty)
                  case tvv: TypeVariable =>
                    getLowerboundFuns(tvv) 
                  case _ =>
                    err("match error", f.toLoc)
                    Nil
                }).flatten
              res
            }
            val funs = getLowerboundFuns(tv)
            funs match {
              case x :: Nil => 
                funs.head
              case Nil =>
                err("cannot extract any function", f.toLoc)
              case _ =>
               err(s"more than one fun type found! => ${funs}", f.toLoc)
            }
          case PolymorphicType(_, AliasOf(fun_ty @ FunctionType(_, _))) =>
            fun_ty
          case FunctionType(_, _) =>
            f_ty
          case _ =>
            err("match error", f.toLoc)
            f_ty
        }
        val argsList = fun_ty.unwrapProxies match {
          case FunctionType(TupleType(fields), _) =>
            fields.map(x => x._1 match {
              case Some(arg) =>
                arg
              case N =>
                err("cannot use named args in this case.", a.toLoc)
                Var("error")
            })
          case _ => 
            err("match error", f.toLoc)
            Nil
        }
        desugarNamedArgs(term, f, a, argsList)
      case App(f, a) =>
        val f_ty = typeMonomorphicTerm(f)
        val a_ty = {
          def typeArg(a: Term): ST =
            if (!generalizeArguments) typePolymorphicTerm(a)
            else ctx.poly { implicit ctx => typePolymorphicTerm(a) }
          a match {
            case tup @ Tup(as) =>
              TupleType(as.map { case (n, Fld(mut, spec, a)) => // TODO handle mut?
                // assert(!mut)
                val fprov = tp(a.toLoc, "argument")
                val tym = typeArg(a)
                (n, tym.toUpper(fprov))
              })(as match { // TODO dedup w/ general Tup case
                case Nil | ((N, _) :: Nil) => noProv
                case _ => tp(tup.toLoc, "argument list")
              })
            case _ => // can happen in the old parser
              typeArg(a)
          }
        }
        
        val arg_ty = mkProxy(a_ty, tp(a.toCoveringLoc, "argument"))
          // ^ Note: this no longer really makes a difference, due to tupled arguments by default
        val funProv = tp(f.toCoveringLoc, "applied expression")
        val fun_ty = mkProxy(f_ty, funProv)
          // ^ This is mostly not useful, except in test Tuples.fun with `(1, true, "hey").2`
        val res = freshVar(prov, N)
        val res_ty = con(fun_ty, FunctionType(arg_ty, res)(
          prov
          // funProv // TODO: better?
          ), res)
        res_ty
      case Sel(obj, fieldName) =>
        implicit val shadows: Shadows = Shadows.empty
        // Explicit method calls have the form `x.(Class.Method)`
        // Implicit method calls have the form `x.Method`
        //   If two unrelated classes define methods of the same name,
        //   implicit calls to this method are marked as ambiguous and are forbidden
        // Explicit method retrievals have the form `Class.Method`
        //   Returns a function expecting an additional argument of type `Class` before the method arguments
        def rcdSel(obj: Term, fieldName: Var) = {
          val o_ty = typeMonomorphicTerm(obj)
          val res = freshVar(prov, N, Opt.when(!fieldName.name.startsWith("_"))(fieldName.name))
          val obj_ty = mkProxy(o_ty, tp(obj.toCoveringLoc, "receiver"))
          val rcd_ty = RecordType.mk(
            fieldName -> res.toUpper(tp(fieldName.toLoc, "field selector")) :: Nil)(prov)
          con(obj_ty, rcd_ty, res)
        }
        def mthCallOrSel(obj: Term, fieldName: Var) = 
          ( if (newDefs) N else fieldName.name match {
            case s"$parent.$nme" => ctx.getMth(S(parent), nme) // explicit calls
            case nme => ctx.getMth(N, nme) // implicit calls
          }) match {
            case S(mth_ty) =>
              if (mth_ty.body.isEmpty) {
                assert(mth_ty.parents.sizeCompare(1) > 0, mth_ty)
                err(msg"Implicit call to method ${fieldName.name} is forbidden because it is ambiguous." -> term.toLoc
                  :: msg"Unrelated methods named ${fieldName.name} are defined by:" -> N
                  :: mth_ty.parents.map { prt =>
                    val td = ctx.tyDefs(prt.name)
                    msg"• ${td.kind.str} ${td.nme}" -> td.nme.toLoc
                  })
              }
              val o_ty = typeMonomorphicTerm(obj)
              val res = freshVar(prov, N)
              con(mth_ty.toPT.instantiate, FunctionType(singleTup(o_ty), res)(prov), res)
            case N =>
              if (!newDefs && fieldName.name.isCapitalized) err(msg"Method ${fieldName.name} not found", term.toLoc)
              else {
                val realPrefix = obj match {
                  case Super() => Var("super").withLocOf(obj)
                  case _ => obj
                }
                rcdSel(realPrefix, fieldName)
              }
          }
        obj match {
          case Var(name) if name.isCapitalized && ctx.tyDefs.isDefinedAt(name) => // explicit retrieval
            ctx.getMth(S(name), fieldName.name) match {
              case S(mth_ty) => mth_ty.toPT.instantiate
              case N =>
                err(msg"Class ${name} has no method ${fieldName.name}", term.toLoc)
                mthCallOrSel(obj, fieldName)
            }
          case _ => mthCallOrSel(obj, fieldName)
        }
      case Let(isrec, nme, rhs, bod) =>
        if (newDefs && !isrec) {
          // if (isrec) ???
          val rhs_ty = typeTerm(rhs)
          val newCtx = ctx.nest
          newCtx += nme.name -> VarSymbol(rhs_ty, nme)
          typeTerm(bod)(newCtx, raise, vars, genLambdas)
        } else {
          val n_ty = typeLetRhs(isrec, nme.name, rhs)
          val newCtx = ctx.nest
          newCtx += nme.name -> VarSymbol(n_ty, nme)
          typeTerm(bod)(newCtx, raise, vars, genLambdas)
        }
      // case Blk(s :: stmts) =>
      //   val (newCtx, ty) = typeStatement(s)
      //   typeTerm(Blk(stmts))(newCtx, lvl, raise)
      case b @ Blk(stmts) =>
        if (newDefs) {
          val ttu = typeTypingUnit(TypingUnit(stmts), S(b))
          // TODO check unused defs
          ttu.result.getOrElse(UnitType)
        } else typeTerms(stmts, false, Nil)(ctx.nest, raise, prov, vars, genLambdas)
      case Bind(l, r) =>
        val l_ty = typeMonomorphicTerm(l)
        val newCtx = ctx.nest // so the pattern's context don't merge with the outer context!
        val r_ty = typePattern(r)(newCtx, raise)
        ctx ++= newCtx.env
        con(l_ty, r_ty, r_ty)
      case Test(l, r) =>
        val l_ty = typeMonomorphicTerm(l)
        val newCtx = ctx.nest
        val r_ty = typePattern(r)(newCtx, raise) // TODO make these bindings flow
        con(l_ty, r_ty, TopType)
        BoolType
      case With(t, rcd) =>
        val t_ty = typeMonomorphicTerm(t)
        val rcd_ty = typeMonomorphicTerm(rcd)
        (t_ty without rcd.fields.iterator.map(_._1).toSortedSet) & (rcd_ty, prov)
      case CaseOf(s, cs) =>
        val s_ty = typeMonomorphicTerm(s)
        if (newDefs) con(s_ty, ObjType.withProv(prov), TopType)
        val (tys, cs_ty) = typeArms(s |>? {
          case v: Var => v
          case Asc(v: Var, _) => v
        }, cs)
        val req = tys.foldRight(BotType: SimpleType) {
          case ((a_ty, tv), req) => a_ty & tv | req & a_ty.neg()
        }
        con(s_ty, req, cs_ty)
      case elf: If =>
        try typeTerm(desugarIf(elf)) catch {
          case e: ucs.DesugaringException => err(e.messages)
        }
      case New(S((nmedTy, trm)), TypingUnit(Nil)) =>
        typeMonomorphicTerm(App(Var(nmedTy.base.name).withLocOf(nmedTy), trm))
      case New(base, args) => err(msg"Currently unsupported `new` syntax", term.toCoveringLoc)
      case TyApp(_, _) =>
        // ??? // TODO handle
        err(msg"Type application syntax is not yet supported", term.toLoc)
      case Where(bod, sts) =>
        typeTerms(sts :+ bod, false, Nil, allowPure = true)
      case Forall(vs, bod) =>
        ctx.poly { implicit ctx =>
          val newVars = vs.map {
            case tv @ TypeVar(R(nme), _) => nme ->
              SkolemTag(lvl, freshVar(tp(tv.toLoc, "quantified type variable"), N, S(nme)))(
                tp(tv.toLoc, "rigid type variable"))
            case _ => die
          }
          vars ++ newVars |> { implicit vars =>
            implicit val genLambdas: GenLambdas = false
            typeTerm(bod)
          }
        }
      case Inst(bod) =>
        val bod_ty = typePolymorphicTerm(bod)
        var founPoly = false
        def go(ty: ST): ST = ty.unwrapAll match {
          case pt: PolymorphicType =>
            founPoly = true
            implicit val shadows: Shadows = Shadows.empty
            go(pt.instantiate)
          case _ => ty
        }
        val res = go(bod_ty)
        if (!founPoly) warn(msg"Inferred type `${bod_ty.expPos}` of this ${
          bod_ty.prov.desc} cannot be instantiated", prov.loco)
        res
      case Eqn(lhs, rhs) =>
        err(msg"Unexpected equation in this position", term.toLoc)
    }
  }(r => s"$lvl. : ${r}")
  
  def typeArms(scrutVar: Opt[Var], arms: CaseBranches)
      (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType], genLambdas: GenLambdas)
      : Ls[SimpleType -> SimpleType] -> SimpleType = arms match {
    case NoCases => Nil -> BotType
    case Wildcard(b) =>
      val fv = freshVar(tp(arms.toLoc, "wildcard pattern"), N)
      val newCtx = ctx.nest
      scrutVar match {
        case Some(v) =>
          newCtx += v.name -> VarSymbol(fv, v)
          val b_ty = typeTerm(b)(newCtx, raise, vars, genLambdas)
          (fv -> TopType :: Nil) -> b_ty
        case _ =>
          (fv -> TopType :: Nil) -> typeTerm(b)
      }
    case Case(pat, bod, rest) =>
      val (tagTy, patTy) : (ST, ST) = pat match {
        case lit: Lit =>
          val t = ClassTag(lit,
            if (newDefs) lit.baseClassesNu else lit.baseClassesOld)(tp(pat.toLoc, "literal pattern"))
          t -> t
        case v @ Var(nme) =>
          val tpr = tp(pat.toLoc, "type pattern")
          ctx.tyDefs.get(nme) match {
            case None =>
              val bail = () => {
                val e = ClassTag(ErrTypeId, Set.empty)(tpr)
                return ((e -> e) :: Nil) -> e
              }
              ctx.get(nme) match {
                case S(lti: LazyTypeInfo) =>
                  if ((lti.kind isnt Cls) && (lti.kind isnt Mod) && (lti.kind isnt Trt))
                    err(msg"can only match on classes and traits", pat.toLoc)(raise)
                  
                  val prov = tp(pat.toLoc, "class pattern")
                  
                  lti match {
                    case dti: DelayedTypeInfo =>
                      val tag = clsNameToNomTag(dti.decl match { case decl: NuTypeDef => decl; case _ => die })(prov, ctx)
                      val ty =
                        RecordType.mk(dti.tparams.map {
                          case (tn, tv, vi) =>
                            val nv = freshVar(tv.prov, S(tv), tv.nameHint)
                            (Var(nme+"#"+tn.name).withLocOf(tn),
                              FieldType.mk(vi.getOrElse(VarianceInfo.in), nv, nv)(provTODO))
                        })(provTODO)
                      println(s"Match arm $nme: $tag & $ty")
                      tag -> ty
                    case CompletedTypeInfo(cls: TypedNuCls) =>
                      val tag = clsNameToNomTag(cls.td)(prov, ctx)
                      val ty =
                        RecordType.mk(cls.tparams.map {
                          case (tn, tv, vi) =>
                            val nv = freshVar(tv.prov, S(tv), tv.nameHint)
                            (Var(nme+"#"+tn.name).withLocOf(tn),
                              FieldType.mk(vi.getOrElse(cls.varianceOf(tv)), nv, nv)(provTODO))
                        })(provTODO)
                      println(s"Match arm $nme: $tag & $ty")
                      tag -> ty
                    case CompletedTypeInfo(_) => bail()
                  }
                  
                case _ =>
                  err("type identifier not found: " + nme, pat.toLoc)(raise)
                  bail()
              }
            case Some(td) =>
              td.kind match {
                case Als | Mod | Mxn => val t = err(msg"can only match on classes and traits", pat.toLoc)(raise); t -> t
                case Cls => val t = clsNameToNomTag(td)(tp(pat.toLoc, "class pattern"), ctx); t -> t
                case Trt => val t = trtNameToNomTag(td)(tp(pat.toLoc, "trait pattern"), ctx); t -> t
              }
          }
      }
      val newCtx = ctx.nest
      val (req_ty, bod_ty, (tys, rest_ty)) = scrutVar match {
        case S(v) =>
          if (newDefs) {
            newCtx += v.name -> VarSymbol(tagTy & patTy, v)
            val bod_ty = typeTerm(bod)(newCtx, raise, vars, genLambdas)
            (tagTy -> patTy, bod_ty, typeArms(scrutVar, rest))
          } else {
            val tv = freshVar(tp(v.toLoc, "refined scrutinee"), N,
              // S(v.name), // this one seems a bit excessive
            )
            newCtx += v.name -> VarSymbol(tv, v)
            val bod_ty = typeTerm(bod)(newCtx, raise, vars, genLambdas)
            (patTy -> tv, bod_ty, typeArms(scrutVar, rest))
          }
        case N =>
          val bod_ty = typeTerm(bod)(newCtx, raise, vars, genLambdas)
          (tagTy -> TopType, bod_ty, typeArms(scrutVar, rest))
      }
      (req_ty :: tys) -> (bod_ty | rest_ty)
  }
  
  def typeTerms(term: Ls[Statement], rcd: Bool, fields: List[Opt[Var] -> SimpleType], allowPure: Bool = false)
        (implicit ctx: Ctx, raise: Raise, prov: TypeProvenance, vars: Map[Str, SimpleType], genLambdas: GenLambdas): SimpleType
      = term match {
    case (trm @ Var(nme)) :: sts if rcd => // field punning
      typeTerms(Tup(S(trm) -> Fld(false, false, trm) :: Nil) :: sts, rcd, fields)
    case Blk(sts0) :: sts1 => typeTerms(sts0 ::: sts1, rcd, fields)
    case Tup(Nil) :: sts => typeTerms(sts, rcd, fields)
    case Tup((no, Fld(tmut, _, trm)) :: ofs) :: sts =>
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
            new TypeVariable(lvl, Nil, Nil, N)(prov)//.tap(ctx += nme -> _)
          
          // constrain(ty, t_ty)(raise, prov)
          constrain(t_ty, ty)(raise, prov, ctx)
          ctx += nme.name -> VarSymbol(t_ty, nme)
          
          t_ty
          // ty
          // ComposedType(false, t_ty, ty)(prov)
          // ComposedType(true, t_ty, ty)(prov) // loops!
          
        case S(nme) =>
          ctx += nme.name -> VarSymbol(ty, nme)
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
      val newBindings = desug.flatMap(typeStatement(_, allowPure).toOption)
      ctx ++= newBindings.iterator.flatten.map(nt => nt._1 -> VarSymbol(nt._2, Var(nt._1)))
      typeTerms(sts, rcd, fields)
    case Nil =>
      if (rcd) {
        val fs = fields.reverseIterator.zipWithIndex.map {
          case ((S(n), t), i) =>
            n -> t.toUpper(noProv)
          case ((N, t), i) =>
            // err("Missing name for record field", t.prov.loco)
            warn("Missing name for record field", t.prov.loco)
            (Var("_" + (i + 1)), t.toUpper(noProv))
        }.toList
        RecordType.mk(fs)(prov)
      } else TupleType(fields.reverseIterator.mapValues(_.toUpper(noProv)))(prov)
  }

  def getNewVarName(prefix: String, nonValidVars: Set[Var])(implicit raise: Raise): String = {
    // we check all possibe prefix_num combination, till we found one that is not in the nonValidVars
    val ints = LazyList.from(1)
    val result = ints.find(index => {
      !nonValidVars.contains(Var(prefix + "_" + index))
    })
    result match {
      case Some(index) => 
        prefix + "_" + index
      case N => 
        "ERROR" // unreachable, cause there must be an possible NewVar
    }
  }

  def freeVars(ctx: Ctx, t: Term): Set[Var] = {
    t match {
      case App(lhs, rhs) => 
        freeVars(ctx, lhs) ++ freeVars(ctx, rhs)
      case v @ Var(_) => 
        Set(v)
      case Tup(fields) =>
        fields.map(f => freeVars(ctx, f._2.value))
                    .flatMap(x => x)
                    .toSet
      case _ =>
        Set() // TODO
    }
  }

  def desugarNamedArgs(term: Term, f: Term, a: Tup, argsList: List[Var])
  (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType]): SimpleType = {
    def rec (as: List[(String -> Fld) -> Boolean], acc: Map[String, Either[Var, Term]]): Term = {
      as match {
        case ((v, fld), isNamed) :: tail =>
          if (isNamed) {
            fld.value match {
              case lit: Lit =>
                rec(tail, acc + (v -> R(fld.value)))
              case varr: Var =>
                rec(tail, acc + (v -> R(fld.value)))
              case _ =>
                val newVar = Var(getNewVarName(v, freeVars(ctx, a)))
                Let(false, newVar, fld.value, rec(tail, acc + (v -> L(newVar))))
            }        
          } else {
            rec(tail, acc + (v -> R(fld.value)))
          }
        case Nil =>
          val y: Term = Tup(argsList.map(x => 
            acc.get(x.name) match {
              case Some(v) =>
                v match {
                  case Left(v) =>
                    (None, Fld(false, false, v))
                  case Right(t) => 
                    (None, Fld(false, false, t))
                }
              case None =>
                err(s"name ${x} is missed in function call", a.toLoc)
                (None, Fld(false, false, Var("error")))
            }
          ))
          App(f, y)
      }
    }
    val hasDefined = a.fields.exists(x => x._1.isDefined)
    val hasEmpty = a.fields.exists(x => x._1.isEmpty)
    val areArgsMisplaced = a.fields.indexWhere(x => x._1.isDefined) < a.fields.lastIndexWhere(x => x._1.isEmpty)
    if (hasDefined &&
        hasEmpty && 
        areArgsMisplaced) {
      err("the unnamed args should appear first when using named args!", a.toLoc) 
    } else 
      a.fields.sizeCompare(argsList) match {
        case 0 =>
          val as = a.fields.zipWithIndex.map{ case(x, idx) =>
          x._1 match {
            case Some(value) => 
              ((value.name, x._2), true)
            case N =>
              ((argsList(idx).name, x._2), false)
          }}
          if (as.groupBy(x => x._1._1).sizeCompare(argsList) < 0) {
            as.groupBy(x => x._1._1).foreach(
              x =>
                if (x._2.sizeCompare(1) > 0) {
                  err(s"parameter ${x._1} is duplicate!", a.toLoc)
                }
            )
          }
          val desugared = rec(as, Map())
          println("Desugared is here => " + desugared)
          term.desugaredTerm = S(desugared)
          typeTerm(desugared)(ctx = ctx, raise = raise, vars = vars, genLambdas = false)
        case _ =>
          err("number of parameters dosen't match with the function signature!", a.toLoc) 
      }
  }
  
  /** Convert an inferred SimpleType into the immutable Type representation. */
  def expandType(st: TypeLike, stopAtTyVars: Bool = false)(implicit ctx: Ctx): mlscript.TypeLike = {
    val expandType = ()
    
    var bounds: Ls[TypeVar -> Bounds] = Nil
    
    val seenVars = mutable.Set.empty[TV]
    
    def field(ft: FieldType)(implicit ectx: ExpCtx): Field = ft match {
      case FieldType(S(l: TV), u: TV) if l === u =>
        val res = go(u)
        Field(S(res), res) // TODO improve Field
      case f =>
        Field(f.lb.map(go), go(f.ub))
    }
    
    class ExpCtx(val tps: Map[TV, TN]) {
      def apply(tparams: Ls[(TN, TV, Opt[VarianceInfo])]): ExpCtx =
        new ExpCtx(tps ++ tparams.iterator.map{case (tn, tv, vi) => tv -> tn})
    }
    
    def mkTypingUnit(thisTy: ST, members: Map[Str, NuMember])(implicit ectx: ExpCtx): TypingUnit = {
      val sorted = members.toList.sortBy(_._1)
      TypingUnit(sorted.collect {
        case (_, d: TypedNuFun) => goDecl(d)
        case (_, d: TypedNuTypeDef) => goDecl(d)
      })
    }
    def goDecl(d: NuMember)(implicit ectx: ExpCtx): NuDecl = d match {
      case TypedNuAls(level, td, tparams, body) =>
        ectx(tparams) |> { implicit ectx =>
          NuTypeDef(td.kind, td.nme, td.tparams, N, N, S(go(body)), Nil, N, N, TypingUnit(Nil))(
            td.declareLoc, td.abstractLoc)
        }
      case TypedNuMxn(level, td, thisTy, superTy, tparams, params, members) =>
        ectx(tparams) |> { implicit ectx =>
          NuTypeDef(td.kind, td.nme, td.tparams,
            S(Tup(params.map(p => N -> Fld(false, false, Asc(p._1, go(p._2.ub)))))),
            N,//TODO
            N,
            Nil, // TODO mixin parents?
            Option.when(!(TopType <:< superTy))(go(superTy)),
            Option.when(!(TopType <:< thisTy))(go(thisTy)),
            mkTypingUnit(thisTy, members))(td.declareLoc, td.abstractLoc)
        }
      case TypedNuCls(level, td, tparams, params, members, thisTy, sign, ihtags, ptps) =>
        ectx(tparams) |> { implicit ectx =>
          NuTypeDef(td.kind, td.nme, td.tparams,
            Opt.when(td.params.isDefined)(Tup(params.map(p => N -> Fld(false, false, Asc(p._1, go(p._2.ub)))))),
            td.ctor,
            Option.when(!(TopType <:< sign))(go(sign)),
            ihtags.toList.sorted.map(_.toVar), // TODO provide targs/args
            N,//TODO
            Option.when(!(TopType <:< thisTy))(go(thisTy)),
            mkTypingUnit(thisTy, members))(td.declareLoc, td.abstractLoc)
          }
      case TypedNuTrt(level, td, tparams, members, thisTy, sign, ihtags, ptps) => 
        ectx(tparams) |> { implicit ectx =>
          NuTypeDef(td.kind, td.nme, td.tparams,
            N,
            td.ctor,
            Option.when(!(TopType <:< sign))(go(sign)),
            ihtags.toList.sorted.map(_.toVar), // TODO provide targs/args
            N,//TODO
            Option.when(!(TopType <:< thisTy))(go(thisTy)),
            mkTypingUnit(thisTy, members))(td.declareLoc, td.abstractLoc)
          }
      case tf @ TypedNuFun(level, fd, bodyTy) =>
        NuFunDef(fd.isLetRec, fd.nme, Nil, R(go(tf.typeSignature)))(fd.declareLoc, fd.signature, fd.outer)
      case p: NuParam =>
        ??? // TODO
      case TypedNuDummy(d) =>
        ??? // TODO
    }
    def goLike(ty: TypeLike)(implicit ectx: ExpCtx): mlscript.TypeLike = ty match {
      case ty: SimpleType =>
        val res = go(ty)
        // if (bounds.isEmpty) res
        // else Constrained(res, bounds, Nil)
        res
      case OtherTypeLike(tu) =>
        val mems = tu.implementedMembers.map(goDecl)
        Signature(mems, tu.result.map(go))
    }
    
    def go(st: SimpleType)(implicit ectx: ExpCtx): Type =
            // trace(s"expand $st") {
          st.unwrapProvs match {
        case tv: TypeVariable if stopAtTyVars => tv.asTypeVar
        case tv: TypeVariable => ectx.tps.getOrElse(tv, {
          val nv = tv.asTypeVar
          if (!seenVars(tv)) {
            seenVars += tv
            tv.assignedTo match {
              case S(ty) =>
                val b = go(ty)
                bounds ::= nv -> Bounds(b, b)
              case N =>
                val l = go(tv.lowerBounds.foldLeft(BotType: ST)(_ | _))
                val u = go(tv.upperBounds.foldLeft(TopType: ST)(_ &- _))
                if (l =/= Bot || u =/= Top)
                  bounds ::= nv -> Bounds(l, u)
            }
          }
          nv
        })
        case FunctionType(l, r) => Function(go(l), go(r))
        case ct @ ComposedType(true, l, r) =>
          if (ct >:< (TrueType | FalseType)) TN("Bool") // TODO should rather be done in TypeSimplifier
          else Union(go(l), go(r))
        case ComposedType(false, l, r) => Inter(go(l), go(r))
        case RecordType(fs) => Record(fs.mapValues(field))
        case TupleType(fs) => Tuple(fs.mapValues(field))
        case ArrayType(FieldType(None, ub)) => AppliedType(TypeName("Array"), go(ub) :: Nil)
        case ArrayType(f) =>
          val f2 = field(f)
          AppliedType(TypeName("MutArray"), Bounds(f2.in.getOrElse(Bot), f2.out) :: Nil)
        case SpliceType(elems) => Splice(elems.map { 
              case L(l) => L(go(l)) 
              case R(v) => R(Field(v.lb.map(go(_)), go(v.ub))) })
        case NegType(t) => Neg(go(t))
        case ExtrType(true) => Bot
        case ExtrType(false) => Top
        case WithType(base, rcd) =>
          WithExtension(go(base), Record(rcd.fields.mapValues(field)))
        case ProxyType(und) => go(und)
        case obj: ObjectTag => obj.id match {
          case Var(n) =>
            if (primitiveTypes.contains(n) // primitives like `int` are internally maintained as class tags
              || n === "this" // `this` type
            ) TypeName(n)
            else TypeTag(n.capitalize)
          case lit: Lit => Literal(lit)
        }
        case SkolemTag(_, tv) => tv.nameHint match {
            case S(n) if
                n.isCapitalized // rigid type params like A in class Foo[A]
              => TypeName(n)
            case _ => go(tv)
          }
        case ex @ Extruded(p, SkolemTag(_, tv)) =>
          if (p) tv.asPosExtrudedTypeVar else tv.asNegExtrudedTypeVar
        case TypeRef(td, Nil) => td
        case tr @ TypeRef(td, targs) => AppliedType(td, tr.mapTargs(S(true)) {
          case ta @ ((S(true), TopType) | (S(false), BotType)) => Bounds(Bot, Top)
          case (_, ty) => go(ty)
        })
        case TypeBounds(lb, ub) => Bounds(go(lb), go(ub))
        case Without(base, names) => Rem(go(base), names.toList)
        case Overload(as) => as.map(go).reduce(Inter)
        case PolymorphicType(lvl, bod) =>
          val boundsSize = bounds.size
          val b = go(bod)
          
          // This is not completely correct: if we've already traversed TVs as part of a previous sibling PolymorphicType,
          // the bounds of these TVs won't be registered again...
          // FIXME in principle we'd want to compute a transitive closure...
          val newBounds = bounds.reverseIterator.drop(boundsSize).toBuffer
          
          val qvars = bod.varsBetween(lvl, MaxLevel).iterator
          val ftvs = b.freeTypeVariables ++
            newBounds.iterator.map(_._1) ++
            newBounds.iterator.flatMap(_._2.freeTypeVariables)
          val fvars = qvars.filter(tv => ftvs.contains(tv.asTypeVar))
          if (fvars.isEmpty) b else
            PolyType(fvars.map(_.asTypeVar pipe (R(_))).toList, b)
        case ConstrainedType(cs, bod) =>
          val (ubs, others1) = cs.groupMap(_._1)(_._2).toList.partition(_._2.sizeIs > 1)
          val lbs = others1.mapValues(_.head).groupMap(_._2)(_._1).toList
          val bounds = (ubs.mapValues(_.reduce(_ &- _)) ++ lbs.mapValues(_.reduce(_ | _)).map(_.swap))
          val procesased = bounds.map { case (lo, hi) => Bounds(go(lo), go(hi)) }
          Constrained(go(bod), Nil, procesased)
        
        // case DeclType(lvl, info) =>
          
    }
    // }(r => s"~> $r")
    
    val res = goLike(st)(new ExpCtx(Map.empty))
    if (bounds.isEmpty) res
    else Constrained(res, bounds, Nil)
    
    // goLike(st)
  }
  
  
  private var curUid: Int = 0
  def nextUid: Int = {
    val res = curUid
    curUid += 1
    res
  }
}
