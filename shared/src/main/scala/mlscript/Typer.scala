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
class Typer(var dbg: Boolean, var verbose: Bool, var explainErrors: Bool)
    extends TypeDefs with TypeSimplifier {
  
  def funkyTuples: Bool = false
  
  type Raise = Diagnostic => Unit
  type Binding = Str -> TypeScheme
  type Bindings = Map[Str, TypeScheme]
  
  /** Keys of `mthEnv`:
    * `L` represents the inferred types of method definitions. The first value is the parent name,
    *   and the second value is the method name.
    * `R` represents the actual method types.
    *   The first optional value is the parent name, with `N` representing implicit calls,
    *   and the second value is the method name.
    *   (See the case for `Sel` in `typeTerm` for documentation on explicit vs. implicit calls.)
    * The public helper functions should be preferred for manipulating `mthEnv`
   */
  case class Ctx(parent: Opt[Ctx], env: MutMap[Str, TypeInfo], mthEnv: MutMap[(Str, Str) \/ (Opt[Str], Str), MethodType],
      lvl: Int, inPattern: Bool, tyDefs: Map[Str, TypeDef]) { // <-- last tyDefs
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
    def nextLevel: Ctx = copy(lvl = lvl + 1)
    private val abcCache: MutMap[Str, Set[Var]] = MutMap.empty
    // USE THIS!!!
    def allBaseClassesOf(name: Str): Set[Var] = abcCache.getOrElseUpdate(name,
      tyDefs.get(name).fold(Set.empty[Var])(_.allBaseClasses(this)(Set.empty)))
  }
  object Ctx {
    def init: Ctx = Ctx(
      parent = N,
      env = MutMap.from(builtinBindings),
      mthEnv = MutMap.empty,
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
    {
      val tv = freshVar(noProv)(1)
      TypeDef(Als, TypeName("Array"), List(TypeName("A") -> tv), Nil, ArrayType(tv)(noProv), Nil, Nil, Set.empty, N)
    } ::
    Nil
  val primitiveTypes: Set[Str] =
    builtinTypes.iterator.filter(_.kind is Cls).map(_.nme.name).flatMap(n => n :: n.capitalize :: Nil).toSet
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
      "toString" -> fun(singleTup(TopType), StrType)(noProv),
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
  
  
  /* Parameters `vars` and `newDefsInfo` are used for typing `TypeName`s.
   * If the key is found in `vars`, the type is typed as the associated value. Use case: type arguments.
   * If the key is found in `newDefsInfo`, the type is typed as a `TypeRef`, where the associated value
   *   is used to check the kind of the definition and the number of type arguments expected. Use case:
   *   for typing bodies of type definitions with mutually recursive references. */
  def typeType(ty: Type, simplify: Bool = true)
        (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType]): SimpleType =
    typeType2(ty, simplify)._1
  
  /* Also returns an iterable of `TypeVariable`s instantiated when typing `TypeVar`s.
   * Useful for instantiating them by substitution when expanding a `TypeRef`. */
  def typeType2(ty: Type, simplify: Bool = true)
        (implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType],
        newDefsInfo: Map[Str, (TypeDefKind, Int)] = Map.empty): (SimpleType, Iterable[TypeVariable]) =
      trace(s"$lvl. Typing type $ty") {
    println(s"vars=$vars newDefsInfo=$newDefsInfo")
    val typeType2 = ()
    def typeNamed(loc: Opt[Loc], name: Str): (() => ST) \/ (TypeDefKind, Int) =
      newDefsInfo.get(name)
        .orElse(ctx.tyDefs.get(name).map(td => (td.kind, td.tparamsargs.size)))
        .toRight(() => err("type identifier not found: " + name, loc)(raise))
    val localVars = mutable.Map.empty[TypeVar, TypeVariable]
    def tyTp(loco: Opt[Loc], desc: Str, originName: Opt[Str] = N) =
      TypeProvenance(loco, desc, originName, isType = true)
    def rec(ty: Type)(implicit ctx: Ctx, recVars: Map[TypeVar, TypeVariable]): SimpleType = ty match {
      case Top => ExtrType(false)(tyTp(ty.toLoc, "top type"))
      case Bot => ExtrType(true)(tyTp(ty.toLoc, "bottom type"))
      case Bounds(lb, ub) => TypeBounds(rec(lb), rec(ub))(tyTp(ty.toLoc,
        if (lb === Bot && ub === Top) "type wildcard" else "type bounds"))
      // case Tuple(fields) => TupleType(fields.map(f => f._1 -> rec(f._2)))(tp(ty.toLoc, "tuple type"))
      case Tuple(fields) => TupleType(fields.map(f => f._1 -> rec(f._2)))(fields match {
        case Nil | ((N, _) :: Nil) => noProv
        case _ => tyTp(ty.toLoc, "tuple type")
      })
      case Arr(inner) => ArrayType(rec(inner))(tp(ty.toLoc, "array type"))
      case Inter(lhs, rhs) => (if (simplify) rec(lhs) & (rec(rhs), _: TypeProvenance)
          else ComposedType(false, rec(lhs), rec(rhs)) _
        )(tyTp(ty.toLoc, "intersection type"))
      case Union(lhs, rhs) => (if (simplify) rec(lhs) | (rec(rhs), _: TypeProvenance)
          else ComposedType(true, rec(lhs), rec(rhs)) _
        )(tyTp(ty.toLoc, "union type"))
      case Neg(t) => NegType(rec(t))(tyTp(ty.toLoc, "type negation"))
      case Record(fs) => 
        val prov = tyTp(ty.toLoc, "record type")
        fs.groupMap(_._1.name)(_._1).foreach { case s -> fieldNames if fieldNames.size > 1 => err(
            msg"Multiple declarations of field name ${s} in ${prov.desc}" -> ty.toLoc
              :: fieldNames.map(tp => msg"Declared at" -> tp.toLoc))(raise)
          case _ =>
        }
        RecordType.mk(fs.map { nt =>
          if (nt._1.name.isCapitalized)
            err(msg"Field identifiers must start with a small letter", nt._1.toLoc)(raise)
          nt._1 -> rec(nt._2)
        })(prov)
      case Function(lhs, rhs) => FunctionType(rec(lhs), rec(rhs))(tyTp(ty.toLoc, "function type"))
      case WithExtension(b, r) => WithType(rec(b),
        RecordType(r.fields.mapValues(rec))(tyTp(r.toLoc, "extension record")))(tyTp(ty.toLoc, "extension type"))
      case Literal(lit) => ClassTag(lit, lit.baseClasses)(tyTp(ty.toLoc, "literal type"))
      case TypeName("this") =>
        ctx.env.getOrElse("this", err(msg"undeclared this" -> ty.toLoc :: Nil)) match {
          case AbstractConstructor(_, _) => ??? // how to handle this case?
          case t: TypeScheme => t.instantiate
        }
      case tn @ TypeName(name) =>
        val tyLoc = ty.toLoc
        val tpr = tyTp(tyLoc, "type reference")
        vars.get(name).getOrElse {
          typeNamed(tyLoc, name) match {
            case R((_, tpnum)) =>
              if (tpnum =/= 0) {
                err(msg"Type $name takes parameters", tyLoc)(raise)
              } else TypeRef(tn, Nil)(tpr)
            case L(e) =>
              if (name.isEmpty || !name.head.isLower) e()
              else (typeNamed(tyLoc, name.capitalize), ctx.tyDefs.get(name.capitalize)) match {
                case (R((kind, _)), S(td)) => kind match {
                  case Cls => clsNameToNomTag(td)(tyTp(tyLoc, "class tag"), ctx)
                  case Trt => trtNameToNomTag(td)(tyTp(tyLoc, "trait tag"), ctx)
                  case Als => err(
                    msg"Type alias ${name.capitalize} cannot be used as a type tag", tyLoc)(raise)
                }
                case _ => e()
              }
          }
        }
      case tv: TypeVar =>
        // assert(ty.toLoc.isDefined)
        recVars.getOrElse(tv,
          localVars.getOrElseUpdate(tv, freshVar(noProv, tv.identifier.toOption))
            .withProv(tyTp(ty.toLoc, "type variable")))
      case AppliedType(base, targs) =>
        val prov = tyTp(ty.toLoc, "applied type reference")
        typeNamed(ty.toLoc, base.name) match {
          case R((_, tpnum)) =>
            val realTargs = if (targs.size === tpnum) targs.map(rec) else {
              err(msg"Wrong number of type arguments – expected ${tpnum.toString}, found ${
                  targs.size.toString}", ty.toLoc)(raise)
              (targs.iterator.map(rec) ++ Iterator.continually(freshVar(noProv))).take(tpnum).toList
            }
            TypeRef(base, realTargs)(prov)
          case L(e) => e()
        }
      case Recursive(uv, body) =>
        val tv = freshVar(tyTp(ty.toLoc, "local type binding"), uv.identifier.toOption)
        val bod = rec(body)(ctx, recVars + (uv -> tv))
        tv.upperBounds ::= bod
        tv.lowerBounds ::= bod
        tv
      case Rem(base, fs) => Without(rec(base), fs.toSortedSet)(tyTp(ty.toLoc, "field removal type"))
    }
    (rec(ty)(ctx, Map.empty), localVars.values)
  }(r => s"=> ${r._1} | ${r._2.mkString(", ")}")
  
  def typePattern(pat: Term)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType] = Map.empty): SimpleType =
    typeTerm(pat)(ctx.copy(inPattern = true), raise, vars)
  
  
  def typeStatement(s: DesugaredStatement, allowPure: Bool)
        (implicit ctx: Ctx, raise: Raise): PolymorphicType \/ Ls[Binding] = s match {
    case Def(false, Var("_"), L(rhs)) => typeStatement(rhs, allowPure)
    case Def(isrec, nme, L(rhs)) => // TODO reject R(..)
      if (nme.name === "_")
        err(msg"Illegal definition name: ${nme.name}", nme.toLoc)(raise)
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
      err(msg"Illegal position for this ${s.describe} statement.", s.toLoc)(raise)
      R(Nil)
  }
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: Str, rhs: Term)(implicit ctx: Ctx, raise: Raise,
      vars: Map[Str, SimpleType] = Map.empty): PolymorphicType = {
    val res = if (isrec) {
      val e_ty = freshVar(
        // It turns out it is better to NOT store a provenance here,
        //    or it will obscure the true provenance of constraints causing errors
        //    across recursive references.
        noProv
        // TypeProvenance(rhs.toLoc, "let-bound value")
      )(lvl + 1)
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
          v.toLoc)(raise)
      v.name
    }
  }
  object ValidPatVar {
    def unapply(v: Var)(implicit ctx: Ctx, raise: Raise): Opt[Str] =
      if (ctx.inPattern && v.isPatVar) {
        ctx.parent.dlof(_.get(v.name))(N) |>? { case S(ts: TypeScheme) => ts.instantiate(0).unwrapProxies } |>? {
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
        // Note: only look at ctx.env, and not the outer ones!
        ctx.env.get(nme).collect { case ts: TypeScheme => ts.instantiate }
          .getOrElse(new TypeVariable(lvl, Nil, Nil)(prov).tap(ctx += nme -> _))
      case v @ ValidVar(name) =>
        val ty = ctx.get(name).fold(err("identifier not found: " + name, term.toLoc): TypeScheme) {
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
          case ty: TypeScheme => ty
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
              :: fieldNames.map(tp => msg"Declared at" -> tp.toLoc))(raise)
          case _ =>
        }
        RecordType.mk(fs.map { case (n, t) => 
          if (n.name.isCapitalized)
            err(msg"Field identifiers must start with a small letter", term.toLoc)(raise)
          (n, typeTerm(t))
        })(prov)
      case tup: Tup if funkyTuples =>
        typeTerms(tup :: Nil, false, Nil)
      case Tup(fs) =>
        TupleType(fs.map(f => f._1 -> typeTerm(f._2)))(fs match {
          case Nil | ((N, _) :: Nil) => noProv
          case _ => tp(term.toLoc, "tuple literal")
        })
      case Subs(a, i) =>
        val t_a = typeTerm(a)
        val t_i = typeTerm(i)
        val res = freshVar(prov)
        con(t_a, ArrayType(res)(prov), t_a)
        con(t_i, IntType, t_i)
        res
      case Bra(false, trm: Blk) => typeTerm(trm)
      case Bra(rcd, trm @ (_: Tup | _: Blk)) if funkyTuples => typeTerms(trm :: Nil, rcd, Nil)
      case Bra(_, trm) => typeTerm(trm)
      case Blk((s: Term) :: Nil) => typeTerm(s)
      case Blk(Nil) => UnitType
      case pat if ctx.inPattern =>
        err(msg"Unsupported pattern shape${
          if (dbg) " ("+pat.getClass.toString+")" else ""}:", pat.toLoc)(raise)
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
        val funProv = tp(f.toCoveringLoc, "applied expression")
        val fun_ty = mkProxy(f_ty, funProv)
          // ^ This is mostly not useful, except in test Tuples.fun with `(1, true, "hey").2`
        val resTy = con(fun_ty, FunctionType(arg_ty, res)(
          prov
          // funProv // TODO: better?
          ), res)
        resTy
      case Sel(obj, fieldName) =>
        // Explicit method calls have the form `x.(Class.Method)`
        // Implicit method calls have the form `x.Method`
        //   If two unrelated classes define methods of the same name,
        //   implicit calls to this method are marked as ambiguous and are forbidden
        // Explicit method retrievals have the form `Class.Method`
        //   Returns a function expecting an additional argument of type `Class` before the method arguments
        def rcdSel(obj: Term, fieldName: Var) = {
          val o_ty = typeTerm(obj)
          val res = freshVar(prov)
          val obj_ty = mkProxy(o_ty, tp(obj.toCoveringLoc, "receiver"))
          con(obj_ty, RecordType.mk((fieldName, res) :: Nil)(prov), res)
        }
        def mthCallOrSel(obj: Term, fieldName: Var) = 
          (fieldName.name match {
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
              val o_ty = typeTerm(obj)
              val res = freshVar(prov)
              con(mth_ty.toPT.instantiate, FunctionType(singleTup(o_ty), res)(prov), res)
            case N =>
              if (fieldName.name.isCapitalized) err(msg"Method ${fieldName.name} not found", term.toLoc)
              else rcdSel(obj, fieldName) // TODO: no else?
          }
        trace(s"$lvl. Typing Sel") {
          obj match {
            case Var(name) if name.isCapitalized && ctx.tyDefs.isDefinedAt(name) => // explicit retrieval
              ctx.getMth(S(name), fieldName.name) match {
                case S(mth_ty) => trace(s"$lvl. instantiate method type ${mth_ty}") {
                  mth_ty.toPT.instantiate
                }(r => s"$lvl. instantiate result: ${r}")
                case N =>
                  err(msg"Class ${name} has no method ${fieldName.name}", term.toLoc)
                  mthCallOrSel(obj, fieldName)
              }
            case _ => mthCallOrSel(obj, fieldName)
          }
        }(r => s"$lvl. : ${r}")
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
        (t_ty without rcd.fields.iterator.map(_._1).toSortedSet) & (rcd_ty, prov)
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
              err("type identifier not found: " + nme, pat.toLoc)(raise)
              val e = ClassTag(ErrTypeId, Set.empty)(tpr)
              return ((e -> e) :: Nil) -> e
            case Some(td) =>
              td.kind match {
                case Als => err(msg"can only match on classes and traits", pat.toLoc)(raise)
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
  
  
  /** Convert an inferred SimpleType into the immutable Type representation.
    * Important precondition:
    *   We require that only polar variables
    *     (those occurring strictly positively or strictly negatively)
    *   have bounds.
    *   So typically, only recursive variables whose recursion is expressed through the bound
    *     (since other polar variables would be simplified away).
    *   This is because we re-tie the recursive knots by using hash consing
    *     in order to simplify recursive structures,
    *     after which we want to be able to discard the old leftover polar variables. */
  def expandType(st: SimpleType, polarity: Bool, stopAtTyVars: Bool = false): Type = {
    val expandType = ()
    
    // TODO improve/simplify? (take inspiration from other impls?)
    //    see: duplication of recursive.get(st_pol) logic
    
    val recursive = mutable.Map.empty[SimpleType -> Bool, TypeVar]
    def go(st: SimpleType, polarity: Boolean)(implicit inProcess: Set[SimpleType -> Bool]): Type =
      // trace(s"expand $st, $polarity  — $inProcess") {
        goImpl(st.unwrapProvs, polarity)
      // }(r => s"=> $r")
    def goImpl(st: SimpleType, polarity: Boolean)(implicit inProcess: Set[SimpleType -> Bool]): Type = {
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
              case None =>
                if (boundTypes.isEmpty)
                  boundTypes.foldLeft[Type](tv.asTypeVar)(mrg)
                else // see precondition
                  boundTypes.reduceOption(mrg).getOrElse(if (polarity) Bot else Top)
            }
          }
        case _ =>
          val res = st match {
            case FunctionType(l, r) => Function(go(l, !polarity), go(r, polarity))
            case ComposedType(true, l, r) => Union(go(l, polarity), go(r, polarity))
            case ComposedType(false, l, r) => Inter(go(l, polarity), go(r, polarity))
            case RecordType(fs) => Record(fs.map(nt => nt._1 -> go(nt._2, polarity)))
            case TupleType(fs) => Tuple(fs.map(nt => nt._1 -> go(nt._2, polarity)))
            case ArrayType(inner) => Arr(go(inner, polarity))
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
