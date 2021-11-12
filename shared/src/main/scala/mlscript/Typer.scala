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
    nme: Primitive,
    tparams: List[Primitive],
    body: Type,
    baseClasses: Set[Var],
    toLoc: Opt[Loc],
  ) {
    def allBaseClasses(ctx: Ctx)(implicit traversed: Set[Var]): Set[Var] =
      baseClasses.map(v => Var(v.name.toList.mapHead(_.toLower).mkString)) ++
        baseClasses.iterator.filterNot(traversed).flatMap(v =>
          ctx.tyDefs(v.name).allBaseClasses(ctx)(traversed + v))
  }
  
  case class Ctx(parent: Opt[Ctx], env: MutMap[Str, TypeScheme], lvl: Int, inPattern: Bool, tyDefs: Map[Str, TypeDef]) {
    def +=(b: Binding): Unit = env += b
    def ++=(bs: IterableOnce[Binding]): Unit = bs.iterator.foreach(+=)
    def get(name: Str): Opt[TypeScheme] = env.get(name) orElse parent.dlof(_.get(name))(N)
    def contains(name: Str): Bool = env.contains(name) || parent.exists(_.contains(name))
    def nest: Ctx = copy(Some(this), MutMap.empty)
    def nextLevel: Ctx = copy(lvl = lvl + 1)
  }
  object Ctx {
    def init: Ctx = Ctx(
      parent = N,
      env = MutMap.from(builtinBindings),
      lvl = 0,
      inPattern = false,
      tyDefs = Map.from(builtinTypes.map(t => t.nme.name -> t)))
  }
  implicit def lvl(implicit ctx: Ctx): Int = ctx.lvl
  
  import TypeProvenance.{apply => tp}
  def ttp(trm: Term, desc: Str = ""): TypeProvenance =
    TypeProvenance(trm.toLoc, if (desc === "") trm.describe else desc)
  
  val noProv: TypeProvenance = tp(N, "expression")
  
  val TopType: ExtrType = ExtrType(false)(noProv)
  val BotType: ExtrType = ExtrType(true)(noProv)
  val UnitType: PrimType = PrimType(Var("unit"), Set.empty)(noProv)
  val BoolType: PrimType = PrimType(Var("bool"), Set.empty)(noProv)
  val IntType: PrimType = PrimType(Var("int"), Set.single(Var("number")))(noProv)
  val DecType: PrimType = PrimType(Var("number"), Set.empty)(noProv)
  val StrType: PrimType = PrimType(Var("string"), Set.empty)(noProv)
  
  val ErrTypeId: SimpleTerm = Var("error")
  
  private val primTypes =
    List("unit" -> UnitType, "bool" -> BoolType, "int" -> IntType, "number" -> DecType, "string" -> StrType,
      "anything" -> TopType, "nothing" -> BotType)
  
  val builtinTypes: Ls[TypeDef] =
    TypeDef(Cls, Primitive("int"), Nil, Top, Set.single(Var("number")), N) ::
    TypeDef(Cls, Primitive("number"), Nil, Top, Set.empty, N) ::
    TypeDef(Cls, Primitive("bool"), Nil, Top, Set.empty, N) ::
    TypeDef(Cls, Primitive("string"), Nil, Top, Set.empty, N) ::
    TypeDef(Als, Primitive("anything"), Nil, Top, Set.empty, N) ::
    TypeDef(Als, Primitive("nothing"), Nil, Bot, Set.empty, N) ::
    Nil
  val builtinBindings: Bindings = {
    val tv = freshVar(noProv)(1)
    import FunctionType.{ apply => fun }
    Map(
      "true" -> BoolType,
      "false" -> BoolType,
      "document" -> BotType,
      "window" -> BotType,
      "not" -> fun(BoolType, BoolType)(noProv),
      "succ" -> fun(IntType, IntType)(noProv),
      "log" -> PolymorphicType(0, fun(tv, UnitType)(noProv)),
      "discard" -> PolymorphicType(0, fun(tv, UnitType)(noProv)),
      "add" -> fun(IntType, fun(IntType, IntType)(noProv))(noProv),
      "sub" -> fun(IntType, fun(IntType, IntType)(noProv))(noProv),
      "mul" -> fun(IntType, fun(IntType, IntType)(noProv))(noProv),
      "div" -> fun(IntType, fun(IntType, IntType)(noProv))(noProv),
      "sqrt" -> fun(IntType, IntType)(noProv),
      "lt" -> fun(IntType, fun(IntType, BoolType)(noProv))(noProv),
      "le" -> fun(IntType, fun(IntType, BoolType)(noProv))(noProv),
      "gt" -> fun(IntType, fun(IntType, BoolType)(noProv))(noProv),
      "ge" -> fun(IntType, fun(IntType, BoolType)(noProv))(noProv),
      "eq" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(v, fun(v, BoolType)(noProv))(noProv))
      },
      "ne" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(v, fun(v, BoolType)(noProv))(noProv))
      },
      "error" -> BotType,
      "+" -> fun(IntType, fun(IntType, IntType)(noProv))(noProv),
      "<" -> fun(IntType, fun(IntType, BoolType)(noProv))(noProv),
      "id" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(v, v)(noProv))
      },
      "if" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(BoolType, fun(v, fun(v, v)(noProv))(noProv))(noProv))
      },
    ) ++ primTypes ++ primTypes.map(p => "" + p._1.head.toUpper + p._1.tail -> p._2) // TODO settle on naming convention...
  }
  
  def clsNameToNomTag(td: TypeDef)(prov: TypeProvenance, ctx: Ctx): SimpleType =
    PrimType(Var(td.nme.name.head.toLower.toString + td.nme.name.tail), td.allBaseClasses(ctx)(Set.single(Var(td.nme.name))))(prov)
  
  def baseClassesOf(tyd: mlscript.TypeDef): Set[Var] =
    if (tyd.kind === Als) Set.empty else baseClassesOf(tyd.body)
  
  private def baseClassesOf(ty: Type): Set[Var] = ty match {
      case Inter(l, r) => baseClassesOf(l) ++ baseClassesOf(r)
      case Primitive(nme) => Set.single(Var(nme))
      case AppliedType(b, _) => baseClassesOf(b)
      case Record(_) => Set.empty
      case _: Union => Set.empty
      case _ => Set.empty // TODO TupleType?
    }
  
  def processTypeDefs(newDefs0: List[mlscript.TypeDef])(implicit ctx: Ctx, raise: Raise): Ctx = {
    var allDefs = ctx.tyDefs
    val newDefs = newDefs0.map { td =>
      implicit val prov: TypeProvenance = tp(td.toLoc, "data definition")
      val n = td.nme
      allDefs.get(n.name).foreach { other =>
        err(msg"Type '$n' is already defined.", td.nme.toLoc)
      }
      if (!n.name.head.isUpper) err(
        msg"Type names must start with a capital letter", n.toLoc)
      val td1 = TypeDef(td.kind, td.nme, td.tparams, td.body, baseClassesOf(td), td.toLoc)
      allDefs += n.name -> td1
      td1
    }
    import ctx.{tyDefs => oldDefs}
    // implicit val newCtx = ctx.copy(tyDefs = newDefs)
    ctx.copy(tyDefs = allDefs) |> { implicit ctx =>
      ctx.copy(tyDefs = oldDefs ++ newDefs.flatMap { td =>
        implicit val prov: TypeProvenance = tp(td.toLoc, "data definition")
        val n = td.nme
        val dummyTargs =
          td.tparams.map(p => freshVar(noProv/*TODO*/)(ctx.lvl + 1))
        val targsMap: Map[Str, SimpleType] = td.tparams.map(_.name).zip(dummyTargs).toMap
        val body_ty = typeType(td.body)(ctx.nextLevel, raise, targsMap)
        var fields = SortedMap.empty[Str, SimpleType]
        def checkCycleComputeFields(ty: SimpleType, computeFields: Bool)
            (implicit travsersed: Set[TypeDef]): Bool =
              trace(s"Cycle? $ty {${travsersed.mkString(",")}}"){ty match {
          case PrimType(_, _) => true
          case TypeRef(td, _) if travsersed(td) =>
            err(msg"illegal cycle involving type ${td.nme.name}", prov.loco)
            false
          case tr @ TypeRef(td, targs) => checkCycleComputeFields(tr.expand, computeFields)(travsersed + td)
          case ComposedType(_, l, r) => checkCycleComputeFields(l, computeFields) && checkCycleComputeFields(r, computeFields)
          case tv: TypeVariable => true
          case _: FunctionType => true
          case NegType(u) => checkCycleComputeFields(u, computeFields)
          case RecordType(fs) =>
            fs.foreach(f => fields += f._1 -> (fields.getOrElse(f._1, TopType) & f._2))
            true
          case _: ExtrType => true
          case p: ProxyType => checkCycleComputeFields(p.underlying, computeFields)
          case _ => ??? // TODO
        }}()
        val rightParents = td.kind match {
          case Als => checkCycleComputeFields(body_ty, computeFields = false)(Set.single(td))
          case Cls | Trt =>
            val parentsClasses = MutSet.empty[TypeRef]
            def checkParents(ty: SimpleType): Bool = ty match {
              // case PrimType(Var("string"), _) => true // Q: always?
              case PrimType(_, _) => true // Q: always?
              case tr @ TypeRef(td, _) =>
                td.kind match {
                  case Cls =>
                    parentsClasses.isEmpty || {
                      err(msg"cannot inherit from ${tr.defn.nme
                          } as this type already inherits from ${parentsClasses.head.defn.nme}",
                        prov.loco)
                      false
                    } tap (_ => parentsClasses += tr)
                  case Trt | Als => checkParents(tr.expand)
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
              case _: RecordType | _: ExtrType => true
              case p: ProxyType => checkParents(p.underlying)
              case _ => ??? // TODO
            }
            checkParents(body_ty) &&
                checkCycleComputeFields(body_ty, computeFields = td.kind === Cls)(Set.single(td)) && {
              val nomTag = clsNameToNomTag(td)(noProv/*FIXME*/, ctx)
              val fieldsRefined = RecordType(fields.iterator.map(f => f._1 -> freshVar(noProv)(1).tap(_.upperBounds ::= f._2)).toList)(noProv)
              val ctor = PolymorphicType(0, FunctionType(fieldsRefined, nomTag & fieldsRefined)(noProv/*FIXME*/))
              ctx += n.name -> ctor
              true
            }
        }
        def checkRegular(ty: SimpleType)(implicit reached: Map[Str, Ls[SimpleType]]): Bool = ty match {
          case tr @ TypeRef(defn, targs) => reached.get(defn.nme.name) match {
            case None => checkRegular(tr.expand)(reached + (defn.nme.name -> targs))
            case Some(tys) =>
              // TODO less syntactic check...
              if (tys =/= targs) {
                if (defn.nme.name === td.nme.name)
                  err(msg"Type definition is not regular: it occurs within itself as ${
                  expandType(tr).show
                  }, but is defined as ${
                  expandType(TypeRef(defn, dummyTargs)(noProv, ctx)).show
                  }", td.toLoc)(raise, noProv)
                false
              } else true
          }
          case _ => ty.children.forall(checkRegular)
        }
        // Note: this will end up going through some types several times... We could make sure to
        //    only go through each type once, but the error messages would be worse.
        if (rightParents && checkRegular(body_ty)(Map(n.name -> dummyTargs)))
          td.nme.name -> td :: Nil
        else Nil
      })
    }
  }
  // TODO record provenances!
  def typeType(ty: Type)(implicit ctx: Ctx, raise: Raise, vars: Map[Str, SimpleType]): SimpleType = {
    val typeType = ()
    def typeNamed(ty: Type, name: Str): Opt[TypeDef] = {
      val res = ctx.tyDefs.get(name)
      if (res.isEmpty)
        err("type identifier not found: " + name, ty.toLoc)(raise, noProv /*FIXME*/);
      res
    }
    val localVars = mutable.Map.empty[TypeVar, TypeVariable]
    def rec(ty: Type)(implicit ctx: Ctx): SimpleType = ty match {
      case Top => TopType
      case Bot => BotType
      case Tuple(fields) => TupleType(fields.map(f => f._1 -> rec(f._2)))(tp(ty.toLoc, "tuple type"))
      case Inter(lhs, rhs) => rec(lhs) & rec(rhs)
      case Union(lhs, rhs) => rec(lhs) | rec(rhs)
      case Applied(Primitive("~"), rhs) => NegType(rec(rhs))(tp(ty.toLoc, "type negation"))
      case Applied(lhs, rhs) => ??? // TODO
      case Record(fs) => RecordType.mk(fs.map(nt => nt._1 -> rec(nt._2)))(tp(ty.toLoc, "record type"))
      case Function(lhs, rhs) => FunctionType(rec(lhs), rec(rhs))(tp(ty.toLoc, "function type"))
      case Literal(lit) => PrimType(lit, Set.single(lit.baseClass))(tp(ty.toLoc, "literal type"))
      case Primitive(name) =>
        vars.get(name) orElse
          typeNamed(ty, name).flatMap(td =>
            if (td.tparams.nonEmpty) {
              err(msg"Type $name takes parameters", ty.toLoc)(raise, noProv /*FIXME*/)
              N
            } else S(TypeRef(td, Nil)(tp(ty.toLoc, "type reference"), ctx))
          ) getOrElse freshVar(noProv) // TODO use ty's prov
      case tv: TypeVar =>
        localVars.getOrElseUpdate(tv, new TypeVariable(ctx.lvl, Nil, Nil)(tp(ty.toLoc, "type variable")))
      case AppliedType(base, targs) => typeNamed(ty, base.name) match {
        case Some(td) =>
          val tpnum = td.tparams.size
          val realTargs = if (targs.size === tpnum) targs.map(rec) else {
            err(msg"Wrong number of type arguments – expected ${tpnum.toString}, found ${targs.size.toString}",
              ty.toLoc)(raise, noProv /*FIXME*/);
            (targs.iterator.map(rec) ++ Iterator.continually(freshVar(noProv)))
              .take(tpnum).toList
          }
          TypeRef(td,
            realTargs)(tp(ty.toLoc, "applied type reference"), ctx)
        case None => freshVar(noProv) // TODO use ty's prov
      }
      case Recursive(uv, body) => ??? // TODO
      case Rem(base, fs) => Without(rec(base), fs.map(_.name) // TODO Without should store Var's with locs...
        .toSet)(tp(ty.toLoc, "function type")) // TODO use ty's prov
    }
    rec(ty)
  }
  
  def typePattern(pat: Term)(implicit ctx: Ctx, raise: Raise): SimpleType =
    typeTerm(pat)(ctx.copy(inPattern = true), raise)
  
  
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
            prov = TypeProvenance(t.toLoc, t.describe))
      }
      L(PolymorphicType(0, ty))
    case _ =>
      err(msg"Illegal position for this ${s.describe} statement.", s.toLoc)(raise, noProv)
      R(Nil)
  }
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: Str, rhs: Term)
        (implicit ctx: Ctx, raise: Raise): PolymorphicType = {
    val res = if (isrec) {
      val e_ty = freshVar(TypeProvenance(rhs.toLoc, "let-bound value"))(lvl + 1)
      ctx += nme -> e_ty
      val ty = typeTerm(rhs)(ctx.nextLevel, raise)
      constrain(ty, e_ty)(raise, TypeProvenance(rhs.toLoc, "binding of " + rhs.describe))
      e_ty
    } else typeTerm(rhs)(ctx.nextLevel, raise)
    PolymorphicType(lvl, res)
  }
  
  def mkProxy(ty: SimpleType, prov: TypeProvenance): SimpleType = {
    ProxyType(ty)(prov)
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
          case S(_: VarType | PrimType(Var(v.name), _)) =>
            warn(msg"Variable name '${v.name}' already names a symbol in scope. " +
              s"If you want to refer to that symbol, you can use `scope.${v.name}`; " +
              s"if not, give your future readers a break and use another name :^)", v.toLoc)
        }
        ValidVar.unapply(v)
      } else N
  }
  
  /** Infer the type of a term. */
  def typeTerm(term: Term)(implicit ctx: Ctx, raise: Raise): SimpleType
        = trace(s"$lvl. Typing ${if (ctx.inPattern) "pattern" else "term"} $term") {
    implicit val prov: TypeProvenance = ttp(term)
    
    def con(lhs: SimpleType, rhs: SimpleType, res: SimpleType): SimpleType = {
      var alreadyReportedAnError = false
      constrain(lhs, rhs)({
        case err: TypeError if alreadyReportedAnError => () // silence further errors from this location
        case err: TypeError =>
          alreadyReportedAnError = true
          constrain(errType, res)(_ => (), noProv) // This is just to get error types leak into the result
          raise(err)
        case diag => raise(diag)
      }, prov)
      res
    }
    term match {
      case v @ Var("_") => // TODO parse this differently... or handle consistently everywhere
        freshVar(tp(v.toLoc, "wildcard"))
      case Asc(trm, ty) =>
        val trm_ty = typeTerm(trm)
        implicit val vars: Map[Str, SimpleType] = Map.empty
        val ty_ty = typeType(ty)(ctx.copy(inPattern = false), raise, vars)
        con(trm_ty, ty_ty, ty_ty)
        if (ctx.inPattern) trm_ty else ty_ty
      case (v @ ValidPatVar(nme)) =>
        val prov = tp(if (verboseConstraintProvenanceHints) v.toLoc else N, "variable")
        ctx.env.get(nme).map(_.instantiate) // Note: only look at ctx.env, and not the outer ones!
          .getOrElse(new TypeVariable(lvl, Nil, Nil)(prov).tap(ctx += nme -> _))
      case v @ ValidVar(name) =>
        val ty = ctx.get(name).getOrElse {
          // TODO: delay type expansion to message display and show the expected type here!
          err("identifier not found: " + name, term.toLoc)
        }.instantiate
        mkProxy(ty, prov)
        // ^ TODO maybe use a description passed in param?
        // currently we get things like "flows into variable reference"
        // but we used to get the better "flows into object receiver" or "flows into applied expression"...
      case lit: Lit => PrimType(lit, Set.single(lit.baseClass))(prov)
      case App(Var("neg" | "~"), trm) => typeTerm(trm).neg(prov)
      case App(App(Var("|"), lhs), rhs) =>
        typeTerm(lhs) | (typeTerm(rhs), prov)
      case App(App(Var("&"), lhs), rhs) =>
        typeTerm(lhs) & (typeTerm(rhs), prov)
      case Rcd(fs) => // TODO rm: no longer used?
        RecordType.mk(fs.map { case (n, t) => (n, typeTerm(t)) })(tp(term.toLoc, "record literal"))
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
        val param_ty = typePattern(pat)(newCtx, raise)
        newCtx ++= newBindings
        val body_ty = typeTerm(body)(newCtx, raise)
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
        if (raw_fun_ty.isInstanceOf[VarType] || raw_fun_ty.isInstanceOf[AppType]) // TODO more principled
          (fun_ty app arg_ty)(appProv)
        else resTy
      case Sel(obj, name) =>
        val o_ty = typeTerm(obj)
        val res = freshVar(prov)
        val obj_ty = mkProxy(o_ty, tp(obj.toCoveringLoc, "receiver"))
        con(obj_ty, RecordType.mk((name, res) :: Nil)(prov), res)
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
      case With(t, n, v) =>
        val t_ty = typeTerm(t)
        val v_ty = typeTerm(v)
        (t_ty without n) &
          RecordType.mk(n -> v_ty :: Nil)(noProv) // TODO maybe With should take a Rcd and we'd use its type with prov here
      case CaseOf(s, cs) =>
        val s_ty = typeTerm(s)
        val (tys, cs_ty) = typeArms(s |>? {
          case v: Var => v
          case Asc(v: Var, _) => v
        }, cs)
        val req = tys.foldRight(BotType: SimpleType) {
          case ((a_ty, tv), req) =>
            a_ty & tv | req & a_ty.neg(noProv // FIXME
              )
        }
        con(s_ty, req, cs_ty)
    }
  }(r => s"$lvl. : ${r}")
  
  def typeArms(scrutVar: Opt[Var], arms: CaseBranches)
      (implicit ctx: Ctx, raise: Raise, lvl: Int)
      : Ls[SimpleType -> SimpleType] -> SimpleType = arms match {
    case NoCases => Nil -> BotType
    case Wildcard(b) =>
      val fv = freshVar(noProv // FIXME
      )
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
          PrimType(lit, Set.single(lit.baseClass))(tp(pat.toLoc, "literal pattern"))
        case Var(nme) =>
          ctx.tyDefs.get(nme) match {
            case None =>
              err("type identifier not found: " + nme, pat.toLoc)(raise, noProv /*FIXME*/)
              val e = PrimType(ErrTypeId, Set.empty)(noProv)
              return ((e -> e) :: Nil) -> e
            case Some(td) =>
              // TODO check td is a class (or also support traits?)
              if (td.kind === Als) err(msg"can only match on classes and traits",
                pat.toLoc)(raise, noProv /*FIXME*/)
              clsNameToNomTag(td)(tp(pat.toLoc, "type pattern"), ctx)
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
  
  def typeTerms(term: Ls[Statement], rcd: Bool, fields: List[Opt[Str] -> SimpleType])
        (implicit ctx: Ctx, raise: Raise, prov: TypeProvenance): SimpleType
      = term match {
    case (trm @ Var(nme)) :: sts if rcd => // field punning
      typeTerms(Tup(S(nme) -> trm :: Nil) :: sts, rcd, fields)
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
          constrain(t_ty, ty)(raise, prov)
          ctx += nme -> t_ty
          
          t_ty
          // ty
          // ComposedType(false, t_ty, ty)(prov)
          // ComposedType(true, t_ty, ty)(prov) // loops!
          
        case S(nme) =>
          ctx += nme -> ty
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
            ("_" + (i + 1), t)
        }.toList
        RecordType.mk(fs)(prov)
      } else TupleType(fields.reverse)(prov)
  }
  
  
  /** Convert an inferred SimpleType into the immutable Type representation. */
  def expandType(st: SimpleType, polarity: Bool = true): Type = {
    
    // TODO improve/simplify? (take inspiration from other impls?)
    //    see: duplication of recursive.get(st_pol) logic
    
    val recursive = mutable.Map.empty[SimpleType -> Bool, TypeVar]
    def go(st: SimpleType, polarity: Boolean)(implicit inProcess: Set[SimpleType -> Bool]): Type = {
      val st_pol = st -> polarity
      if (inProcess(st_pol)) recursive.getOrElseUpdate(st_pol, freshVar(st.prov)(0).asTypeVar)
      else (inProcess + st_pol) pipe { implicit inProcess => st match {
        case tv: TypeVariable =>
          val bounds = if (polarity) tv.lowerBounds else tv.upperBounds
          val bound =
            if (polarity) bounds.foldLeft(BotType: SimpleType)(_ | _)
            else bounds.foldLeft(TopType: SimpleType)(_ & _)
          if (inProcess(bound -> polarity))
            recursive.getOrElseUpdate(bound -> polarity, freshVar(st.prov)(0).asTypeVar)
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
            case vt: VarType => Primitive(vt.vi.v.name) // TODO disambiguate homonyms...
            case FunctionType(l, r) => Function(go(l, !polarity), go(r, polarity))
            case ComposedType(true, l, r) => Union(go(l, polarity), go(r, polarity))
            case ComposedType(false, l, r) => Inter(go(l, polarity), go(r, polarity))
            case RecordType(fs) => Record(fs.map(nt => nt._1 -> go(nt._2, polarity)))
            case TupleType(fs) => Tuple(fs.map(nt => nt._1 -> go(nt._2, polarity)))
            case AppType(fun, args) => args.map(go(_, polarity)).foldLeft(go(fun, polarity))(Applied(_, _))
            case NegType(t) => Applied(Primitive("~"), expandType(t))
            case ExtrType(true) => Bot
            case ExtrType(false) => Top
            case ProxyType(und) => go(und, polarity)
            case PrimType(n, _) => Primitive(n.idStr)
            case TypeRef(td, Nil) => Primitive(td.nme.name)
            case TypeRef(td, targs) =>
              AppliedType(Primitive(td.nme.name), targs.map(expandType(_, polarity)))
            case Without(base, names) => Rem(expandType(base, polarity), names.toList.map(Var))
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
