package funtypes

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import funtypes.utils._, shorthands._
import funtypes.Message._

/** A class encapsulating type inference state.
 *  It uses its own internal representation of types and type variables, using mutable data structures.
 *  Inferred SimpleType values are then turned into CompactType values for simplification.
 *  In order to turn the resulting CompactType into a funtypes.Type, we use `expandCompactType`.
 */
class Typer(var dbg: Boolean, var verbose: Bool, var explainErrors: Bool) extends ConstraintSolver with TypeSimplifier {
  
  type Ctx = Map[String, TypeScheme]
  type Raise = Diagnostic => Unit
  
  val primProv: TypeProvenance = TypeProvenance(N, "expression")
  
  val UnitType: PrimType = PrimType(Var("unit"))(primProv)
  val BoolType: PrimType = PrimType(Var("bool"))(primProv)
  val IntType: PrimType = PrimType(Var("int"))(primProv)
  val DecType: PrimType = PrimType(Var("number"))(primProv)
  val StrType: PrimType = PrimType(Var("string"))(primProv)
  
  val ErrTypeId: SimpleTerm = Var("error")
  
  val builtins: Ctx = {
    val tv = freshVar(primProv)(1) // Q: level?
    import FunctionType.{ apply => fun }
    Map(
      "true" -> BoolType,
      "false" -> BoolType,
      "not" -> fun(BoolType, BoolType)(primProv),
      "succ" -> fun(IntType, IntType)(primProv),
      "log" -> PolymorphicType(0, fun(tv, UnitType)(primProv)),
      "discard" -> PolymorphicType(0, fun(tv, UnitType)(primProv)),
      "add" -> fun(IntType, fun(IntType, IntType)(primProv))(primProv),
      "+" -> fun(IntType, fun(IntType, IntType)(primProv))(primProv),
      "<" -> fun(IntType, fun(IntType, BoolType)(primProv))(primProv),
      "id" -> {
        val v = freshVar(primProv)(1)
        PolymorphicType(0, fun(v, v)(primProv))
      },
      "if" -> {
        val v = freshVar(primProv)(1)
        PolymorphicType(0, fun(BoolType, fun(v, fun(v, v)(primProv))(primProv))(primProv))
      },
    ) ++ List("unit" -> UnitType, "bool" -> BoolType, "int" -> IntType, "number" -> DecType, "string" -> StrType)
  }
  
  import TypeProvenance.{apply => tp}
  def ttp(trm: Term, desc: Str = ""): TypeProvenance =
    TypeProvenance(trm.toLoc, if (desc === "") trm.describe else desc)
  
  /** The main type inference function */
  def inferTypes(pgrm: Pgrm, ctx: Ctx = builtins): List[Either[TypeError, PolymorphicType]] =
    pgrm.defs match {
      case (isrec, nme, rhs) :: defs =>
        val ty_sch = try Right(typeLetRhs(isrec, nme, rhs)(ctx, 0, throw _)) catch {
          case err: TypeError => Left(err) }
        val errProv = TypeProvenance(rhs.toLoc, "let-bound value")
        ty_sch :: inferTypes(Pgrm(defs), ctx + (nme -> ty_sch.getOrElse(freshVar(errProv)(0))))
      case Nil => Nil
    }
  
  // Saldy, the version above does not work in JavaScript as it raises a
  //    "RangeError: Maximum call stack size exceeded"
  // So we have to go with this uglier one:
  def inferTypesJS(
    pgrm: Pgrm,
    ctx: Ctx = builtins,
    stopAtFirstError: Boolean = true,
  ): List[Either[TypeError, PolymorphicType]] = {
    var defs = pgrm.defs
    var curCtx = ctx
    var res = collection.mutable.ListBuffer.empty[Either[TypeError, PolymorphicType]]
    while (defs.nonEmpty) {
      val (isrec, nme, rhs) = defs.head
      defs = defs.tail
      val ty_sch = try Right(typeLetRhs(isrec, nme, rhs)(curCtx, 0, throw _)) catch {
        case err: TypeError =>
          if (stopAtFirstError) defs = Nil
          Left(err)
      }
      res += ty_sch
      val errProv = TypeProvenance(rhs.toLoc, "let-bound value")
      curCtx += (nme -> ty_sch.getOrElse(freshVar(errProv)(0)))
    }
    res.toList
  }
  
  type Binding = (Str, PolymorphicType)
  
  def typeBlk(blk: Blk, ctx: Ctx = builtins, allowPure: Bool = false)
        : Ls[Ls[Diagnostic] -> (PolymorphicType \/ Ls[Binding])]
        = blk.stmts match {
    case s :: stmts =>
      val diags = mutable.ListBuffer.empty[Diagnostic]
      val newBindings = typeStatement(s, allowPure)(ctx, 0, diags += _)
      val newCtx = ctx ++ newBindings.getOrElse(Nil)
      diags.toList -> newBindings :: typeBlk(Blk(stmts), newCtx, allowPure)
    case Nil => Nil
  }
  def typeStatement(s: Statement, allowPure: Bool = false)
        (implicit ctx: Ctx, lvl: Int, raise: Raise): PolymorphicType \/ Ls[Binding] = {
    val (diags, desug) = s.desugared
    diags.foreach(raise)
    typeStatement(desug, allowPure)
  }
  type PatCtx = mutable.Map[Str, TypeVariable]
  def typePattern(pat: Term, newBindings: PatCtx)(implicit ctx: Ctx, lvl: Int, raise: Raise): SimpleType = pat match {
    case (v @ ValidVar(nme)) =>
      val prov = tp(v.toLoc, "pattern variable")
      newBindings.getOrElseUpdate(nme, new TypeVariable(lvl, Nil, Nil)(prov))
    case (tup @ Tup(fs)) =>
      val params_ty = fs.map {
        case (S(nme), t) =>
          val prov = tp(t.toLoc, "parameter type")
          // TODO in positive position, this should create a new VarType instead!
          val tv = newBindings.getOrElseUpdate(nme, new TypeVariable(lvl, Nil, Nil)(prov))
          val t_ty = t match {
            case Bra(false, t) => // we use syntax `(x: (p))` to type `p` as a pattern and not a type...
              typePattern(t, newBindings)
            case _ => typeTerm(t)
          }
          constrain(tv, t_ty)(raise, prov)
          S(nme) -> tv
        case (N, t) =>
          val t_ty = typePattern(t, newBindings)
          N -> t_ty
      }
      TupleType(params_ty)(ttp(tup))
    case Blk((t: Term) :: Nil) => typePattern(t, newBindings)
    case Bra(false, t) => typePattern(t, newBindings)
    case _ => // TODO
      err(msg"Unsupported parameter shape:", pat.toLoc)(raise, ttp(pat))
  }
  def typeData(d: DataDesug)(implicit ctx: Ctx, lvl: Int, raise: Raise): VarType -> Ls[SimpleType] = {
    val newBindings = mutable.Map.empty[Str, TypeVariable]
    val params_ty = d.params.map(typePattern(_, newBindings))
    val appProv = tp(d.original.toLoc, "data definition")
    val refinedBase = RecordType(newBindings.toList.sortBy(_._1))(appProv) //, tv)(raise, appProv)
    val ty = params_ty.foldRight(refinedBase: SimpleType)(_.abs(_)(appProv))
    VarType(new VarIdentity(lvl - 1, d.head), ty, false)(tp(d.head.toLoc, "data symbol")) -> params_ty
  }
  def typeStatement(s: DesugaredStatement, allowPure: Bool)
        (implicit ctx: Ctx, lvl: Int, raise: Raise): PolymorphicType \/ Ls[Binding] = s match {
    case LetDesug(isrec, v @ ValidVar(nme), rhs) =>
      val ty_sch = typeLetRhs(isrec, nme, rhs)
      (ctx + (nme -> ty_sch)) -> ty_sch
      R(nme -> ty_sch :: Nil)
    case d @ DataDesug(v @ ValidVar(nme), params) =>
      val (vt, params_ty) = typeData(d)(ctx, lvl + 1, raise)
      val bind = nme -> PolymorphicType(lvl, vt)
      R(bind :: Nil)
    case d @ DatatypeDesug(v @ ValidVar(nme), params, cases) => (lvl + 1) |> { implicit lvl =>
      val vProv = tp(v.toLoc, "data type symbol")
      val appProv = tp(d.original.toLoc, "data type definition")
      val base_tv = freshVar(vProv)
      val newBindings = mutable.Map.empty[Str, TypeVariable]
      val params_ty = params.map(typePattern(_, newBindings))
      val baseBindings = newBindings.toList.sortBy(_._1)
      val newCtx = ctx ++ baseBindings + (nme -> base_tv)
      val caseBindings = mutable.ListBuffer.empty[Binding]
      val cases_ty = cases.map { case c @ DataDesug(v @ ValidVar(nme), params) =>
        val (vt, params_ty) = typeData(c)(newCtx, lvl + 1, raise)
        caseBindings += nme -> PolymorphicType(lvl, vt) // FIXME is the quantification correct?
        val applied_ty = params_ty.foldLeft(vt: SimpleType)(_.app(_)(appProv))
        applied_ty
      }
      val ty = new TypeVariable(lvl, cases_ty, cases_ty)(appProv) // FIXME!!
      val fty = params_ty.foldRight(ty: SimpleType)(_.abs(_)(appProv))
      val vty = VarType(new VarIdentity(lvl, v), fty, true)(vProv)
      constrain(fty, base_tv)(raise, appProv)
      // constrain(base_tv, fty)(raise, appProv) // TODO what we need here is a union in negative position...
      R(nme -> PolymorphicType(lvl, vty) :: caseBindings.toList)
    }
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
  }
  
  def inferType(term: Term, ctx: Ctx = builtins, lvl: Int = 0): SimpleType =
    typeTerm(term)(ctx, lvl, throw _)
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: String, rhs: Term)
        (implicit ctx: Ctx, lvl: Int, raise: Raise): PolymorphicType = {
    val res = if (isrec) {
      val e_ty = freshVar(TypeProvenance(rhs.toLoc, "let-bound value"))(lvl + 1)
      val ty = typeTerm(rhs)(ctx + (nme -> e_ty), lvl + 1, raise)
      constrain(ty, e_ty)(raise, TypeProvenance(rhs.toLoc, "binding of " + rhs.describe))
      e_ty
    } else typeTerm(rhs)(ctx, lvl + 1, raise)
    PolymorphicType(lvl, res)
  }
  
  def mkProxy(ty: SimpleType, prov: TypeProvenance): SimpleType = {
    ProxyType(ty)(prov)
    // TODO switch to return this in perf mode:
    // ty
  }
  
  val reservedNames: Set[Str] = Set("|", "&", ",")
  
  object ValidVar {
    def unapply(v: Var)(implicit raise: Raise): S[Str] = S {
      if (reservedNames(v.name)) err("unexpected use of: " + v.name, v.toLoc)(raise, ttp(v))
      v.name
    }
  }
  
  /** Infer the type of a term. */
  def typeTerm(term: Term)
        (implicit ctx: Ctx, lvl: Int, raise: Raise): SimpleType
        = trace(s"$lvl. Typing $term") {
    implicit val prov: TypeProvenance = TypeProvenance(term.toLoc, term.describe)
    
    def con(lhs: SimpleType, rhs: SimpleType, res: TypeVariable): SimpleType = {
      var alreadyReportedAnError = false
      constrain(lhs, rhs)({
        case err: TypeError if alreadyReportedAnError => () // silence further errors from this location
        case err: TypeError =>
          alreadyReportedAnError = true
          constrain(errType, res)
          raise(err)
        case diag => raise(diag)
      }, prov)
      res
    }
    term match {
      case v @ Var("_") => // TODO parse this differently... or handle consistently everywhere
        freshVar(tp(v.toLoc, "wildcard"))
      case ValidVar(name) =>
        val ty = ctx.getOrElse(name, {
          // TODO: delay type expansion to message display and show the expected type here!
          err("identifier not found: " + name, term.toLoc)
        }).instantiate
        mkProxy(ty, tp(term.toLoc, term.describe))
        // ^ TODO maybe use a description passed in param?
        // currently we get things like "flows into variable reference"
        // but we used to get the better "flows into object receiver" or "flows into applied expression"...
      case Lam(v @ ValidVar(name), body) =>
        val param = freshVar(tp(if (verboseConstraintProvenanceHints) v.toLoc else N, "parameter"))
        val body_ty = typeTerm(body)(ctx + (name -> param), lvl, raise)
        FunctionType(param, body_ty)(tp(term.toLoc, "function"))
      case Lam(pat, body) =>
        val newBindings = mutable.Map.empty[Str, TypeVariable]
        val param_ty = typePattern(pat, newBindings)
        val body_ty = typeTerm(body)(ctx ++ newBindings, lvl, raise)
        FunctionType(param_ty, body_ty)(tp(term.toLoc, "function"))
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
      case lit: Lit => PrimType(lit)(tp(term.toLoc, "constant literal"))
      case Sel(obj, name) =>
        val o_ty = typeTerm(obj)
        val res = freshVar(prov)
        val obj_ty = mkProxy(o_ty, tp(obj.toCoveringLoc, "receiver"))
        con(obj_ty, RecordType((name, res) :: Nil)(prov), res)
      case Rcd(fs) => // TODO rm: no longer used?
        RecordType(fs.map { case (n, t) => (n, typeTerm(t)) })(tp(term.toLoc, "record literal"))
      case Let(isrec, nme, rhs, bod) =>
        val n_ty = typeLetRhs(isrec, nme, rhs)
        typeTerm(bod)(ctx + (nme -> n_ty), lvl, raise)
      case tup: Tup =>
        typeTerms(tup :: Nil, false, Nil)
      case Bra(false, trm: Blk) => typeTerm(trm)
      case Bra(rcd, trm @ (_: Tup | _: Blk)) => typeTerms(trm :: Nil, rcd, Nil)
      case Bra(_, trm) => typeTerm(trm)
      case Blk((s: Term) :: Nil) => typeTerm(s)
      case Blk(Nil) => UnitType
      // case Blk(s :: stmts) =>
      //   val (newCtx, ty) = typeStatement(s)
      //   typeTerm(Blk(stmts))(newCtx, lvl, raise)
      case Blk(stmts) => typeTerms(stmts, false, Nil)
    }
  }(r => s"$lvl. : ${r}")
  
  def typeTerms(term: Ls[Statement], rcd: Bool, fields: List[Opt[Str] -> SimpleType])
        (implicit ctx: Ctx, lvl: Int, raise: Raise, prov: TypeProvenance): SimpleType
      = term match {
    case (trm @ Var(nme)) :: sts if rcd => // field punning
      typeTerms(Tup(S(nme) -> trm :: Nil) :: sts, rcd, fields)
    case Blk(sts0) :: sts1 => typeTerms(sts0 ::: sts1, rcd, fields)
    case Tup(Nil) :: sts => typeTerms(sts, rcd, fields)
    case Tup((no, trm) :: ofs) :: sts =>
      val ty = if (ofs.isEmpty) typeTerm(Bra(rcd, trm)) else typeTerm(trm)
      val newCtx = no.fold(ctx)(n => ctx + (n -> ty))
      typeTerms(Tup(ofs) :: sts, rcd, (no, ty) :: fields)(newCtx, lvl, raise, prov)
    case (trm: Term) :: Nil =>
      if (fields.nonEmpty)
        warn("Previous field definitions are discarded by this returned expression.", trm.toLoc)
      typeTerm(trm)
    // case (trm: Term) :: Nil =>
    //   assert(!rcd)
    //   val ty = typeTerm(trm)
    //   typeBra(Nil, rcd, (N, ty) :: fields)
    case s :: sts =>
      val newBindings = typeStatement(s)
      val newCtx = ctx ++ newBindings.getOrElse(Nil)
      typeTerms(sts, rcd, fields)(newCtx, lvl, raise, prov)
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
        RecordType(fs)(prov)
      } else TupleType(fields.reverse)(prov)
  }
  
  /** Convert an inferred SimpleType into the immutable Type representation. */
  def expandType(st: SimpleType, polarity: Bool = true): Type = {
    val recursive = mutable.Map.empty[PolarVariable, TypeVar]
    def go(st: SimpleType, polarity: Boolean)(inProcess: Set[PolarVariable]): Type = st match {
      case tv: TypeVariable =>
        val tv_pol = tv -> polarity
        if (inProcess.contains(tv_pol))
          recursive.getOrElseUpdate(tv_pol, freshVar(tv.prov)(0).asTypeVar)
        else {
          val bounds = if (polarity) tv.lowerBounds else tv.upperBounds
          val boundTypes = bounds.map(go(_, polarity)(inProcess + tv_pol))
          val mrg = if (polarity) Union else Inter
          val res = boundTypes.foldLeft[Type](tv.asTypeVar)(mrg)
          recursive.get(tv_pol).fold(res)(Recursive(_, res))
        }
      case vt: VarType => Primitive(vt.vi.v.name) // TODO disambiguate homonyms...
      case FunctionType(l, r) => Function(go(l, !polarity)(inProcess), go(r, polarity)(inProcess))
      case RecordType(fs) => Record(fs.map(nt => nt._1 -> go(nt._2, polarity)(inProcess)))
      case TupleType(fs) => Tuple(fs.map(nt => nt._1 -> go(nt._2, polarity)(inProcess)))
      case AppType(fun, args) => args.map(go(_, polarity)(inProcess)).foldLeft(go(fun, polarity)(inProcess))(Applied(_, _))
      case NegType(_) => ??? // TODO
      case ProxyType(und) => go(und, polarity)(inProcess)
      case PrimType(n) => Primitive(n.idStr)
    }
    go(st, polarity)(Set.empty)
  }
  
}
