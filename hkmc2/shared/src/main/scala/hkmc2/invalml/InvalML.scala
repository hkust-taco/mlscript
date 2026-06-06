package hkmc2
package invalml


import scala.collection.mutable.{HashSet, HashMap, ListBuffer}
import scala.annotation.tailrec

import hkmc2.utils.*, shorthands.*
import utils.*

import Message.MessageContext
import semantics.*, Term.*, ucs.FlatPattern
import Elaborator.Ctx
import syntax.*
import Tree.*
import utils.Scope

object InfVarUid extends Uid.Handler[InfVar]


final case class InvalCtx(
  raise: Raise,
  ctx: Ctx,
  parent: Option[InvalCtx],
  lvl: Int,
  env: HashMap[Uid[Symbol], GeneralType],
  outRegAcc: Type,
  symbolCache: HashMap[Str, TypeSymbol],
):
  def +=(p: Symbol -> GeneralType): Unit = env += p._1.uid -> p._2
  def get(sym: Symbol): Option[GeneralType] = env.get(sym.uid) orElse parent.dlof(_.get(sym))(None)
  def getCls(name: Str): TypeSymbol = symbolCache.getOrElseUpdate(name,
    ctx.get(name).get.symbol.get.asTpe.get)
  def &=(p: (Symbol, Type, InfVar)): Unit =
    env += p._1.uid -> InvalCtx.varTy(p._2, p._3)(using this)
  def nest: InvalCtx = copy(parent = Some(this), env = HashMap.empty)
  def nextLevel: InvalCtx = copy(parent = Some(this), lvl = lvl + 1, env = HashMap.empty)
  def nestReg(reg: InfVar): InvalCtx =
    copy(parent = Some(this), lvl = lvl + 1, env = HashMap.empty, outRegAcc = outRegAcc | reg)
  def nestWithOuter(outer: InfVar): InvalCtx =
    copy(parent = Some(this), lvl = lvl + 1, env = HashMap.empty, outRegAcc = outRegAcc | outer)
  def getRegEnv: Type = outRegAcc

def invalctx(using ctx: InvalCtx): InvalCtx = ctx

given (using ctx: InvalCtx): Raise = ctx.raise

object InvalCtx:
  def unitTy(using ctx: InvalCtx): Type = ClassLikeType(ctx.getCls("Unit"), Nil)
  def intTy(using ctx: InvalCtx): Type = ClassLikeType(ctx.getCls("Int"), Nil)
  def numTy(using ctx: InvalCtx): Type = ClassLikeType(ctx.getCls("Num"), Nil)
  def strTy(using ctx: InvalCtx): Type = ClassLikeType(ctx.getCls("Str"), Nil)
  def boolTy(using ctx: InvalCtx): Type = ClassLikeType(ctx.getCls("Bool"), Nil)
  def errTy(using ctx: InvalCtx): Type = ClassLikeType(ctx.getCls("Error"), Nil)
  private def codeBaseTy(ct: TypeArg, cr: TypeArg, isVar: TypeArg)(using ctx: InvalCtx): Type =
    ClassLikeType(ctx.getCls("CodeBase"), ct :: cr :: isVar :: Nil)
  def codeTy(ct: Type, cr: Type)(using ctx: InvalCtx): Type =
    codeBaseTy(Wildcard.out(ct), Wildcard.out(cr), Wildcard.out(Top))
  def varTy(ct: Type, cr: Type)(using ctx: InvalCtx): Type =
    codeBaseTy(ct, Wildcard(cr, cr), Wildcard.out(Bot))
  def regionTy(sk: Type)(using ctx: InvalCtx): Type =
    ClassLikeType(ctx.getCls("Region"), Wildcard.out(sk) :: Nil)
  def refTy(ct: Type, sk: Type)(using ctx: InvalCtx): Type =
    ClassLikeType(ctx.getCls("Ref"), Wildcard(ct, ct) :: Wildcard.out(sk) :: Nil)
  def init(raise: Raise)(using Elaborator.State, Elaborator.Ctx): InvalCtx =
    new InvalCtx(raise, summon, None, 1, HashMap.empty, Bot, HashMap.empty)

  val builtinOps = Elaborator.binaryOps ++ Elaborator.unaryOps ++ Elaborator.aliasOps.keySet
end InvalCtx


class InvalTyper(using elState: Elaborator.State, tl: TL)(using Ctx):
  import tl.{trace, log}
  
  private val infVarState = new InfVarUid.State()
  private val solver = new ConstraintSolver(infVarState, elState, tl)

  // A temporary solution for ADT matching exhausive checking
  // `adtCtors` maps IDs of ADTs to their constructors' IDs
  // `adtParent` maps constructors' IDs to the ADT class symbol they belong to
  // `typeNames` maintains all type names 
  // since we need to reject all non-variable patterns in ADT match for now
  private val adtCtors = HashMap.empty[Uid[Symbol], ListBuffer[Uid[Symbol]]]
  private val adtParent = HashMap.empty[Uid[Symbol], Symbol]
  private val typeNames = HashSet.empty[Str]

  private def freshSkolem(sym: Symbol, hint: Str = "")(using ctx: InvalCtx): InfVar =
    InfVar(ctx.lvl, infVarState.nextUid, new VarState(), true)(sym, hint)
  private def freshVar(sym: Symbol, hint: Str = "")(using ctx: InvalCtx): InfVar =
    InfVar(ctx.lvl, infVarState.nextUid, new VarState(), false)(sym, hint)
  private def freshWildcard(sym: Symbol)(using ctx: InvalCtx) =
    val in = freshVar(sym, "")
    val out = freshVar(sym, "")
    // in.state.upperBounds ::= out // * Not needed for soundness; complicates inferred types
    Wildcard(in, out)
  private def freshReg(sym: Symbol)(using ctx: InvalCtx) =
    val state = new VarState()
    state.upperBounds = ctx.getRegEnv.! :: Nil
    InfVar(ctx.lvl + 1, infVarState.nextUid, state, true)(sym, "")
  private def freshOuter(sym: Symbol)(using ctx: InvalCtx): InfVar =
    InfVar(ctx.lvl + 1, infVarState.nextUid, new VarState(), true)(sym, "")
  private def freshEnv(sym: Symbol)(using ctx: InvalCtx): InfVar =
    val state = new VarState()
    state.upperBounds = ctx.getRegEnv :: Nil
    state.lowerBounds = ctx.getRegEnv :: Nil
    InfVar(ctx.lvl, infVarState.nextUid, state, false)(sym, "")

  private def error(msg: Ls[Message -> Opt[Loc]], extraInfo: => Opt[Any] = N)(using InvalCtx) =
    raise(ErrorReport(msg, extraInfo = extraInfo))
    Bot // TODO: error type?

  private def addADTCtor(pSym: Symbol, cSym: Symbol) =
    if !adtCtors.keySet(pSym.uid) then
      adtCtors += pSym.uid -> ListBuffer(cSym.uid)
    else adtCtors(pSym.uid) += cSym.uid
    adtParent += cSym.uid -> pSym
    typeNames.add(pSym.nme)
    typeNames.add(cSym.nme)

  private def typeAndSubstType
      (ty: Term, pol: Bool)(using map: Map[Uid[Symbol], TypeArg])(using ctx: InvalCtx, cctx: CCtx)
      : GeneralType =
  trace[GeneralType](s"${ctx.lvl}. Typing type ${ty.showDbg}", r => s"~> ${r.showDbg}"):
    def mono(ty: Term, pol: Bool): Type =
      monoOrErr(typeAndSubstType(ty, pol), ty)
    ty match
    case Ref(sym: LocalSymbol) =>
      log(s"Type lookup: ${sym.nme} ${sym.uid} ${map.keySet}")
      map.get(sym.uid) match
        case Some(Wildcard(in, out)) => if pol then out else in
        case Some(ty: Type) => ty
        case N => ctx.get(sym) match
          case Some(ty) => ty
          case _ =>
            error(msg"Variable not found: ${sym.nme}" -> ty.toLoc :: Nil)
    case FunTy(Term.Tup(params), ret, eff) =>
      PolyFunType(params.map {
        case Fld(_, p, _) => typeAndSubstType(p, !pol)
        case spd: Spd => lastWords(s"unexpected spread in function type parameters: $spd")
      }, typeAndSubstType(ret, pol), eff.map(e => typeAndSubstType(e, pol) match {
        case t: Type => t
        case _ => error(msg"Effect cannot be polymorphic." -> ty.toLoc :: Nil)
      }).getOrElse(Bot))
    case f @ Term.Forall(tvs, outer, body) =>
      val outVar = freshOuter(outer.getOrElse(new TempSymbol(S(f), "outer")))(using ctx)
      val nestCtx = ctx.nestWithOuter(outVar)
      outer.foreach(sym => nestCtx += sym -> outVar)
      given InvalCtx = nestCtx
      genPolyType(tvs, outVar, typeAndSubstType(body, pol))
    case Term.TyApp(cls, targs) =>
      // log(s"Type application: ${cls.nme} with ${targs}")
      cls.symbol.flatMap(_.asTpe) match
      case S(tpeSym) =>
        if tpeSym.nme === "Any" then Top // FIXME hygiene
        else if tpeSym.nme === "Nothing" then Bot // FIXME hygiene
        else
          val defn = tpeSym.defn.get
          if targs.length != defn.tparams.length then
            error(msg"Type arguments do not match class definition" -> ty.toLoc :: Nil)
          val ts = defn.tparams.lazyZip(targs).map: (tp, t) =>
            t match
            case Term.WildcardTy(in, out) => Wildcard(
                in.map(t => mono(t, !pol)).getOrElse(Bot),
                out.map(t => mono(t, pol)).getOrElse(Top)
              )
            case _ =>
              val ta = mono(t, pol)
              tp.vce match
                case S(false) => Wildcard.in(ta)
                case S(true) => Wildcard.out(ta)
                case N => ta
          ClassLikeType(tpeSym, ts)
      case N =>
        error(msg"Not a valid class: ${cls.describe}" -> cls.toLoc :: Nil)
    case Neg(rhs) =>
      mono(rhs, !pol).!
    case CompType(lhs, rhs, pol) =>
      Type.mkComposedType(typeMonoType(lhs), typeMonoType(rhs), pol)
    case UnitVal() =>
      InvalCtx.unitTy
    case _ =>
      ty.symbol.flatMap(_.asTpe) match
      case S(cls: (ClassSymbol | TypeAliasSymbol)) => typeAndSubstType(Term.TyApp(ty, Nil)(N), pol)
      case S(_) | N => error(msg"Invalid type" -> ty.toLoc :: Nil, S(ty)) // TODO

  private def genPolyType(tvs: Ls[QuantVar], outer: InfVar, body: => GeneralType)(using ctx: InvalCtx, cctx: CCtx) =
    val bds = tvs.map:
      case qv @ QuantVar(sym, ub, lb) =>
        val tv = freshVar(sym)
        ctx += sym -> tv // TODO: a type var symbol may be better...
        tv -> qv
    bds.foreach:
      case (tv, QuantVar(_, ub, lb)) =>
        ub.foreach(ub => tv.state.upperBounds ::= typeMonoType(ub))
        lb.foreach(lb => tv.state.lowerBounds ::= typeMonoType(lb))
        val lbty = tv.state.lowerBounds.foldLeft[Type](Bot)(_ | _)
        val ubty = tv.state.upperBounds.foldLeft[Type](Top)(_ & _)
        constrain(lbty, ubty)
    PolyType(bds.map(_._1), S(outer), body)

  private def typeMonoType(ty: Term)(using ctx: InvalCtx, cctx: CCtx): Type = monoOrErr(typeType(ty), ty)

  private def typeType(ty: Term)(using ctx: InvalCtx, cctx: CCtx): GeneralType =
    typeAndSubstType(ty, pol = true)(using Map.empty)
  
  private def instantiate(ty: PolyType)(using ctx: InvalCtx): GeneralType =
    ty.instantiate(infVarState.nextUid, freshEnv(new TempSymbol(N, "env")), ctx.lvl)(tl)

  private def extrude(ty: GeneralType)(using ctx: InvalCtx, pol: Bool, cctx: CCtx): GeneralType = ty match
    case ty: Type => solver.extrude(ty)(using ctx.lvl, pol, HashMap.empty)
    case PolyType(tvs, outer, body) => PolyType(tvs, outer, extrude(body))
    case pf @ PolyFunType(args, ret, eff) =>
      PolyFunType(args.map(extrude(_)(using ctx, !pol)), extrude(ret), solver.extrude(eff)(using ctx.lvl, pol, HashMap.empty))

  private def constrain(lhs: Type, rhs: Type)(using ctx: InvalCtx, cctx: CCtx): Unit =
    solver.constrain(lhs, rhs)

  private def typeCode(code: Term)(using ctx: InvalCtx, scope: Scope): (Type, Type, Type) =
    given CCtx = CCtx.init(code, N)
    code match
    case UnitVal() => (Top, Bot, Bot)
    case Lit(lit) => ((lit match // TODO dedup with other `case Lit(lit)`
      case _: IntLit => InvalCtx.intTy
      case _: DecLit => InvalCtx.numTy
      case _: StrLit => InvalCtx.strTy
      case _: UnitLit => InvalCtx.unitTy
      case _: BoolLit => InvalCtx.boolTy), Bot, Bot)
    case Ref(sym: Symbol) if sym.nme === "error" => (Bot, Bot, Bot)
    case Ref(sym: Symbol) if InvalCtx.builtinOps(sym.nme) => ctx.get(sym) match
      case S(ty) => (tryMkMono(ty, code), Bot, Bot)
      case N =>
        (error(msg"Cannot quote operator ${sym.nme}" -> code.toLoc :: Nil), Bot, Bot)
    case f @ Lam(PlainParamList(params), body) =>
      val nestCtx = ctx.nextLevel
      given InvalCtx = nestCtx
      val bds = params.map:
        case Param(sym = sym) =>
          val tv = freshVar(sym)
          val sk = freshSkolem(sym)
          nestCtx &= (sym, tv, sk)
          (tv, sk)
      val (bodyTy, ctxTy, eff) = typeCode(body)
      val res = freshVar(new TempSymbol(S(f), "ctx"))(using ctx)
      constrain(ctxTy, bds.foldLeft[Type](res)((res, bd) => res | bd._2))
      (FunType(bds.map(_._1), bodyTy, Bot), res, eff)
    case app @ Term.App(lhs, Term.Tup(rhs)) =>
      val (lhsTy, lhsCtx, lhsEff) = typeCode(lhs)
      val (rhsTy, rhsCtx, rhsEff) = rhs.foldLeft[(Ls[Type], Type, Type)]((Nil, Bot, Bot)):
        case (res, p: Fld) =>
          val (ty, ctx, eff) = typeCode(p.term)
          (ty :: res._1, res._2 | ctx, res._3 | eff)
        case (_, spd: Spd) => TODO(s"spread arguments in quoted code: $spd")
      val resTy = freshVar(new TempSymbol(S(app), "app"))
      constrain(lhsTy, FunType(rhsTy.reverse, resTy, Bot)) // TODO: right
      (resTy, lhsCtx | rhsCtx, lhsEff | rhsEff)
    case sel @ Term.SynthSel(Term.Ref(_: TopLevelSymbol), _) if sel.symbol.isDefined =>
      val (opTy, eff) = typeCheck(Ref(sel.symbol.get)(sel.nme, 666, N)) // FIXME 666
      (tryMkMono(opTy, sel), Bot, eff)
    case unq @ Term.Unquoted(body) =>
      val (ty, eff) = typeCheck(body)
      val tv = freshVar(new TempSymbol(S(unq), "cde"))
      val cr = freshVar(new TempSymbol(S(unq), "ctx"))
      constrain(tryMkMono(ty, body), InvalCtx.codeTy(tv, cr))
      (tv, cr, eff)
    case blk @ Term.Blk(LetDecl(sym, _) :: DefineVar(sym2, rhs) :: Nil, body)
    if sym2 is sym => // TODO: more than one!!
      val (rhsTy, rhsCtx, rhsEff) = typeCode(rhs)(using ctx)
      val nestCtx = ctx.nextLevel
      given InvalCtx = nestCtx
      val sk = freshSkolem(sym)
      nestCtx &= (sym, rhsTy, sk)
      val (bodyTy, bodyCtx, bodyEff) = typeCode(body)
      val res = freshVar(new TempSymbol(S(blk), "ctx"))(using ctx)
      constrain(bodyCtx, sk | res)
      (bodyTy, rhsCtx | res, rhsEff | bodyEff)
    case Term.IfLike(_, IfLikeForm.ReturningIf, SimpleSplit.IfThenElse(cond, cons, alts)) =>
      val (condTy, condCtx, condEff) = typeCode(cond)
      val (consTy, consCtx, consEff) = typeCode(cons)
      val (altsTy, altsCtx, altsEff) = typeCode(alts)
      constrain(condTy, InvalCtx.boolTy)
      (consTy | altsTy, condCtx | consCtx | altsCtx, condEff | consEff | altsEff)
    case _ =>
      (error(msg"Cannot quote ${code.toString}" -> code.toLoc :: Nil), Bot, Bot)

  private def typeFunDef(sym: Symbol, lam: Term, sig: Opt[Term])(using ctx: InvalCtx, cctx: CCtx, scope: Scope) = lam match
    case Term.Lam(params, body) => sig match
      case S(sig) =>
        val sigTy = typeType(sig)(using ctx)
        ctx += sym -> sigTy
        ascribe(lam, sigTy)
        ()
      case N =>
        val outer = freshOuter(new TempSymbol(S(lam), "outer"))(using ctx)
        given InvalCtx = ctx.nestWithOuter(outer)
        val funTyV = freshVar(sym)
        ctx += sym -> funTyV // for recursive functions
        val (res, _) = typeCheck(lam)
        val funTy = tryMkMono(res, lam)
        given CCtx = CCtx.init(lam, N)
        constrain(funTy, funTyV)(using ctx)
        ctx += sym -> PolyType.generalize(funTy, S(outer), ctx.lvl + 1)
    case _ => error(msg"Function definition shape not yet supported for ${sym.nme}" -> lam.toLoc :: Nil)

  // Check if a given matching expression is matching on an ADT.
  // An `if` expression can only matching on one ADT and patterns can only carry variables so far.
  // It is a temporary solution to ADTs.
  private def isADTMatch(split: Split)(using InvalCtx) =
    def rec(split: Split, acc: Either[Opt[Symbol], Unit]): Bool =
      split match
        case Split.Cons(Branch(_, pattern, _), alts) =>
          pattern match
            case FlatPattern.ClassLike(_, sym, _, _) if adtParent.keySet(sym.uid) =>
              acc match
                case L(N) => rec(alts, L(S(sym)))
                case L(S(other)) if adtParent.get(other.uid).exists(p => p.uid == adtParent(sym.uid).uid) =>
                  rec(alts, L(S(sym)))
                case L(S(_)) =>
                  error(msg"Matching patterns from different ADTs in one match is not supported." -> split.toLoc :: Nil)
                  false
                case R(_) =>
                  error(msg"Mixing ADT pattern matching and general matching is not supported yet." -> split.toLoc :: Nil)
                  false
            case _ => acc match
              case L(S(_)) =>
                error(msg"Mixing ADT pattern matching and general matching is not supported yet." -> split.toLoc :: Nil)
                false
              case _ => rec(alts, R(()))
        case Split.Let(_, _, tail) => rec(tail, acc)
        case _ => acc match
          case L(S(sym)) => true
          case _ => false
    rec(split, L(N))

  // Type check ADT matching, which also returns mentioned constructors for exhaustive checking.
  // No GADT reasoning.
  // It is a temporary solution to ADTs.
  private def typeADTMatch
    (split: Split, sign: Opt[GeneralType])(using ctx: InvalCtx)(using CCtx, Scope)
    : (GeneralType, Type, Ls[Symbol], Bool) = split match
    case Split.Cons(Branch(scrutinee, pattern, cons), alts) =>
      val (scrutineeTy, scrutineeEff) = typeCheck(scrutinee)
      val map = HashMap[Uid[Symbol], TypeArg]()
      pattern match
        case FlatPattern.ClassLike(_, sym, paramsOpt, _) =>
          val clsTy = adtParent.get(sym.uid).flatMap(_.asCls.flatMap(_.defn)) match
            case S(cls) =>
              ClassLikeType(cls.sym, cls.tparams.map(_ => freshWildcard(sym)))
            case _ =>
              error(msg"Cannot match ${scrutinee.toString} as ${sym.toString}" -> split.toLoc :: Nil)
              Bot
          constrain(tryMkMono(scrutineeTy, scrutinee), clsTy)
          val (paramList, tps, isGeneric, ext) = sym.asCls.flatMap(_.defn) match
            case S(clsDef) =>
              val isGeneric = clsDef.annotations.exists {
                case Annot.Modifier(syntax.Keyword.data) => true
                case _ => false
              }
              val ext = clsDef.ext match
                case S(Term.New(p: Term, _, _)) => p
                case _ => Term.Error
              (clsDef.paramsOpt.map(p => p.params).getOrElse(Nil), clsDef.tparams, isGeneric, ext)
            case N =>
              error(msg"${sym.toString} is not a valid constructor." -> split.toLoc :: Nil)
              (Nil, Nil, false, Term.Error)
          val params = paramsOpt.getOrElse(Nil)
          if params.length != paramList.length then
            error(msg"${sym.toString} is not a valid constructor." -> split.toLoc :: Nil)
            (Bot, Bot, sym :: Nil, false)
          else
            val nestCtx = if isGeneric then ctx.nextLevel else ctx.nest
            tps.foreach {
              case TyParam(_, _, targ) =>
                val ty = if isGeneric then freshVar(targ)(using nestCtx) else freshWildcard(targ)(using nestCtx)
                map += targ.uid -> ty
            }
            if !isGeneric then // no GADT reasoning so far
              constrain(clsTy, tryMkMono(typeAndSubstType(ext, true)(using map.toMap), scrutinee))
            params.iterator.zip(paramList).foreach:
              case (p, Param(_, _, S(ty), _)) =>
                nestCtx += p._1 -> typeAndSubstType(ty, true)(using map.toMap)
              case (_, p) =>
                error(msg"Invalid ADT parameter." -> p.toLoc :: Nil)
            val (consTy, consEff) = typeAllSplits(cons, sign)(using nestCtx)
            val (altsTy, altsEff, altCases, fallback) = typeADTMatch(alts, sign)
            val allEff = scrutineeEff | (consEff | altsEff)
            (sign.getOrElse(tryMkMono(consTy, cons) | tryMkMono(altsTy, alts)), allEff, sym :: altCases, fallback)
        case _ => lastWords(s"unexpected non-ClassLike pattern in ADT match: $pattern")
    case Split.Let(name, term, tail) =>
      val nestCtx = ctx.nest
      given InvalCtx = nestCtx
      val (termTy, termEff) = typeCheck(term)
      nestCtx += name -> termTy
      val (tailTy, tailEff, cases, fallback) = typeADTMatch(tail, sign)(using nestCtx)
      (tailTy, termEff | tailEff, cases, fallback)
    case Split.Else(alts) => sign match
      case S(sign) =>
        val (ty, res) = ascribe(alts, sign)
        (ty, res, Nil, true)
      case _ =>
        val (ty, res) = typeCheck(alts)
        (ty, res, Nil, true)
    case Split.End => (Bot, Bot, Nil, false)
    case Split.LetSplit(sym, tail) => typeADTMatch(tail, sign)
    case Split.UseSplit(sym) => typeADTMatch(sym.body, sign)

  private def typeSplit
      (split: Split, sign: Opt[GeneralType])(using ctx: InvalCtx)(using CCtx, Scope)
      : (GeneralType, Type) =
    split match
    case Split.Cons(Branch(scrutinee, pattern, cons), alts) =>
      val (scrutineeTy, scrutineeEff) = typeCheck(scrutinee)
      val nestCtx1 = ctx.nest
      val nestCtx2 = ctx.nest
      val patTy = pattern match
      case pat: FlatPattern.ClassLike =>
        pat.constructor.symbol.flatMap(_.asCls) match
          case S(sym) =>
            val (clsTy, tv, emptyTy) = sym.defn.map(sym -> _) match
            case S((sym, cls)) =>
              (ClassLikeType(sym, cls.tparams.map(_ => freshWildcard(sym))), (freshVar(new TempSymbol(S(scrutinee), "scrut"))), ClassLikeType(sym, cls.tparams.map(_ => Wildcard.empty)))
            case _ =>
              error(msg"Cannot match ${scrutinee.toString} as ${sym.toString}" -> split.toLoc :: Nil)
              (Bot, Bot, Bot)
            scrutinee match // * refine
              case Ref(sym: LocalSymbol) =>
                nestCtx1 += sym -> clsTy
                nestCtx2 += sym -> tv
              case _ => () // TODO: refine all variables holding this value?
            clsTy | (tv & Type.mkNegType(emptyTy))
          case N =>
            error(msg"Not a valid class: ${pat.constructor.describe}" -> pat.constructor.toLoc :: Nil)
            Bot
      case FlatPattern.Lit(lit) => lit match
        case _: Tree.BoolLit => InvalCtx.boolTy
        case _: Tree.IntLit => InvalCtx.intTy
        case _: Tree.DecLit => InvalCtx.numTy
        case _: Tree.StrLit => InvalCtx.strTy
        case _: Tree.UnitLit => InvalCtx.unitTy
      case (_: FlatPattern.Tuple) | (_: FlatPattern.Record) => TODO(s"tuple/record patterns in invalml split typing: $pattern")
      constrain(tryMkMono(scrutineeTy, scrutinee), patTy)
      val (consTy, consEff) = typeSplit(cons, sign)(using nestCtx1)
      val (altsTy, altsEff) = typeSplit(alts, sign)(using nestCtx2)
      val allEff = scrutineeEff | (consEff | altsEff)
      (sign.getOrElse(tryMkMono(consTy, cons) | tryMkMono(altsTy, alts)), allEff)
    case Split.Let(name, term, tail) =>
      val nestCtx = ctx.nest
      given InvalCtx = nestCtx
      val (termTy, termEff) = typeCheck(term)
      nestCtx += name -> termTy
      val (tailTy, tailEff) = typeSplit(tail, sign)(using nestCtx)
      (tailTy, termEff | tailEff)
    case Split.Else(alts) => sign match
      case S(sign) => ascribe(alts, sign)
      case _ => typeCheck(alts)
    case Split.End => (Bot, Bot)
    case Split.LetSplit(sym, tail) => typeSplit(tail, sign)
    case Split.UseSplit(sym) => typeSplit(sym.body, sign)

  private def typeAllSplits
    (split: Split, sign: Opt[GeneralType])(using ctx: InvalCtx)(using CCtx, Scope)
    : (GeneralType, Type) =
      if isADTMatch(split) then
        val (res, eff, cases, fallback) = typeADTMatch(split, sign)
        if !fallback then
          cases match // A primitive exhaustive check
            case c :: rest => // previous check already guarantees that all cases belong to the same ADT.
              adtParent.get(c.uid).flatMap(p => adtCtors.get(p.uid)) match
                case S(ctors) =>
                  val dist = cases.map(_.uid).distinct
                  if dist.length < cases.length then
                    error(msg"Duplicate match branches." -> split.toLoc :: Nil)
                  if dist.length != ctors.length then
                    error(msg"Expect ${ctors.length.toString()} cases, but ${dist.length.toString()} got." -> split.toLoc :: Nil)
                case N =>
                  error(msg"Unknown ADT constructor ${c.nme}" -> split.toLoc :: Nil)
            case Nil => ??? // impossible
        (res, eff)
      else typeSplit(split, sign)

  // * Note: currently, the returned type is not used or useful, but it could be in the future
  private def ascribe(lhs: Term, rhs: GeneralType)(using ctx: InvalCtx, scope: Scope): (GeneralType, Type) =
  trace[(GeneralType, Type)](s"${ctx.lvl}. Ascribing ${lhs.showDbg} : ${rhs.showDbg}", res => s"! ${res._2.showDbg}"):
    given CCtx = CCtx.init(lhs, S(rhs))
    (lhs, rhs) match
    case (Term.Lam(PlainParamList(params), body), ft @ PolyFunType(args, ret, eff)) => // * annoted functions
      if params.length != args.length then
        (error(msg"Cannot type this ${lhs.describe} as ${rhs.show}" -> lhs.toLoc :: Nil), Bot)
      else
        val nestCtx = ctx.nest
        val argsTy = params.zip(args).map:
          case (Param(sym = sym), ty) =>
            nestCtx += sym -> ty
            ty
        given InvalCtx = nestCtx
        val (_, effTy) = ascribe(body, ret)
        constrain(effTy, eff)
        (ft, Bot)
    case (Term.Lam(params, body), ft @ FunType(args, ret, eff)) => ascribe(lhs, PolyFunType(args, ret, eff))
    case (term, pt @ PolyType(_, outer, _)) => // * generalize
      val nextCtx = outer match
        case S(outer) => ctx.nestWithOuter(outer)
        case N => ctx.nextLevel
      given InvalCtx = nextCtx
      constrain(ascribe(term, skolemize(pt))._2, Bot) // * never generalize terms with effects
      (pt, Bot)
    case (Term.IfLike(_, IfLikeForm.ReturningIf, split), ty) => // * propagate
      typeAllSplits(split.getExpandedSplit, S(ty))
    case (Term.Asc(term, ty), rhs) =>
      ascribe(term, typeType(ty))
      ascribe(term, rhs)
    case _ =>
      val (lhsTy, eff) = typeCheck(lhs)
      rhs match
        case pf: PolyFunType if pf.isPoly =>
          (error(msg"Cannot type non-function term ${lhs.toString} as ${rhs.show}" -> lhs.toLoc :: Nil), Bot)
        case _ =>
          constrain(tryMkMono(lhsTy, lhs), monoOrErr(rhs, lhs))
          (rhs, eff)

  // TODO: t -> loc when toLoc is implemented
  private def app(lhs: (GeneralType, Type), rhs: Ls[Elem], t: Term)
      (using ctx: InvalCtx)(using CCtx, Scope)
      : (GeneralType, Type) =
    lhs match
    case (PolyFunType(params, ret, eff), lhsEff) =>
      // * if the function type is known, we can directly use it
      if params.length != rhs.length
      then (error(msg"Incorrect number of arguments" -> t.toLoc :: Nil), Bot)
      else
        var resEff: Type = lhsEff | eff
        rhs.lazyZip(params).foreach:
          case (f: Fld, t) =>
            val (ty, ef) = ascribe(f.term, t)
            resEff |= ef
          case (spd: Spd, _) => TODO(s"spread arguments: $spd")
        (ret, resEff)
    case (FunType(params, ret, eff), lhsEff) => app((PolyFunType(params, ret, eff), lhsEff), rhs, t)
    case (ty: PolyType, eff) => app((instantiate(ty), eff), rhs, t)
    case (funTy, lhsEff) =>
      val (argTy, argEff) = rhs.flatMap:
          case f: Fld =>
            val (ty, eff) = typeCheck(f.term)
            Left(ty) :: Right(eff) :: Nil
          case spd: Spd => TODO(s"spread arguments: $spd")
        .partitionMap(x => x)
      val effVar = freshVar(new TempSymbol(S(t), "eff"))
      val retVar = freshVar(new TempSymbol(S(t), "app"))
      constrain(tryMkMono(funTy, t), FunType(argTy.map((tryMkMono(_, t))), retVar, effVar))
      (retVar, argEff.foldLeft[Type](effVar | lhsEff)((res, e) => res | e))

  private def skolemize(ty: PolyType)(using ctx: InvalCtx) = ty.skolemize(infVarState.nextUid, ctx.lvl)(tl)

  // TODO: implement toLoc
  private def monoOrErr(ty: GeneralType, sc: Located)(using InvalCtx) =
    ty.monoOr(error(msg"General type is not allowed here." -> sc.toLoc :: Nil))

  // * Try to instantiate the given type if it is forall quantified
  private def tryMkMono(ty: GeneralType, sc: Located)(using InvalCtx, Scope): Type = ty match
    case pt: PolyType => tryMkMono(instantiate(pt), sc)
    case ft: PolyFunType =>
      ft.monoOr(error(msg"Expected a monomorphic type or an instantiable type here, but ${ty.show} found" -> sc.toLoc :: Nil))
    case ty: Type => ty
  
  private def createADTCtor(clsDef: ClassDef, resTy: Term)(using ctx: InvalCtx, scope: Scope, cctx: CCtx) =
    val nestCtx = ctx.nextLevel
    given InvalCtx = nestCtx
    val map = HashMap[Uid[Symbol], TypeArg]()
    val isGeneric = clsDef.annotations.exists {
      case Annot.Modifier(syntax.Keyword.data) => true
      case _ => false
    }
    val targs = clsDef.tparams.map {
      case TyParam(_, vce, targ) =>
        val ty = vce match
          case S(v) =>
            val tv = freshVar(targ)
            if v then Wildcard.out(tv) else Wildcard.in(tv)
          case _ => if isGeneric then freshVar(targ) else freshWildcard(targ)
        map += targ.uid -> ty
        ty
    }
    addADTCtor(clsDef.ext.flatMap(n => n.cls.symbol).getOrElse(???), clsDef.sym)
    clsDef match
      case clsDef: ClassDef.Plain =>
        ctx += clsDef.bsym -> typeAndSubstType(resTy, true)(using map.toMap)
      case clsDef: ClassDef.Parameterized =>
        if clsDef.tparams.isEmpty then
          ctx += clsDef.bsym -> PolyFunType(clsDef.params.params.map {
            case Param(_, _, S(ty), _) => typeType(ty)
            case p =>
              error(msg"Invalid ADT parameter." -> p.toLoc :: Nil)
              Bot
          }, typeAndSubstType(resTy, true)(using map.toMap), Bot)
        else
          ctx += clsDef.bsym -> PolyType(targs.flatMap {
            case Wildcard(in: InfVar, out: InfVar) => in :: out :: Nil
            case Wildcard(in: InfVar, _) => in :: Nil
            case Wildcard(_, out: InfVar) => out :: Nil
            case v: InfVar => v :: Nil
            case other => lastWords(s"unexpected non-InfVar type argument in ADT ctor: $other")
          }, N, PolyFunType(clsDef.params.params.map {
            case Param(_, _, S(ty), _) => typeAndSubstType(ty, true)(using map.toMap)
            case p =>
              error(msg"Invalid ADT parameter." -> p.toLoc :: Nil)
              Bot
          }, typeAndSubstType(resTy, true)(using map.toMap), Bot))

  private def typeCheck(t: Term)(using ctx: InvalCtx, scope: Scope): (GeneralType, Type) =
  trace[(GeneralType, Type)](s"${ctx.lvl}. Typing ${t.showDbg}", res => s": (${res._1.showDbg}, ${res._2.showDbg})"):
    given CCtx = CCtx.init(t, N)
    t match
      case Term.Annotated(Annot.Untyped, _) => (Bot, Bot)
      case sel @ Term.SynthSel(Ref(_: TopLevelSymbol), nme)
        if sel.symbol.isDefined =>
        typeCheck(Ref(sel.symbol.get)(sel.nme, 666, N)) // FIXME 666
      case Ref(sym) =>
        ctx.get(sym) match
          case Some(ty) => (ty, Bot)
          case _ =>
            // (error(msg"Variable not found: ${sym.nme} (${sym.toString} @ ${sym.uid.toString})"
            (error(msg"Variable not found: ${sym.nme}"
              -> t.toLoc :: Nil), Bot)
      case Blk(stats, res) =>
        val effBuff = ListBuffer.empty[Type]
        def goStats(stats: Ls[Statement]): Unit = stats match
          case Nil => ()
          case (term: Term) :: stats =>
            effBuff += typeCheck(term)._2
            goStats(stats)
          case LetDecl(sym, _) :: DefineVar(sym2, rhs) :: stats =>
            require(sym2 is sym)
            val (rhsTy, eff) = typeCheck(rhs)
            effBuff += eff
            ctx += sym -> rhsTy
            goStats(stats)
          case (td @ TermDefinition(k = Fun, params = ps :: Nil, sign = sig, body = S(body))) :: stats =>
            typeFunDef(td.sym, Term.Lam(ps, body), sig)
            goStats(stats)
          case (td @ TermDefinition(k = Fun, params = Nil, sign = sig, body = S(body))) :: stats =>
            typeFunDef(td.sym, body, sig)  // * may be a case expressions
            goStats(stats)
          case (td1 @ TermDefinition(k = Fun, sign = S(sig), body = None)) :: (td2 @ TermDefinition(k = Fun, body = S(body))) :: stats
            if td1.sym === td2.sym => goStats(td2 :: stats) // * avoid type check signatures twice
          case (td @ TermDefinition(k = Fun, sign = S(sig), body = None)) :: stats =>
            ctx += td.sym -> typeType(sig)
            goStats(stats)
          case (clsDef: ClassDef) :: stats =>
            typeNames.add(clsDef.sym.nme)
            clsDef.ext match
              case S(Term.New(ty, _, N)) => createADTCtor(clsDef, ty)
              case _ => ()
            goStats(stats)
          case (modDef: ModuleOrObjectDef) :: stats =>
            typeNames.add(modDef.sym.nme)
            goStats(stats)
          case Import(sym, str, pth) :: stats =>
            goStats(stats) // TODO:
          case stat :: _ =>
            TODO(stat)
        goStats(stats)
        val (ty, eff) = typeCheck(res)
        (ty, effBuff.foldLeft(eff)((res, e) => res | e))
      case UnitVal() => (InvalCtx.unitTy, Bot)
      case Lit(lit) => ((lit match
        case _: IntLit => InvalCtx.intTy
        case _: DecLit => InvalCtx.numTy
        case _: StrLit => InvalCtx.strTy
        case _: UnitLit => InvalCtx.unitTy
        case _: BoolLit => InvalCtx.boolTy), Bot)
      case Lam(PlainParamList(params), body) =>
        val nestCtx = ctx.nest
        given InvalCtx = nestCtx
        val tvs = params.map:
          case Param(_, sym, sign, _) =>
            val ty = sign.map(s => typeType(s)(using nestCtx)).getOrElse(freshVar(sym))
            nestCtx += sym -> ty
            ty
        val (bodyTy, eff) = typeCheck(body)
        (PolyFunType(tvs, bodyTy, eff), Bot)
      case Term.SelProj(term, cls, field) =>
        val (ty, eff) = typeCheck(term)
        cls.symbol.flatMap(_.asCls.flatMap(sym => sym.defn.map(sym -> _))) match
          case S(clsSym -> clsDfn) =>
            val map = HashMap[Uid[Symbol], TypeArg]()
            val targs = clsDfn.tparams.map {
              case TyParam(_, _, targ) =>
                val ty = freshWildcard(targ)
                map += targ.uid -> ty
                ty
            }
            constrain(tryMkMono(ty, term), ClassLikeType(clsSym, targs))
            require(clsDfn.paramsOpt.forall(_.restParam.isEmpty))
            (clsDfn.paramsOpt.fold(Nil)(_.params).map {
              case Param(_, sym, sign, _) =>
                if sym.nme === field.name then sign else N
            }.filter(_.isDefined)) match
              case S(res) :: Nil => (typeAndSubstType(res, pol = true)(using map.toMap), eff)
              case _ => (error(msg"${field.name} is not a valid member in class ${clsSym.nme}" -> t.toLoc :: Nil), Bot)
          case N => 
            (error(msg"Not a valid class: ${cls.describe}" -> cls.toLoc :: Nil), Bot)
      case t @ Term.App(lhs, Term.Tup(rhs)) =>
        val (funTy, lhsEff) = typeCheck(lhs)
        app((funTy, lhsEff), rhs, t)
      case Term.New(cls, args, N) =>
        cls.symbol.flatMap(_.asCls.flatMap(_.defn)) match
        case S(clsDfn: ClassDef.Parameterized) =>
          require(clsDfn.paramsOpt.forall(_.restParam.isEmpty))
          val argsList = args match
            case Nil => Nil
            case Term.Tup(elems) :: Nil => elems.map:
              case PlainFld(term) => term
              case _ => ???
            case _ => ???
          if argsList.length != clsDfn.params.params.length then
            (error(msg"The number of parameters is incorrect" -> t.toLoc :: Nil), Bot)
          else
            val map = HashMap[Uid[Symbol], TypeArg]()
            val targs = clsDfn.tparams.map {
              case TyParam(_, S(_), targ) =>
                val ty = freshVar(targ)
                map += targ.uid -> ty
                ty
              case TyParam(_, N, targ) =>
                // val ty = freshWildcard // FIXME probably not correct
                val ty = freshVar(targ)
                map += targ.uid -> ty
                ty
            }
            val effBuff = ListBuffer.empty[Type]
            require(clsDfn.paramsOpt.forall(_.restParam.isEmpty))
            argsList.iterator.zip(clsDfn.params.params).foreach {
              case (arg, Param(sign = S(sign))) =>
                val (ty, eff) = ascribe(arg, typeAndSubstType(sign, pol = true)(using map.toMap))
                effBuff += eff
              case _ => ???
            }
            (ClassLikeType(clsDfn.sym, targs), effBuff.foldLeft[Type](Bot)((res, e) => res | e))
        case S(clsDfn: ClassDef.Plain) => ??? // TODO
        case N => 
          (error(msg"Not a valid class: ${cls.describe}" -> cls.toLoc :: Nil), Bot)
      case Term.Asc(term, ty) =>
        val res = typeType(ty)(using ctx)
        ascribe(term, res)
      case Term.IfLike(_, IfLikeForm.ReturningIf, split) => typeAllSplits(split.getExpandedSplit, N)
      case reg @ Term.Region(sym, body) =>
        val sk = freshReg(sym)(using ctx)
        val nestCtx = ctx.nestReg(sk)
        given InvalCtx = nestCtx
        nestCtx += sym -> InvalCtx.regionTy(sk)
        val (res, eff) = typeCheck(body)
        val tv = freshVar(new TempSymbol(S(reg), "eff"))(using ctx)
        constrain(eff, tv | sk)
        (extrude(res)(using ctx, true), tv)
      case Term.RegRef(reg, value) =>
        val (regTy, regEff) = typeCheck(reg)
        val (valTy, valEff) = typeCheck(value)
        val sk = freshVar(new TempSymbol(S(reg), "reg"))
        constrain(tryMkMono(regTy, reg), InvalCtx.regionTy(sk))
        (InvalCtx.refTy(tryMkMono(valTy, value), sk), sk | (regEff | valEff))
      case Term.SetRef(lhs, rhs) =>
        val (lhsTy, lhsEff) = typeCheck(lhs)
        val (rhsTy, rhsEff) = typeCheck(rhs)
        val sk = freshVar(new TempSymbol(S(lhs), "reg"))
        constrain(tryMkMono(lhsTy, lhs), InvalCtx.refTy(tryMkMono(rhsTy, rhs), sk))
        (tryMkMono(rhsTy, rhs), sk | (lhsEff | rhsEff))
      case Term.Deref(ref) =>
        val (refTy, refEff) = typeCheck(ref)
        val sk = freshVar(new TempSymbol(S(ref), "reg"))
        val ctnt = freshVar(new TempSymbol(S(ref), "ref"))
        constrain(tryMkMono(refTy, ref), InvalCtx.refTy(ctnt, sk))
        (ctnt, sk | refEff)
      case Term.Quoted(body) =>
        val nestCtx = ctx.nest
        given InvalCtx = nestCtx
        val (ty, ctxTy, eff) = typeCode(body)
        (InvalCtx.codeTy(ty, ctxTy), eff)
      case _: Term.Unquoted =>
        (error(msg"Unquote should nest in quasiquote" -> t.toLoc :: Nil), Bot)
      case Throw(e) =>
        val (ty, eff) = typeCheck(e)
        constrain(tryMkMono(ty, e), InvalCtx.errTy)
        (Bot, eff)
      case Term.Error =>
        (Bot, Bot) // TODO: error type?
      case _ =>
        (error(msg"Term shape not yet supported by InvalML: ${t.toString}" -> t.toLoc :: Nil), Bot)

  def typePurely(t: Term)(using InvalCtx, Scope): GeneralType =
    val (ty, eff) = typeCheck(t)
    given CCtx = CCtx.init(t, N)
    constrain(eff, Bot)
    ty
