package hkmc2
package bbml


import scala.collection.mutable.{LinkedHashSet, HashMap, ListBuffer}
import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import utils.*

import Message.MessageContext
import semantics.*, semantics.Term.*
import Elaborator.Ctx
import syntax.*
import Tree.*


object InfVarUid extends Uid.Handler[InfVar]


final case class BbCtx(
  raise: Raise,
  ctx: Ctx,
  parent: Option[BbCtx],
  lvl: Int,
  clsDefs: HashMap[Str, ClassDef],
  env: HashMap[Uid[Symbol], GeneralType],
  quoteSkolemEnv: HashMap[Uid[Symbol], InfVar], // * SkolemTag for variables in quasiquotes
):
  def +=(p: Symbol -> GeneralType): Unit = env += p._1.uid -> p._2
  def get(sym: Symbol): Option[GeneralType] = env.get(sym.uid) orElse parent.dlof(_.get(sym))(None)
  def *=(cls: ClassDef): Unit = clsDefs += cls.sym.id.name -> cls
  def getCls(name: Str): Option[TypeSymbol] =
    for
      elem <- ctx.get(name)
      sym <- elem.symbol
      cls <- sym.asTpe
    yield cls
  def &=(p: (Symbol, Type, InfVar)): Unit =
    env += p._1.uid -> BbCtx.varTy(p._2, p._3)(using this)
    quoteSkolemEnv += p._1.uid -> p._3
  def getSk(sym: Symbol): Option[Type] = quoteSkolemEnv.get(sym.uid) orElse parent.dlof(_.getSk(sym))(None)
  def nest: BbCtx = copy(parent = Some(this))
  def nextLevel: BbCtx = copy(lvl = lvl + 1)

given (using ctx: BbCtx): Raise = ctx.raise

object BbCtx:
  def allocTy(using ctx: BbCtx): Type = ClassLikeType(ctx.getCls("Alloc").get, Nil)
  def intTy(using ctx: BbCtx): Type = ClassLikeType(ctx.getCls("Int").get, Nil)
  def numTy(using ctx: BbCtx): Type = ClassLikeType(ctx.getCls("Num").get, Nil)
  def strTy(using ctx: BbCtx): Type = ClassLikeType(ctx.getCls("Str").get, Nil)
  def boolTy(using ctx: BbCtx): Type = ClassLikeType(ctx.getCls("Bool").get, Nil)
  private def codeBaseTy(ct: TypeArg, cr: TypeArg, isVar: TypeArg)(using ctx: BbCtx): Type =
    ClassLikeType(ctx.getCls("CodeBase").get, ct :: cr :: isVar :: Nil)
  def codeTy(ct: Type, cr: Type)(using ctx: BbCtx): Type =
    codeBaseTy(Wildcard.out(ct), Wildcard.out(cr), Wildcard.out(Top))
  def varTy(ct: Type, cr: Type)(using ctx: BbCtx): Type =
    codeBaseTy(ct, Wildcard(cr, cr), Wildcard.out(Bot))
  def regionTy(sk: Type)(using ctx: BbCtx): Type =
    ClassLikeType(ctx.getCls("Region").get, Wildcard(sk, sk) :: Nil)
  def refTy(ct: Type, sk: Type)(using ctx: BbCtx): Type =
    ClassLikeType(ctx.getCls("Ref").get, Wildcard(ct, ct) :: Wildcard.out(sk) :: Nil)
  def init(raise: Raise)(using Elaborator.State, Elaborator.Ctx): BbCtx =
    new BbCtx(raise, summon, None, 1, HashMap.empty, HashMap.empty, HashMap.empty)
end BbCtx


class BBTyper(using elState: Elaborator.State, tl: TL):
  import elState.nextUid
  import tl.{trace, log}
  
  private val infVarState = new InfVarUid.State()
  private val solver = new ConstraintSolver(infVarState, tl)

  private def freshSkolem(using ctx: BbCtx): InfVar =
    InfVar(ctx.lvl, infVarState.nextUid, new VarState(), true)
  private def freshVar(using ctx: BbCtx): InfVar =
    InfVar(ctx.lvl, infVarState.nextUid, new VarState(), false)
  private def freshWildcard(using ctx: BbCtx) =
    val in = freshVar
    val out = freshVar
    // in.state.upperBounds ::= out // * Not needed for soundness; complicates inferred types
    Wildcard(in, out)

  private def allocType(using BbCtx): Type =
    BbCtx.allocTy

  private def error(msg: Ls[Message -> Opt[Loc]])(using BbCtx) =
    raise(ErrorReport(msg))
    Bot // TODO: error type?


  private def typeAndSubstType
      (ty: Term, pol: Bool)(using map: Map[Uid[Symbol], TypeArg])(using ctx: BbCtx, cctx: CCtx)
      : GeneralType =
  trace[GeneralType](s"${ctx.lvl}. Typing type ${ty.toString}", r => s"~> $r"):
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
            if sym.nme === "Alloc" then
              allocType
            else
              error(msg"Variable not found: ${sym.nme}" -> ty.toLoc :: Nil)
    case FunTy(Term.Tup(params), ret, eff) =>
      PolyFunType(params.map {
        case Fld(_, p, _) => typeAndSubstType(p, !pol)
      }, typeAndSubstType(ret, pol), eff.map(e => typeAndSubstType(e, pol) match {
        case t: Type => t
        case _ => error(msg"Effect cannot be polymorphic." -> ty.toLoc :: Nil)
      }).getOrElse(Bot))
    case Term.Forall(tvs, body) =>
      val nestCtx = ctx.nextLevel
      given BbCtx = nestCtx
      genPolyType(tvs, typeAndSubstType(body, pol))
    case Term.TyApp(cls, targs) =>
      // log(s"Type application: ${cls.nme} with ${targs}")
      cls.symbol.flatMap(_.asTpe) match
      case S(tpeSym) =>
        if tpeSym.nme === "Any" then Top
        else if tpeSym.nme === "Nothing" then Bot
        else
          val defn = tpeSym.defn.get
          if targs.length != defn.tparams.length then
            error(msg"Type arguments do not match class definition" -> ty.toLoc :: Nil)
          val ts = defn.tparams.lazyZip(targs).map: (tp, t) =>
            t match
            case Term.WildcardTy(in, out) => Wildcard(
                in.map(t => mono(t, pol)).getOrElse(Bot),
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
    case _ =>
      ty.symbol.flatMap(_.asTpe) match
      case S(cls: (ClassSymbol | TypeAliasSymbol)) => typeAndSubstType(Term.TyApp(ty, Nil), pol)
      case _ => error(msg"${ty.symbol.get.getClass.toString()} is not a valid type" -> ty.toLoc :: Nil) // TODO

  private def genPolyType(tvs: Ls[QuantVar], body: => GeneralType)(using ctx: BbCtx, cctx: CCtx) =
    val bds = tvs.map:
      case qv @ QuantVar(sym, ub, lb) =>
        val tv = freshVar
        ctx += sym -> tv // TODO: a type var symbol may be better...
        tv -> qv
    bds.foreach:
      case (tv, QuantVar(_, ub, lb)) =>
        ub.foreach(ub => tv.state.upperBounds ::= typeMonoType(ub))
        lb.foreach(lb => tv.state.lowerBounds ::= typeMonoType(lb))
        val lbty = tv.state.lowerBounds.foldLeft[Type](Bot)(_ | _)
        val ubty = tv.state.upperBounds.foldLeft[Type](Top)(_ & _)
        constrain(lbty, ubty)
    PolyType(bds.map(_._1), body)

  private def typeMonoType(ty: Term)(using ctx: BbCtx, cctx: CCtx): Type = monoOrErr(typeType(ty), ty)

  private def typeType(ty: Term)(using ctx: BbCtx, cctx: CCtx): GeneralType =
    typeAndSubstType(ty, pol = true)(using Map.empty)
  
  private def instantiate(ty: PolyType)(using ctx: BbCtx): GeneralType = ty.instantiate(infVarState.nextUid, ctx.lvl)(tl)

  private def extrude(ty: GeneralType)(using ctx: BbCtx, pol: Bool): GeneralType = ty match
    case ty: Type => solver.extrude(ty)(using ctx.lvl, pol, HashMap.empty)
    case PolyType(tvs, body) => PolyType(tvs, extrude(body))
    case PolyFunType(args, ret, eff) =>
      PolyFunType(args.map(extrude(_)(using ctx, !pol)), extrude(ret), solver.extrude(eff)(using ctx.lvl, pol, HashMap.empty))

  private def constrain(lhs: Type, rhs: Type)(using ctx: BbCtx, cctx: CCtx): Unit =
    solver.constrain(lhs, rhs)

  // TODO: content type
  private def typeCode(code: Term)(using ctx: BbCtx): (Type, Type, Type) =
    given CCtx = CCtx.init(code, N)
    code match
    case Lit(lit) => ((lit match
      case _: IntLit => BbCtx.intTy
      case _: DecLit => BbCtx.numTy
      case _: StrLit => BbCtx.strTy
      case _: UnitLit => Top
      case _: BoolLit => BbCtx.boolTy), Bot, Bot)
    case Ref(sym: Symbol) if sym.nme === "error" => (Bot, Bot, Bot)
    case Lam(params, body) =>
      val nestCtx = ctx.nextLevel
      given BbCtx = nestCtx
      val bds = params.map:
        case Param(_, sym, _) =>
          val tv = freshVar
          val sk = freshSkolem
          nestCtx &= (sym, tv, sk)
          (tv, sk)
      val (bodyTy, ctxTy, eff) = typeCode(body)
      val res = freshVar(using ctx)
      constrain(ctxTy, bds.foldLeft[Type](res)((res, bd) => res | bd._2))
      (FunType(bds.map(_._1), bodyTy, Bot), res, eff)
    case Term.App(lhs, Term.Tup(rhs)) =>
      val (lhsTy, lhsCtx, lhsEff) = typeCode(lhs)
      val (rhsTy, rhsCtx, rhsEff) = rhs.foldLeft[(Ls[Type], Type, Type)]((Nil, Bot, Bot))((res, p) =>
        val (ty, ctx, eff) = typeCode(p.value)
        (ty :: res._1, res._2 | ctx, res._3 | eff)
      )
      val resTy = freshVar
      constrain(lhsTy, FunType(rhsTy.reverse, resTy, Bot)) // TODO: right
      (resTy, lhsCtx | rhsCtx, lhsEff | rhsEff)
    case Term.Unquoted(body) =>
      val (ty, eff) = typeCheck(body)
      val tv = freshVar
      val cr = freshVar
      constrain(tryMkMono(ty, body), BbCtx.codeTy(tv, cr))
      (tv, cr, eff)
    case Term.Blk(LetDecl(sym) :: DefineVar(sym2, rhs) :: Nil, body) if sym2 is sym => // TODO: more than one!!
      val (rhsTy, rhsCtx, rhsEff) = typeCode(rhs)(using ctx)
      val nestCtx = ctx.nextLevel
      given BbCtx = nestCtx
      val sk = freshSkolem
      nestCtx &= (sym, rhsTy, sk)
      val (bodyTy, bodyCtx, bodyEff) = typeCode(body)
      val res = freshVar(using ctx)
      constrain(bodyCtx, sk | res)
      (bodyTy, rhsCtx | res, rhsEff | bodyEff)
    case Term.IfLike(Keyword.`if`, Split.Cons(Branch(cond, Pattern.LitPat(BoolLit(true)), Split.Else(cons)), Split.Else(alts))) =>
      val (condTy, condCtx, condEff) = typeCode(cond)
      val (consTy, consCtx, consEff) = typeCode(cons)
      val (altsTy, altsCtx, altsEff) = typeCode(alts)
      constrain(condTy, BbCtx.boolTy)
      (consTy | altsTy, condCtx | consCtx | altsCtx, condEff | consEff | altsEff)
    case _ =>
      (error(msg"Cannot quote ${code.toString}" -> code.toLoc :: Nil), Bot, Bot)

  private def typeFunDef(sym: Symbol, lam: Term, sig: Opt[Term], pctx: BbCtx)(using ctx: BbCtx, cctx: CCtx) = lam match
    case Term.Lam(params, body) => sig match
      case S(sig) =>
        val sigTy = typeType(sig)(using ctx)
        pctx += sym -> sigTy
        ascribe(lam, sigTy)
        ()
      case N =>
        given BbCtx = ctx.nextLevel
        val funTyV = freshVar
        pctx += sym -> funTyV // for recursive functions
        val (res, _) = typeCheck(lam)
        val funTy = tryMkMono(res, lam)
        given CCtx = CCtx.init(lam, N)
        constrain(funTy, funTyV)(using ctx)
        pctx += sym -> PolyType.generalize(funTy, 1)
    case _ => error(msg"Function definition shape not yet supported for ${sym.nme}" -> lam.toLoc :: Nil)

  private def typeSplit
      (split: Split, sign: Opt[GeneralType])(using ctx: BbCtx)(using CCtx)
      : (GeneralType, Type) =
    split match
    case Split.Cons(Branch(scrutinee, Pattern.ClassLike(sym, _, _, _), cons), alts) =>
      // * Pattern matching
      val (clsTy, tv, emptyTy) = ctx.getCls(sym.nme).flatMap(_.defn) match
        case S(cls) =>
          (ClassLikeType(sym, cls.tparams.map(_ => freshWildcard)), freshVar, ClassLikeType(sym, cls.tparams.map(_ => Wildcard.empty)))
        case _ =>
          error(msg"Cannot match ${scrutinee.toString} as ${sym.toString}" -> split.toLoc :: Nil)
          (Bot, Bot, Bot)
      val (scrutineeTy, scrutineeEff) = typeCheck(scrutinee)
      constrain(tryMkMono(scrutineeTy, scrutinee), clsTy | (tv & Type.mkNegType(emptyTy)))
      val nestCtx1 = ctx.nest
      val nestCtx2 = ctx.nest
      scrutinee match // * refine
        case Ref(sym: LocalSymbol) =>
          nestCtx1 += sym -> clsTy
          nestCtx2 += sym -> tv
        case _ => () // TODO: refine all variables holding this value?
      val (consTy, consEff) = typeSplit(cons, sign)(using nestCtx1)
      val (altsTy, altsEff) = typeSplit(alts, sign)(using nestCtx2)
      val allEff = scrutineeEff | (consEff | altsEff)
      (sign.getOrElse(tryMkMono(consTy, cons) | tryMkMono(altsTy, alts)), allEff)
    case Split.Let(name, term, tail) =>
      val nestCtx = ctx.nest
      given BbCtx = nestCtx
      val (termTy, termEff) = typeCheck(term)
      val sk = freshSkolem
      nestCtx += name -> termTy
      val (tailTy, tailEff) = typeSplit(tail, sign)(using nestCtx)
      (tailTy, termEff | tailEff)
    case Split.Else(alts) => sign match
      case S(sign) => ascribe(alts, sign)
      case _ => typeCheck(alts)
    case Split.End => ???

  // * Note: currently, the returned type is not used or useful, but it could be in the future
  private def ascribe(lhs: Term, rhs: GeneralType)(using ctx: BbCtx): (GeneralType, Type) =
  trace[(GeneralType, Type)](s"${ctx.lvl}. Ascribing ${lhs.showDbg} : ${rhs}", res => s"! ${res._2}"):
    given CCtx = CCtx.init(lhs, S(rhs))
    (lhs, rhs) match
    case (Term.Lam(params, body), ft @ PolyFunType(args, ret, eff)) => // * annoted functions
      if params.length != args.length then
         (error(msg"Cannot type function ${lhs.toString} as ${rhs.toString}" -> lhs.toLoc :: Nil), Bot)
      else
        val nestCtx = ctx.nest
        val argsTy = params.zip(args).map:
          case (Param(_, sym, _), ty) =>
            nestCtx += sym -> ty
            ty
        given BbCtx = nestCtx
        val (_, effTy) = ascribe(body, ret)
        constrain(effTy, eff)
        (ft, Bot)
    case (Term.Lam(params, body), ft @ FunType(args, ret, eff)) => ascribe(lhs, PolyFunType(args, ret, eff))
    case (term, pt: PolyType) => // * generalize
      val nextCtx = ctx.nextLevel
      given BbCtx = nextCtx
      constrain(ascribe(term, skolemize(pt))._2, Bot) // * never generalize terms with effects
      (pt, Bot)
    case (Term.IfLike(Keyword.`if`, branches), ty) => // * propagate
      typeSplit(branches, S(ty))
    case (Term.Asc(term, ty), rhs) =>
      ascribe(term, typeType(ty))
      ascribe(term, rhs)
    case _ =>
      val (lhsTy, eff) = typeCheck(lhs)
      rhs match
        case pf: PolyFunType if pf.isPoly =>
          (error(msg"Cannot type non-function term ${lhs.toString} as ${rhs.toString}" -> lhs.toLoc :: Nil), Bot)
        case _ =>
          constrain(tryMkMono(lhsTy, lhs), monoOrErr(rhs, lhs))
          (rhs, eff)

  // TODO: t -> loc when toLoc is implemented
  private def app(lhs: (GeneralType, Type), rhs: Ls[Fld], t: Term)
      (using ctx: BbCtx)(using CCtx)
      : (GeneralType, Type) =
    lhs match
    case (PolyFunType(params, ret, eff), lhsEff) =>
      // * if the function type is known, we can directly use it
      if params.length != rhs.length
      then (error(msg"Incorrect number of arguments" -> t.toLoc :: Nil), Bot)
      else
        var resEff: Type = lhsEff | eff
        rhs.lazyZip(params).foreach: (f, t) =>
          val (ty, ef) = ascribe(f.value, t)
          resEff |= ef
        (ret, resEff)
    case (FunType(params, ret, eff), lhsEff) => app((PolyFunType(params, ret, eff), lhsEff), rhs, t)
    case (ty: PolyType, eff) => app((instantiate(ty), eff), rhs, t)
    case (funTy, lhsEff) =>
      val (argTy, argEff) = rhs.flatMap(f =>
        val (ty, eff) = typeCheck(f.value)
        Left(ty) :: Right(eff) :: Nil
      ).partitionMap(x => x)
      val effVar = freshVar
      val retVar = freshVar
      constrain(tryMkMono(funTy, t), FunType(argTy.map((tryMkMono(_, t))), retVar, effVar))
      (retVar, argEff.foldLeft[Type](effVar | lhsEff)((res, e) => res | e))

  private def skolemize(ty: PolyType)(using ctx: BbCtx) = ty.skolemize(infVarState.nextUid, ctx.lvl)(tl)

  // TODO: implement toLoc
  private def monoOrErr(ty: GeneralType, sc: Located)(using BbCtx) =
    ty.monoOr(error(msg"General type is not allowed here." -> sc.toLoc :: Nil))

  // * Try to instantiate the given type if it is forall quantified
  private def tryMkMono(ty: GeneralType, sc: Located)(using BbCtx): Type = ty match
    case pt: PolyType => tryMkMono(instantiate(pt), sc)
    case ft: PolyFunType =>
      ft.monoOr(error(msg"Expected a monomorphic type or an instantiable type here, but ${ty.toString} found" -> sc.toLoc :: Nil))
    case ty: Type => ty
  
  private def typeCheck(t: Term)(using ctx: BbCtx): (GeneralType, Type) =
  trace[(GeneralType, Type)](s"${ctx.lvl}. Typing ${t.showDbg}", res => s": $res"):
    given CCtx = CCtx.init(t, N)
    t match
      case sel @ Term.Sel(Ref(_: TopLevelSymbol), nme)
        if sel.symbol.isDefined =>
        typeCheck(Ref(sel.symbol.get)(sel.nme, 666)) // FIXME 666
      case Ref(sym) =>
        ctx.get(sym) match
          case Some(ty) => (ty, Bot)
          case _ =>
            // (error(msg"Variable not found: ${sym.nme} (${sym.toString} @ ${sym.uid.toString})"
            (error(msg"Variable not found: ${sym.nme}"
              -> t.toLoc :: Nil), Bot)
      case Blk(stats, res) =>
        val nestCtx = ctx.nest
        given BbCtx = nestCtx
        val effBuff = ListBuffer.empty[Type]
        def goStats(stats: Ls[Statement]): Unit = stats match
          case Nil => ()
          case (term: Term) :: stats =>
            effBuff += typeCheck(term)._2
            goStats(stats)
          case LetDecl(sym) :: DefineVar(sym2, rhs) :: stats =>
            require(sym2 is sym)
            val (rhsTy, eff) = typeCheck(rhs)
            effBuff += eff
            nestCtx += sym -> rhsTy
            goStats(stats)
          case TermDefinition(_, Fun, sym, ParamList(_, ps) :: Nil, sig, Some(body), _) :: stats =>
            typeFunDef(sym, Term.Lam(ps, body), sig, ctx)
            goStats(stats)
          case TermDefinition(_, Fun, sym, Nil, sig, Some(body), _) :: stats =>
            typeFunDef(sym, body, sig, ctx)  // * may be a case expressions
            goStats(stats)
          case TermDefinition(_, Fun, sym, _, S(sig), None, _) :: stats =>
            ctx += sym -> typeType(sig)
            goStats(stats)
          case (clsDef: ClassDef) :: stats =>
            ctx *= clsDef
            goStats(stats)
        goStats(stats)
        val (ty, eff) = typeCheck(res)
        (ty, effBuff.foldLeft(eff)((res, e) => res | e))
      case Lit(lit) => ((lit match
        case _: IntLit => BbCtx.intTy
        case _: DecLit => BbCtx.numTy
        case _: StrLit => BbCtx.strTy
        case _: UnitLit => Top
        case _: BoolLit => BbCtx.boolTy), Bot)
      case Lam(params, body) =>
        val nestCtx = ctx.nest
        given BbCtx = nestCtx
        val tvs = params.map:
          case Param(_, sym, sign) =>
            val ty = sign.map(s => typeType(s)(using nestCtx)).getOrElse(freshVar)
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
                val ty = freshWildcard
                map += targ.uid -> ty
                ty
            }
            constrain(tryMkMono(ty, term), ClassLikeType(clsSym, targs))
            (clsDfn.paramsOpt.getOrElse(Nil).map {
              case Param(_, sym, sign) =>
                if sym.nme === field.name then sign else N
            }.filter(_.isDefined)) match
              case S(res) :: Nil => (typeAndSubstType(res, pol = true)(using map.toMap), eff)
              case _ => (error(msg"${field.name} is not a valid member in class ${clsSym.nme}" -> t.toLoc :: Nil), Bot)
          case N => 
            (error(msg"Not a valid class: ${cls.describe}" -> cls.toLoc :: Nil), Bot)
      case Term.App(lhs, Term.Tup(rhs)) =>
        val (funTy, lhsEff) = typeCheck(lhs)
        app((funTy, lhsEff), rhs, t)
      case Term.New(cls, args) =>
        cls.symbol.flatMap(_.asCls.flatMap(_.defn)) match
        case S(clsDfn: ClassDef.Parameterized) =>
          if args.length != clsDfn.params.length then
            (error(msg"The number of parameters is incorrect" -> t.toLoc :: Nil), Bot)
          else
            val map = HashMap[Uid[Symbol], TypeArg]()
            val targs = clsDfn.tparams.map {
              case TyParam(_, S(_), targ) =>
                val ty = freshVar
                map += targ.uid -> ty
                ty
              case TyParam(_, N, targ) =>
                // val ty = freshWildcard // FIXME probably not correct
                val ty = freshVar
                map += targ.uid -> ty
                ty
            }
            val effBuff = ListBuffer.empty[Type]
            args.iterator.zip(clsDfn.params).foreach {
              case (arg, Param(_, _, S(sign))) =>
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
      case Term.IfLike(Keyword.`if`, branches) => typeSplit(branches, N)
      case Term.Region(sym, body) =>
        val nestCtx = ctx.nextLevel
        given BbCtx = nestCtx
        val sk = freshSkolem
        nestCtx += sym -> BbCtx.regionTy(sk)
        val (res, eff) = typeCheck(body)
        val tv = freshVar(using ctx)
        constrain(eff, tv | sk)
        (extrude(res)(using ctx, true), tv | allocType)
      case Term.RegRef(reg, value) =>
        val (regTy, regEff) = typeCheck(reg)
        val (valTy, valEff) = typeCheck(value)
        val sk = freshVar
        constrain(tryMkMono(regTy, reg), BbCtx.regionTy(sk))
        (BbCtx.refTy(tryMkMono(valTy, value), sk), sk | (regEff | valEff))
      case Term.Assgn(lhs, rhs) =>
        val (lhsTy, lhsEff) = typeCheck(lhs)
        val (rhsTy, rhsEff) = typeCheck(rhs)
        val sk = freshVar
        constrain(tryMkMono(lhsTy, lhs), BbCtx.refTy(tryMkMono(rhsTy, rhs), sk))
        (tryMkMono(rhsTy, rhs), sk | (lhsEff | rhsEff))
      case Term.Deref(ref) =>
        val (refTy, refEff) = typeCheck(ref)
        val sk = freshVar
        val ctnt = freshVar
        constrain(tryMkMono(refTy, ref), BbCtx.refTy(ctnt, sk))
        (ctnt, sk | refEff)
      case Term.Quoted(body) =>
        val nestCtx = ctx.nextLevel
        given BbCtx = nestCtx
        val (ty, ctxTy, eff) = typeCode(body)
        (BbCtx.codeTy(ty, ctxTy), eff)
      case _: Term.Unquoted =>
        (error(msg"Unquote should nest in quasiquote" -> t.toLoc :: Nil), Bot)
      case Term.Error =>
        (Bot, Bot) // TODO: error type?
      case _ =>
        (error(msg"Term shape not yet supported by BbML: ${t.toString}" -> t.toLoc :: Nil), Bot)

  def typePurely(t: Term)(using BbCtx): GeneralType =
    val (ty, eff) = typeCheck(t)
    given CCtx = CCtx.init(t, N)
    constrain(eff, allocType)
    ty
