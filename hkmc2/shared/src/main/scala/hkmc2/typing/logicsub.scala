package hkmc2
package typing
package logicsub


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
import hkmc2.codegen.ErasedType.eraseSign


class Typer(using elState: Elaborator.State, tl: TL, raise: Raise):
  import tl.{trace, log}
  private val builtinOps = Elaborator.binaryOps ++ Elaborator.unaryOps ++ Elaborator.aliasOps.keySet
  private val solver = new ConstraintSolver(elState, tl)

  private def error(msg: Ls[Message -> Opt[Loc]], extraInfo: => Opt[Any] = N)(using InfCtx) =
    raise(ErrorReport(msg, extraInfo = extraInfo))
    Bot // TODO: error type?

  private def typeNames(using ctx: InfCtx) = ctx.typeNames
  private def freshVar(origin: Symbol | Term, hint: Str = "")(using ctx: InfCtx) =
    // ctx.freshVar(origin, hint)
    InfVar(ctx.lvl, InfVarSymbol(origin, hint), false)
  private def freshWildcard(s: Symbol)(using InfCtx) = Wildcard(freshVar(s),freshVar(s))

  private def freshOuter(sym: Symbol)(using ctx: InfCtx): InfVar =
    // ctx.freshOuter(sym)
    InfVar(ctx.lvl + 1, new InfVarSymbol(sym), true)

  private def mono(ty: InfType)(using ctx: InfCtx): Opt[Type] = ty match
    case x: Type => S(x)
    case PolyFunType(args, ret, eff) =>
      val a = args.map(mono)
      val r = mono(ret)
      if (r::a).exists(_.isEmpty) then N
      else S(InfCtx.funTy(a.flatten, r.get, eff))
    case _ => N

  private def monoOrErr(ty: InfType, sc: Located)(using InfCtx): Type =
    mono(ty).getOrElse(error(msg"General type is not allowed here." -> sc.toLoc :: Nil))

  private def tryMkMono(ty: InfType, sc: Located)(using InfCtx, Scope): Type = ty match
    case pt: PolyType => tryMkMono(instantiate(pt), sc)
    case ft: PolyFunType =>
      mono(ft).getOrElse:
        error(msg"Expected a monomorphic type or an instantiable type here, but ${ty.show} found" -> sc.toLoc :: Nil)
    case ty: Type => ty

  private def typeAndSubstType(ty: Term, pol: Bool)
      (using map: Map[LocalSymbol, TypeArg], ctx: InfCtx, cctx: CCtx)
    : InfType =
    def mono(ty: Term, pol: Bool): Type = monoOrErr(typeAndSubstType(ty, pol), ty)
    trace[InfType](s"${ctx.lvl}. Typing type ${ty.showDbg}", r => s"~> ${r.showDbg}"):
      ty match
        case Ref(sym: LocalSymbol) =>
          log(s"Type lookup: ${sym.nme} ${sym.uid} ${map.keySet}")
          map.get(sym) match
            case S(Wildcard(in, out)) => if pol then out else in
            case S(ty: Type) => ty
            case N => ctx.get(sym) match
              case S(ty) => ty
              case _ => error(msg"Variable not found: ${sym.nme}" -> ty.toLoc :: Nil)
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
                      in.fold(Bot)(t => mono(t, !pol)),
                      out.fold(Top)(t => mono(t, pol))
                    )
                  case _ =>
                    val ta = mono(t, pol)
                    tp.vce match
                      case S(false) => Wildcard.in(ta)
                      case S(true) => Wildcard.out(ta)
                      case N => ta
                val fs = ts.map(_ => false) // TODO
                ClassLikeType(tpeSym, ts, Nil, fs, fs)
            case N => error(msg"Not a valid class: ${cls.describe}" -> cls.toLoc :: Nil)
        case FunTy(Term.Tup(params), ret, eff) =>
          val p = params.map {
            case Fld(_, p, _) => typeAndSubstType(p, !pol)
            case spd: Spd => lastWords(s"unexpected spread in function type parameters: $spd")
          }
          val e = eff.fold(Bot): e =>
            typeAndSubstType(e, pol) match
              case t: Type => t
              case _ => error(msg"Effect cannot be polymorphic." -> ty.toLoc :: Nil)
          PolyFunType(p, typeAndSubstType(ret, pol), e)
        case f @ Forall(tvs, outer, body) =>
          val outsym = outer.getOrElse(TempSymbol(S(f), erasedType = N, "outer"))
          val outVar = freshOuter(outsym)(using ctx)
          val nestCtx = ctx.nestWithOuter(outVar)
          outer.foreach(sym => nestCtx += sym -> outVar)
          given InfCtx = nestCtx
          genPolyType(tvs, outVar, typeAndSubstType(body, pol))
        case Neg(t) => ~mono(t, !pol)
        case CompType(lhs, rhs, pol) =>
          if pol then mono(lhs, pol) | mono(rhs, pol) else mono(lhs, pol) & mono(rhs, pol)
        case UnitVal() => InfCtx.objTy
        case _ => ty.symbol.flatMap(_.asTpe) match
          case S(cls: (ClassSymbol | TypeAliasSymbol)) => typeAndSubstType(Term.TyApp(ty, Nil)(N), pol)
          case _ => error(msg"Invalid type" -> ty.toLoc :: Nil, S(ty)) // TODO

  private def genPolyType(tvs: Ls[QuantVar], outer: InfVar, body: => InfType)
      (using ctx: InfCtx, cctx: CCtx) =
    val bds = tvs.map:
      case qv @ QuantVar(sym, ub, lb) =>
        val tv = freshVar(sym)
        ctx += sym -> tv // TODO: a type var symbol may be better...
        tv -> qv
    bds.foreach:
      case (tv, QuantVar(_, ub, lb)) =>
        ub.foreach(ub => ctx.addub(tv,typeMonoType(ub)))
        lb.foreach(lb => ctx.addlb(typeMonoType(lb), tv))
        val lbty = ctx.lbs(tv.sym).foldLeft[Type](Bot)(_ | _)
        val ubty = ctx.ubs(tv.sym).foldLeft[Type](Top)(_ & _)
        constrain(lbty, ubty)
    PolyType(bds.map(_._1), S(outer), body)

  private def typeType(ty: Term)(using ctx: InfCtx, cctx: CCtx): InfType =
    typeAndSubstType(ty, true)(using Map.empty)
  private def typeMonoType(ty: Term)(using InfCtx, CCtx) = monoOrErr(typeType(ty), ty)

  def typePurely(t: Term)(using InfCtx, Scope) =
    val (ty, eff) = typeCheck(t)
    given CCtx = CCtx.init(t, N)
    constrain(eff, Bot)
    ty

  private def constrain(x: Type, y: Type)(using ctx: InfCtx, cctx: CCtx): Unit =
    ctx.constrain(solver, ctx.sub(x,y))

  private def fundef(sym: Symbol, lam: Term, sig: Opt[Term])
      (using ctx: InfCtx, cctx: CCtx, scope: Scope) = lam match
    case Term.Lam(params, body) => sig match
      case S(sig) =>
        val sigTy = typeType(sig)
        ctx += sym -> sigTy
        ascribe(lam, sigTy)
        ()
      case N =>
        val outer = freshOuter(new TempSymbol(S(lam), erasedType = N, "outer"))(using ctx)
        given InfCtx = ctx.nestWithOuter(outer)
        val funTyV = freshVar(sym)
        ctx += sym -> funTyV // for recursive functions
        val (res, _) = typeCheck(lam)
        val funTy = tryMkMono(res, lam)
        given CCtx = CCtx.init(lam, N)
        constrain(funTy, funTyV)
        ctx += sym -> generalize(funTy, S(outer), ctx.lvl + 1)
    case _ =>
      error(msg"Function definition shape not yet supported for ${sym.nme}" -> lam.toLoc :: Nil)

  def instantiate(x: InfType): Type = ???
  def generalize(ty: InfType, outer: Opt[InfVar], lvl: Int): PolyType = ???

  private def app(lhs: InfType, lhsEff: Type, rhs: Ls[Elem], t: Term)
      (using ctx: InfCtx, cctx: CCtx, scope: Scope)
    : (InfType, Type) = lhs match
    case PolyFunType(params, ret, eff) =>
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
    case ClassLikeType(s, (params: ClassLikeType) :: ret :: eff :: Nil, _,_,_)
        if s === ctx.prim.fnSym && params.sym === ctx.prim.objSym =>
      app(PolyFunType(params.refinement.values.toList, ret.posPart, eff.posPart), lhsEff, rhs, t)
    case ty: PolyType => app(instantiate(ty), lhsEff, rhs, t)
    case funTy =>
      val (argTy, argEff) = rhs.flatMap:
          case f: Fld =>
            val (ty, eff) = typeCheck(f.term)
            Left(ty) :: Right(eff) :: Nil
          case spd: Spd => TODO(s"spread arguments: $spd")
        .partitionMap(x => x)
      val effVar = freshVar(TempSymbol(S(t), erasedType = N, "eff"))
      val retVar = freshVar(TempSymbol(S(t), erasedType = N, "app"))
      constrain(tryMkMono(funTy, t), InfCtx.funTy(argTy.map(tryMkMono(_, t)), retVar, effVar))
      (retVar, argEff.foldLeft[Type](effVar | lhsEff)((res, e) => res | e))


  private def selproj(t: Term, cls: Term, field: Tree.Ident)(using InfCtx, CCtx, Scope)
    : (InfType, Type) =
    val (ty, eff) = typeCheck(t)
    cls.symbol.flatMap(_.asCls.flatMap(sym => sym.defn.map(sym -> _))) match
      case S(clsSym -> clsDfn) =>
        val map = HashMap[LocalSymbol, TypeArg]()
        val targs = clsDfn.tparams.map {
          case TyParam(_, _, targ) =>
            val ty = freshWildcard(targ)
            map += targ -> ty
            ty
        }
        val fs = targs.map(_ => false) // TODO
        constrain(tryMkMono(ty, t), ClassLikeType(clsSym, targs, Nil, fs, fs))
        require(clsDfn.paramsOpt.forall(_.restParam.isEmpty))
        (clsDfn.paramsOpt.fold(Nil)(_.params).map {
          case Param(_, sym, sign, _) =>
            if sym.nme === field.name then sign else N
        }.filter(_.isDefined)) match
          case S(res) :: Nil => (typeAndSubstType(res, pol = true)(using map.toMap), eff)
          case _ => (error(msg"${field.name} is not a valid member in class ${clsSym.nme}" -> t.toLoc :: Nil), Bot)
      case N => 
        (error(msg"Not a valid class: ${cls.describe}" -> cls.toLoc :: Nil), Bot)

  private def newobj(cls: Term, args: Ls[Term])(using InfCtx, CCtx, Scope) =
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
        (error(msg"The number of parameters is incorrect" -> cls.toLoc :: Nil), Bot)
      else
        val map = HashMap[LocalSymbol, TypeArg]()
        val targs = clsDfn.tparams.map {
          case TyParam(_, S(_), targ) =>
            val ty = freshVar(targ)
            map += targ -> ty
            ty
          case TyParam(_, N, targ) =>
            // val ty = freshWildcard // FIXME probably not correct
            val ty = freshVar(targ)
            map += targ -> ty
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
        val fs = targs.map(_ => false) // TOOD
        (ClassLikeType(clsDfn.sym, targs, Nil, fs, fs), effBuff.foldLeft[Type](Bot)((res, e) => res | e))
    case S(clsDfn: ClassDef.Plain) => ??? // TODO
    case N => 
      (error(msg"Not a valid class: ${cls.describe}" -> cls.toLoc :: Nil), Bot)

  def ascribe(lhs: Term, rhs: InfType)(using ctx: InfCtx, scope: Scope): (InfType, Type) = // TODO
  trace[(InfType, Type)](s"${ctx.lvl}. Ascribing ${lhs.showDbg} : ${rhs.showDbg}", res => s"! ${res._2.showDbg}"):
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
        given InfCtx = nestCtx
        val (_, effTy) = ascribe(body, ret)
        constrain(effTy, eff)
        (ft, Bot)
    case (Term.Lam(params, body), ft @ ClassLikeType(fn, (args: ClassLikeType)::ret::eff::Nil, _,_,_))
        if fn === ctx.prim.fnSym =>
      ascribe(lhs, PolyFunType(args.refinement.values.toList, ret.posPart, eff.posPart))
    case (term, pt @ PolyType(_, outer, _)) => // * generalize
      val nextCtx = outer match
        case S(outer) => ctx.nestWithOuter(outer)
        case N => ctx.nextLevel
      // given InfCtx = nextCtx
      // constrain(ascribe(term, skolemize(pt))._2, Bot) // * never generalize terms with effects
      // (pt, Bot)
      ???
    // case (Term.IfLike(_, IfLikeForm.ReturningIf, split), ty) => // * propagate
    //   typeAllSplits(split.getExpandedSplit, S(ty))
    case (Term.Asc(term, ty), rhs) =>
      ascribe(term, typeType(ty))
      ascribe(term, rhs)
    case _ =>
      val (lhsTy, eff) = typeCheck(lhs)
      rhs match
        case pf: PolyFunType if mono(pf).isEmpty =>
          (error(msg"Cannot type non-function term ${lhs.toString} as ${rhs.show}" -> lhs.toLoc :: Nil), Bot)
        case _ =>
          constrain(tryMkMono(lhsTy, lhs), monoOrErr(rhs, lhs))
          (rhs, eff)

  def typeCheck(t: Term)(using ctx: InfCtx, scope: Scope): (InfType, Type) =
  trace[(InfType, Type)](s"${ctx.lvl}. Typing ${t.showDbg}", r => s": (${r._1.showDbg}, ${r._2.showDbg})"):
    given CCtx = CCtx.init(t, N)
    t match
      case Term.Error() => (Bot, Bot) // TODO: error type?
      case UnitVal() => (InfCtx.objTy, Bot)
      case Lit(lit) => (InfCtx.litTy(lit), Bot)
      case Ref(sym) =>
        ctx.get(sym) match
          case Some(ty) => (ty, Bot)
          case _ => (error(msg"Variable not found: ${sym.nme}" -> t.toLoc :: Nil), Bot)
      case t @ Term.App(lhs, Term.Tup(rhs)) =>
        val (funTy, lhsEff) = typeCheck(lhs)
        app(funTy, lhsEff, rhs, t)
      case trm @ Term.Sel(t, l) =>
        val (ty, eff) = typeCheck(t)
        val r = freshVar(trm, "")
        constrain(tryMkMono(ty, t) , InfCtx.refinedObj(Ls(l -> r)))
        (r, eff)
      case sel @ Term.SynthSel(Ref(_: TopLevelSymbol), nme) if sel.symbol.isDefined =>
        typeCheck(Ref(sel.symbol.get)(sel.nme, N))
      case Term.SelProj(term, cls, field) => selproj(term, cls, field)
      case Term.Tup(fields) => // TODO tup type
        var eff: Type = Bot
        val fs = fields.zipWithIndex.map:
          case (f: Fld, i) =>
            val (ty, ef) = typeCheck(f.term)
            eff |= ef
            (Tree.Ident(i.toString): Tree.Ident, tryMkMono(ty, f))
          case (spd: Spd, _) => TODO(s"spread arguments: $spd")
        (InfCtx.refinedObj(fs), eff)
      // case Term.IfLike(_, IfLikeForm.ReturningIf, split) => typeAllSplits(split.getExpandedSplit, N)
      case Lam(PlainParamList(params), body) =>
        val nestCtx = ctx.nest
        given InfCtx = nestCtx
        val tvs = params.map:
          case Param(_, sym, sign, _) =>
            val ty = sign.map(s => typeType(s)(using nestCtx)).getOrElse(freshVar(sym))
            nestCtx += sym -> ty
            ty
        val (bodyTy, eff) = typeCheck(body)
        (PolyFunType(tvs, bodyTy, eff), Bot)     
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
            fundef(td.sym, Term.Lam(ps, body), sig)
            goStats(stats)
          case (td @ TermDefinition(k = Fun, params = Nil, sign = sig, body = S(body))) :: stats =>
            fundef(td.sym, body, sig)  // * may be a case expressions
            goStats(stats)
          case (td1 @ TermDefinition(k = Fun, sign = S(sig), body = None)) :: (td2 @ TermDefinition(k = Fun, body = S(body))) :: stats
           if td1.sym === td2.sym => goStats(td2 :: stats) // * avoid type check signatures twice
          case (td @ TermDefinition(k = Fun, sign = S(sig), body = None)) :: stats =>
            ctx += td.sym -> typeType(sig)
            goStats(stats)
          case (clsDef: ClassDef) :: stats =>
            typeNames.add(clsDef.sym.nme)
            // clsDef.ext match
            //   case S(Term.New(ty, _, N)) => createADTCtor(clsDef, ty)
            //   case _ => ()
            goStats(stats)
          case (modDef: ModuleOrObjectDef) :: stats =>
            typeNames.add(modDef.sym.nme)
            goStats(stats)
          case Import(sym, str, pth) :: stats =>
            goStats(stats) // TODO:
          case stat :: _ =>
            // TODO(stat) // TODO
        goStats(stats)
        val (ty, eff) = typeCheck(res)
        (ty, effBuff.foldLeft(eff)((res, e) => res | e))
      case Term.New(cls, args, N) => newobj(cls, args)
      case Term.Asc(term, ty) =>
        val res = typeType(ty)(using ctx)
        ascribe(term, res)
      case Term.Annotated(Annot.Untyped, _) => (Bot, Bot)
      case _ =>
        (error(msg"Term shape not yet supported by InvalML: ${t.toString}" -> t.toLoc :: Nil), Bot)
