package hkmc2
package bbml

import scala.collection.mutable.{LinkedHashSet, HashMap, ListBuffer}
import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import semantics.*, semantics.Term.*
import syntax.*
import Tree.*

object InfVarUid extends Uid.Handler[InfVar]

final case class Ctx(
  parent: Option[Ctx],
  lvl: Int,
  clsDefs: HashMap[Str, ClassDef],
  env: HashMap[Uid[Symbol], GeneralType],
  quoteSkolemEnv: HashMap[Uid[Symbol], InfVar], // * SkolemTag for variables in quasiquotes
):
  def +=(p: Symbol -> GeneralType): Unit = env += p._1.uid -> p._2
  def get(sym: Symbol): Option[GeneralType] = env.get(sym.uid) orElse parent.dlof(_.get(sym))(None)
  def *=(cls: ClassDef): Unit = clsDefs += cls.sym.id.name -> cls
  def getDef(name: Str): Option[ClassDef] = clsDefs.get(name) orElse parent.dlof(_.getDef(name))(None)
  def &=(p: (Symbol, Type, InfVar)): Unit =
    env += p._1.uid -> Ctx.varTy(p._2, p._3)(using this)
    quoteSkolemEnv += p._1.uid -> p._3
  def getSk(sym: Symbol): Option[Type] = quoteSkolemEnv.get(sym.uid) orElse parent.dlof(_.getSk(sym))(None)
  def nest: Ctx = Ctx(Some(this), lvl, HashMap.empty, HashMap.empty, quoteSkolemEnv)
  def nextLevel: Ctx = Ctx(Some(this), lvl + 1, HashMap.empty, HashMap.empty, quoteSkolemEnv)

object Ctx:
  def intTy(using ctx: Ctx): Type = ClassType(ctx.getDef("Int").get.sym, Nil)
  def numTy(using ctx: Ctx): Type = ClassType(ctx.getDef("Num").get.sym, Nil)
  def strTy(using ctx: Ctx): Type = ClassType(ctx.getDef("Str").get.sym, Nil)
  def boolTy(using ctx: Ctx): Type = ClassType(ctx.getDef("Bool").get.sym, Nil)
  private def codeBaseTy(ct: TypeArg, cr: TypeArg, isVar: TypeArg)(using ctx: Ctx): Type = ClassType(ctx.getDef("CodeBase").get.sym, ct :: cr :: isVar :: Nil)
  def codeTy(ct: Type, cr: Type)(using ctx: Ctx): Type = codeBaseTy(Wildcard.out(ct), Wildcard.out(cr), Wildcard.out(Top))
  def varTy(ct: Type, cr: Type)(using ctx: Ctx): Type = codeBaseTy(ct, Wildcard(cr, cr), Wildcard.out(Bot))
  def regionTy(sk: Type)(using ctx: Ctx): Type = ClassType(ctx.getDef("Region").get.sym, Wildcard(sk, sk) :: Nil)
  def refTy(ct: Type, sk: Type)(using ctx: Ctx): Type = ClassType(ctx.getDef("Ref").get.sym, Wildcard(ct, ct) :: Wildcard.out(sk) :: Nil)
  private val builtinClasses = Ls(
    "Any", "Int", "Num", "Str", "Bool", "Nothing", "CodeBase", "Region", "Ref"
  )
  private val infVarState = new InfVarUid.State()
  private val int2IntBinTy =
    (ctx: Ctx) => FunType(intTy(using ctx) :: intTy(using ctx) :: Nil, intTy(using ctx), Bot)
  private val int2BoolBinTy =
    (ctx: Ctx) => FunType(intTy(using ctx) :: intTy(using ctx) :: Nil, boolTy(using ctx), Bot)
  private val int2NumBinTy =
    (ctx: Ctx) => FunType(intTy(using ctx) :: intTy(using ctx) :: Nil, numTy(using ctx), Bot)
  private val num2NumBinTy =
    (ctx: Ctx) => FunType(numTy(using ctx) :: numTy(using ctx) :: Nil, numTy(using ctx), Bot)
  private val builtinOps = Map(
    "+" -> int2IntBinTy,
    "-" -> int2IntBinTy,
    "*" -> int2IntBinTy,
    "/" -> int2NumBinTy,
    "<" -> int2BoolBinTy,
    ">" -> int2BoolBinTy,
    "+." -> num2NumBinTy,
    "-." -> num2NumBinTy,
    "*." -> num2NumBinTy,
    "/." -> num2NumBinTy,
    "==" -> ((ctx: Ctx) => {
      val tv: InfVar = InfVar(1, infVarState.nextUid, new VarState(), false)
      PolyType(tv :: Nil, FunType(tv :: tv :: Nil, boolTy(using ctx), Bot))
    })
  )
  private val builtinVals = Map(
    "run" -> ((ctx: Ctx) => {
      val tv: InfVar = InfVar(1, infVarState.nextUid, new VarState(), false)
      PolyType(tv :: Nil, FunType(codeTy(tv, Bot)(using ctx) :: Nil, tv, Bot))
    }),
    "error" -> ((ctx: Ctx) => Bot),
    "log" -> ((ctx: Ctx) => FunType(strTy(using ctx) :: Nil, Top, Bot)),
  )
  def isOp(name: Str): Bool = builtinOps.contains(name)
  def init(predefs: Map[Str, Symbol]): Ctx =
    val ctx = new Ctx(None, 1, HashMap.empty, HashMap.empty, HashMap.empty)
    builtinClasses.foreach(
      cls =>
        predefs.get(cls) match
          case Some(cls: ClassSymbol) => ctx *= ClassDef.Plain(cls, Nil, ObjBody(Term.Blk(Nil, Term.Lit(Tree.UnitLit(true)))), None)
          case _ => ???
    )
    (builtinOps ++ builtinVals).foreach(
      p =>
        predefs.get(p._1) match
          case Some(v: Symbol) => ctx += v -> p._2(ctx)
          case _ => ???
    )
    ctx

class BBTyper(raise: Raise, val initCtx: Ctx, tl: TraceLogger):
  import tl.{trace, log}
  
  private val infVarState = new InfVarUid.State()
  private val solver = new ConstraintSolver(raise, infVarState, tl)

  private def freshSkolem(using ctx: Ctx): InfVar = InfVar(ctx.lvl, infVarState.nextUid, new VarState(), true)
  private def freshVar(using ctx: Ctx): InfVar = InfVar(ctx.lvl, infVarState.nextUid, new VarState(), false)
  private def freshWildcard(using ctx: Ctx) = Wildcard(freshVar, freshVar)

  private val allocSkolem: InfVar = InfVar(0, infVarState.nextUid, new VarState(), true)

  private def error(msg: Ls[Message -> Opt[Loc]]) =
    raise(ErrorReport(msg))
    Bot // TODO: error type?

  private def getClassType(cls: ClassSymbol, t: Term)(using ctx: Ctx) =
    ctx.getDef(cls.nme) match
      case S(_) =>
        if cls.nme == "Any" then
          Top
        else if cls.nme == "Nothing" then
          Bot
        else
          ClassType(cls, Nil)
      case N => 
        error(msg"Definition not found: ${cls.nme}" -> t.toLoc :: Nil)

  private def extract(asc: Term)(using map: Map[Uid[Symbol], Wildcard], pol: Bool)(using ctx: Ctx): GeneralType = asc match
    case Ref(cls: ClassSymbol) => getClassType(cls, asc)
    case Ref(sym: VarSymbol) =>
      map.get(sym.uid) match
        case Some(Wildcard(in, out)) => if pol then out else in
        case _ => ctx.get(sym).getOrElse(error(msg"Type variable not found: ${sym.name}" -> asc.toLoc :: Nil))
    case FunTy(Term.Tup(params), ret, eff) =>
      PolyFunType(params.map {
        case Fld(_, p, _) => extract(p)(using map, !pol)
      }, extract(ret), eff.map(e => extract(e) match {
        case t: Type => t
        case _ => error(msg"Effect cannot be polymorphic." -> asc.toLoc :: Nil)
      }).getOrElse(Bot))
    case Term.Forall(tvs, body) =>
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      genPolyType(tvs, extract(body))
    case _ => error(msg"${asc.toString} is not a valid class member type" -> asc.toLoc :: Nil) // TODO

  private def genPolyType(tvs: Ls[VarSymbol], body: => GeneralType)(using ctx: Ctx) =
    val bd = tvs.map:
      case sym: VarSymbol =>
        val tv = freshVar
        ctx += sym -> tv // TODO: a type var symbol may be better...
        tv
    PolyType(bd, body)

  private def typeMonoType(ty: Term)(using ctx: Ctx): Type = monoOrErr(typeType(ty), ty)

  private def typeType(ty: Term)(using ctx: Ctx): GeneralType = ty match
    case Ref(sym: VarSymbol) =>
      ctx.get(sym) match
        case Some(ty) => ty
        case _ =>
          if sym.nme == "Alloc" then
            allocSkolem
          else
            error(msg"Variable not found: ${sym.name}" -> ty.toLoc :: Nil)
    case Ref(cls: ClassSymbol) => getClassType(cls, ty)
    case FunTy(Term.Tup(params), ret, eff) =>
      PolyFunType(params.map {
        case Fld(_, p, _) => typeType(p)
      }, typeType(ret), eff.map(typeType).getOrElse(Bot) match {
        case t: Type => t
        case _ => error(msg"Effect cannot be polymorphic." -> ty.toLoc :: Nil)
      })
    case Term.Forall(tvs, body) =>
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      genPolyType(tvs, typeType(body))
    case Term.TyApp(lhs, targs) => typeType(lhs) match
      case ClassType(cls, _) => ClassType(cls, targs.map {
        case Term.WildcardTy(in, out) =>
          Wildcard(
            in.map(t => typeMonoType(t)(using ctx)).getOrElse(Bot), out.map(t => typeMonoType(t)(using ctx)).getOrElse(Top)
          )
        case t => typeMonoType(t)(using ctx)
      })
      case _ => error(msg"${lhs.toString} is not a class" -> ty.toLoc :: Nil)
    case CompType(lhs, rhs, pol) =>
      Type.mkComposedType(typeMonoType(lhs), typeMonoType(rhs), pol)
    case _ => error(msg"${ty.toString} is not a valid type annotation" -> ty.toLoc :: Nil)

  private def instantiate(ty: PolyType)(using ctx: Ctx): GeneralType =
    ty.body.subst(using (ty.tvs.map {
      case InfVar(_, uid, _, _) =>
        val nv = freshVar
        uid -> nv
    }).toMap)
  
  // * Check if two poly types are equivalent
  private def checkPoly(lhs: GeneralType, rhs: GeneralType)(using ctx: Ctx): Bool = (lhs, rhs) match
    case (ClassType(name1, targs1), ClassType(name2, targs2)) if name1.uid == name2.uid && targs1.length == targs2.length =>
      targs1.zip(targs2).foldLeft(true)((res, p) => p match {
        case (Wildcard(in1, out1), Wildcard(in2, out2)) =>
          res && checkPoly(in1, in2) && checkPoly(out1, out2)
        case (ty: Type, Wildcard(in2, out2)) =>
          res && checkPoly(ty, in2) && checkPoly(ty, out2)
        case (Wildcard(in1, out1), ty: Type) =>
          res && checkPoly(in1, ty) && checkPoly(out1, ty)
        case (ty1: Type, ty2: Type) => res && checkPoly(ty1, ty2)
      })
    case (InfVar(_, uid1, _, _), InfVar(_, uid2, _, _)) => uid1 == uid2
    case (PolyFunType(args1, ret1, eff1), PolyFunType(args2, ret2, eff2)) if args1.length == args2.length =>
      args1.zip(args2).foldLeft(checkPoly(ret1, ret2) && checkPoly(eff1, eff2))((res, p) => res && checkPoly(p._1, p._2))
    case (FunType(args1, ret1, eff1), FunType(args2, ret2, eff2)) if args1.length == args2.length =>
      args1.zip(args2).foldLeft(checkPoly(ret1, ret2) && checkPoly(eff1, eff2))((res, p) => res && checkPoly(p._1, p._2))
    case (ComposedType(lhs1, rhs1, pol1), ComposedType(lhs2, rhs2, pol2)) if pol1 == pol2 =>
      checkPoly(lhs1, lhs2) && checkPoly(rhs1, rhs2)
    case (NegType(ty1), NegType(ty2)) => checkPoly(ty1, ty2)
    case (PolyType(tv1, body1), PolyType(tv2, body2)) if tv1.length == tv2.length =>
      val maps = (tv1.zip(tv2).flatMap{
        case (InfVar(_, uid1, _, _), InfVar(_, uid2, _, _)) =>
          val nv = freshVar
          (uid1 -> nv) :: (uid2 -> nv) :: Nil
      }).toMap
      checkPoly(body1.subst(using maps), body2.subst(using maps))
    case (Top, Top) => true
    case (Bot, Bot) => true
    case _ => false

  private def extrude(ty: GeneralType)(using ctx: Ctx, pol: Bool): GeneralType = ty match
    case ty: Type => solver.extrude(ty)(using ctx.lvl, pol)
    case PolyType(tvs, body) => PolyType(tvs, extrude(body))
    case PolyFunType(args, ret, eff) =>
      PolyFunType(args.map(extrude(_)(using ctx, !pol)), extrude(ret), solver.extrude(eff)(using ctx.lvl, pol))

  private def constrain(lhs: Type, rhs: Type)(using ctx: Ctx): Unit =
    solver.constrain(lhs, rhs)

  // TODO: content type
  private def typeCode(code: Term)(using ctx: Ctx): (Type, Type, Type) = code match
    case Lit(lit) => ((lit match
      case _: IntLit => Ctx.intTy
      case _: DecLit => Ctx.numTy
      case _: StrLit => Ctx.strTy
      case _: UnitLit => Top
      case _: BoolLit => Ctx.boolTy), Bot, Bot)
    case Ref(sym: Symbol) if sym.nme == "error" => (Bot, Bot, Bot)
    case Lam(params, body) =>
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
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
    case Term.App(Ref(sym: TermSymbol), Term.Tup(lhs :: rhs :: Nil)) if Ctx.isOp(sym.nme) =>
      val op = ctx.get(sym) match
        case Some(ty) => ty
        case _ => error(msg"Operator not found: ${sym.nme}" -> code.toLoc :: Nil)
      val (lhsTy, lhsCtx, lhsEff) = typeCode(lhs.value)
      val (rhsTy, rhsCtx, rhsEff) = typeCode(rhs.value)
      val resTy = freshVar
      constrain(monoOrErr(op match {
        case ty: PolyType => instantiate(ty)
        case _ => op
      }, code), FunType(lhsTy :: rhsTy :: Nil, resTy, Bot))
      (resTy, lhsCtx | rhsCtx, lhsEff | rhsEff)
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
      constrain(monoOrErr(ty, body), Ctx.codeTy(tv, cr))
      (tv, cr, eff)
    case Term.Blk(LetBinding(pat, rhs) :: Nil, body) => // TODO: more than one?
      val (rhsTy, rhsCtx, rhsEff) = typeCode(rhs)(using ctx)
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      val bd = pat match
        case Pattern.Var(sym) =>
          val sk = freshSkolem
          nestCtx &= (sym, rhsTy, sk)
          sk
        case _ => ???
      val (bodyTy, bodyCtx, bodyEff) = typeCode(body)
      val res = freshVar(using ctx)
      constrain(bodyCtx, bd | res)
      (bodyTy, rhsCtx | res, rhsEff | bodyEff)
    case Term.If(Split.Cons(TermBranch.Boolean(cond, Split.Else(cons)), Split.Else(alts))) =>
      val (condTy, condCtx, condEff) = typeCode(cond)
      val (consTy, consCtx, consEff) = typeCode(cons)
      val (altsTy, altsCtx, altsEff) = typeCode(alts)
      constrain(condTy, Ctx.boolTy)
      (consTy | altsTy, condCtx | consCtx | altsCtx, condEff | consEff | altsEff)
    case _ =>
      (error(msg"Cannot quote ${code.toString}" -> code.toLoc :: Nil), Bot, Bot)

  private def typeFunDef(sym: Symbol, lam: Term, sig: Opt[Term], pctx: Ctx)(using ctx: Ctx) = lam match
    case Term.Lam(params, body) => sig match
      case S(sig) =>
        val sigTy = typeType(sig)(using ctx)
        pctx += sym -> sigTy
        ascribe(lam, sigTy)
        ()
      case N =>
        val funTy = freshVar
        pctx += sym -> funTy // for recursive types
        val (res, _) = typeCheck(lam)
        constrain(monoOrErr(res, lam), funTy)(using ctx)
    case _ => error(msg"Can not define function ${sym.nme}" -> lam.toLoc :: Nil)

  private def typeSplit(split: TermSplit, sign: Opt[GeneralType])(using ctx: Ctx): (GeneralType, Type) = split match
    case Split.Cons(TermBranch.Boolean(cond, Split.Else(cons)), alts) => // * boolean condition
      val (condTy, condEff) = typeCheck(cond)
      val (consTy, consEff) = sign match
        case S(sign) => ascribe(cons, sign)
        case _=> typeCheck(cons)
      val (altsTy, altsEff) = typeSplit(alts, sign)
      val allEff = condEff | (consEff | altsEff)
      constrain(monoOrErr(condTy, cond), Ctx.boolTy)
      (sign.getOrElse(monoOrErr(consTy, cons) | monoOrErr(altsTy, alts)), allEff)
    case Split.Cons(TermBranch.Match(scrutinee, Split.Cons(PatternBranch(Pattern.Class(sym, _, _), cons), Split.NoSplit)), alts) =>
      // * Pattern matching
      val (clsTy, tv, emptyTy) = ctx.getDef(sym.nme) match
        case S(ClassDef.Parameterized(_, tparams, _, _, _)) =>
          (ClassType(sym, tparams.map(_ => freshWildcard)), freshVar, ClassType(sym, tparams.map(_ => Wildcard.empty)))
        case S(ClassDef.Plain(_, tparams, _, _)) =>
          (ClassType(sym, tparams.map(_ => freshWildcard)), freshVar, ClassType(sym, tparams.map(_ => Wildcard.empty)))
        case _ =>
          error(msg"Cannot match ${scrutinee.toString} as ${sym.toString}" -> split.toLoc :: Nil)
          (Bot, Bot, Bot)
      val (scrutineeTy, scrutineeEff) = typeCheck(scrutinee)
      constrain(monoOrErr(scrutineeTy, scrutinee), clsTy | (tv & Type.mkNegType(emptyTy)))
      val nestCtx1 = ctx.nest
      val nestCtx2 = ctx.nest
      scrutinee match // * refine
        case Ref(sym: VarSymbol) =>
          nestCtx1 += sym -> clsTy
          nestCtx2 += sym -> tv
        case _ => () // TODO: refine all variables holding this value?
      val (consTy, consEff) = typeSplit(cons, sign)(using nestCtx1)
      val (altsTy, altsEff) = typeSplit(alts, sign)(using nestCtx2)
      val allEff = scrutineeEff | (consEff | altsEff)
      (sign.getOrElse(monoOrErr(consTy, cons) | monoOrErr(altsTy, alts)), allEff)
    case Split.Else(alts) => sign match
      case S(sign) => ascribe(alts, sign)
      case _=> typeCheck(alts)

  private def ascribe(lhs: Term, rhs: GeneralType)(using ctx: Ctx): (GeneralType, Type) = (lhs, rhs) match
    case (Term.Lam(params, body), ft @ PolyFunType(args, ret, eff)) => // * annoted functions
      if params.length != args.length then
         (error(msg"Cannot type function ${lhs.toString} as ${rhs.toString}" -> lhs.toLoc :: Nil), Bot)
      else
        val nestCtx = ctx.nest
        val argsTy = params.zip(args).map:
          case (Param(_, sym, _), ty) =>
            nestCtx += sym -> ty
            ty
        given Ctx = nestCtx
        val (bodyTy, effTy) = typeCheck(body)
        if ret.isPoly && !checkPoly(bodyTy, ret) then
          (error(msg"Cannot type function ${lhs.toString} as ${rhs.toString}" -> lhs.toLoc :: Nil), Bot)
        else
          constrain(effTy, eff)
          if !ret.isPoly then constrain(monoOrErr(bodyTy, body), monoOrErr(ret, body))
          (ft, Bot)
    case (Term.Lam(params, body), ft @ FunType(args, ret, eff)) => ascribe(lhs, PolyFunType(args, ret, eff))
    case (term, pt @ PolyType(tvs, body)) => // * generalize
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      constrain(ascribe(term, skolemize(tvs, body))._2, Bot) // * never generalize terms with effects
      (pt, Bot)
    case (Term.Blk(LetBinding(Pattern.Var(sym), rhs) :: Nil, body), ty) => // * propagate
      val nestCtx = ctx.nest
      given Ctx = nestCtx
      val (rhsTy, eff) = typeCheck(rhs)
      nestCtx += sym -> rhsTy
      val (resTy, resEff) = ascribe(body, ty)
      (resTy, eff | resEff)
    case (Term.If(branches), ty) => // * propagate
      typeSplit(branches, S(ty))
    case _ =>
      val (lhsTy, eff) = typeCheck(lhs)
      (lhsTy, rhs) match
        case (lhsTy: PolyType, rhs) => constrain(monoOrErr(instantiate(lhsTy), lhs), monoOrErr(rhs, lhs))
        case _ => constrain(monoOrErr(lhsTy, lhs), monoOrErr(rhs, lhs))
      (rhs, eff)

  // TODO: t -> loc when toLoc is implemented
  private def app(lhs: (GeneralType, Type), rhs: Ls[Fld], t: Term)(using ctx: Ctx): (GeneralType, Type) = lhs match
    case (PolyFunType(args, ret, eff), lhsEff) => // * if the function type is known, we can directly use it
      if args.length != rhs.length then
        (error(msg"The number of parameters is incorrect" -> t.toLoc :: Nil), Bot)
      else
        val (argTy, argEff) = rhs.zip(args).flatMap{
          case (f, t) =>
            val (ty, eff) = ascribe(f.value, t)
            Left(ty) :: Right(eff) :: Nil
          }.partitionMap(x => x)
        (ret, argEff.foldLeft[Type](eff | lhsEff)((res, e) => res | e))
    case (FunType(args, ret, eff), lhsEff) => app((PolyFunType(args, ret, eff), lhsEff), rhs, t)
    case (ty: PolyType, eff) => app((instantiate(ty), eff), rhs, t)
    case (funTy, lhsEff) =>
      val (argTy, argEff) = rhs.flatMap(f =>
        val (ty, eff) = typeCheck(f.value)
        Left(ty) :: Right(eff) :: Nil
      ).partitionMap(x => x)
      val effVar = freshVar
      val retVar = freshVar
      constrain(monoOrErr(funTy, t), FunType(argTy.map {
        case pt: PolyType => monoOrErr(instantiate(pt), t)
        case ty: Type => ty
        case pf: PolyFunType => monoOrErr(pf, t)
      }, retVar, effVar))
      (retVar, argEff.foldLeft[Type](effVar | lhsEff)((res, e) => res | e))

  private def skolemize(tv: Ls[InfVar], body: GeneralType) =
    val bds = tv.map(v => (v.uid, InfVar(v.vlvl, v.uid, v.state, true))).toMap
    body.subst(using bds)

  // TODO: implement toLoc
  private def monoOrErr(ty: GeneralType, sc: Located) =
    ty.monoOr(error(msg"General type is not allowed here." -> sc.toLoc :: Nil))
  
  private def typeCheck(t: Term)(using ctx: Ctx): (GeneralType, Type) = trace[(GeneralType, Type)](s"Typing ${t.showDbg}", res => s": $res"):
    t match
      case Ref(sym: VarSymbol) =>
        ctx.get(sym) match
          case Some(ty) => (ty, Bot)
          case _ =>
            (error(msg"Variable not found: ${sym.name}" -> t.toLoc :: Nil), Bot)
      case Ref(sym: TermSymbol) =>
        ctx.get(sym) match
          case Some(ty) => (ty, Bot)
          case _ =>
            (error(msg"Definition not found: ${sym.nme}" -> t.toLoc :: Nil), Bot)
      case Blk(stats, res) =>
        val nestCtx = ctx.nest
        given Ctx = nestCtx
        val effBuff = ListBuffer.empty[Type]
        stats.foreach:
          case term: Term => effBuff += typeCheck(term)._2
          case LetBinding(Pattern.Var(sym), rhs) =>
            val (rhsTy, eff) = typeCheck(rhs)
            effBuff += eff
            nestCtx += sym -> rhsTy
          case TermDefinition(Fun, sym, params, sig, Some(body), _) =>
            typeFunDef(sym, params match {
              case S(params) => Term.Lam(params, body)
              case _ => body // * may be a case expressions
            }, sig, ctx)
          case TermDefinition(Fun, sym, _, S(sig), None, _) =>
            ctx += sym -> typeType(sig)
          case clsDef: ClassDef => ctx *= clsDef
          case _ => () // TODO
        val (ty, eff) = typeCheck(res)
        (ty, effBuff.foldLeft(eff)((res, e) => res | e))
      case Lit(lit) => ((lit match
        case _: IntLit => Ctx.intTy
        case _: DecLit => Ctx.numTy
        case _: StrLit => Ctx.strTy
        case _: UnitLit => Top
        case _: BoolLit => Ctx.boolTy), Bot)
      case Lam(params, body) =>
        val nestCtx = ctx.nest
        given Ctx = nestCtx
        val tvs = params.map:
          case Param(_, sym, sign) =>
            val ty = sign.map(s => typeType(s)(using nestCtx)).getOrElse(freshVar)
            nestCtx += sym -> ty
            ty
        val (bodyTy, eff) = typeCheck(body)
        (PolyFunType(tvs, bodyTy, eff), Bot)
      case Term.SelProj(term, Term.Ref(cls: ClassSymbol), field) =>
        val (ty, eff) = typeCheck(term)
        ctx.getDef(cls.nme) match
          case S(ClassDef.Parameterized(_, tparams, params, _, _)) =>
            val map = HashMap[Uid[Symbol], Wildcard]()
            val targs = tparams.map {
              case TyParam(_, targ) =>
                val ty = freshWildcard
                  map += targ.uid -> ty
                  ty
            }
            constrain(monoOrErr(ty, term), ClassType(cls, targs))
            (params.map {
              case Param(_, sym, sign) =>
                if sym.nme == field.name then sign else N
            }.filter(_.isDefined)) match
              case S(res) :: Nil => (extract(res)(using map.toMap, true), eff)
              case _ => (error(msg"${field.name} is not a valid member in class ${cls.nme}" -> t.toLoc :: Nil), Bot)
          case S(ClassDef.Plain(_, tparams, _, _)) => ??? // TODO
          case N => 
            (error(msg"Definition not found: ${cls.nme}" -> t.toLoc :: Nil), Bot)
      case Term.App(lhs, Term.Tup(rhs)) => typeCheck(lhs) match
        case (funTy, lhsEff) => app((funTy, lhsEff), rhs, t)
      case Term.New(cls, args) =>
        ctx.getDef(cls.nme) match
          case S(ClassDef.Parameterized(_, tparams, params, _, _)) =>
            if args.length != params.length then
              (error(msg"The number of parameters is incorrect" -> t.toLoc :: Nil), Bot)
            else
              val map = HashMap[Uid[Symbol], Wildcard]()
              val targs = tparams.map {
                case TyParam(_, targ) =>
                  val ty = freshWildcard
                  map += targ.uid -> ty
                  ty
              }
              val effBuff = ListBuffer.empty[Type]
              args.iterator.zip(params).foreach {
                case (arg, Param(_, _, S(sign))) =>
                  val (ty, eff) = ascribe(arg, extract(sign)(using map.toMap, true))
                  effBuff += eff
                case _ => ???
              }
              (ClassType(cls, targs), effBuff.foldLeft[Type](Bot)((res, e) => res | e))
          case S(ClassDef.Plain(_, tparams, _, _)) => ??? // TODO
          case N => 
            (error(msg"Definition not found: ${cls.nme}" -> t.toLoc :: Nil), Bot)
      case Term.Asc(term, ty) =>
        val res = typeType(ty)(using ctx)
        ascribe(term, res)
      case Term.If(branches) => typeSplit(branches, N)
      case Term.Region(sym, body) =>
        val nestCtx = ctx.nextLevel
        given Ctx = nestCtx
        val sk = freshSkolem
        nestCtx += sym -> Ctx.regionTy(sk)
        val (res, eff) = typeCheck(body)
        val tv = freshVar(using ctx)
        constrain(eff, tv | sk)
        (extrude(res)(using ctx, true), tv | allocSkolem)
      case Term.RegRef(reg, value) =>
        val (regTy, regEff) = typeCheck(reg)
        val (valTy, valEff) = typeCheck(value)
        val sk = freshVar
        constrain(monoOrErr(regTy, reg), Ctx.regionTy(sk))
        (Ctx.refTy(monoOrErr(valTy, value), sk), sk | (regEff | valEff))
      case Term.Set(lhs, rhs) =>
        val (lhsTy, lhsEff) = typeCheck(lhs)
        val (rhsTy, rhsEff) = typeCheck(rhs)
        val sk = freshVar
        constrain(monoOrErr(lhsTy, lhs), Ctx.refTy(monoOrErr(rhsTy, rhs), sk))
        (monoOrErr(rhsTy, rhs), sk | (lhsEff | rhsEff))
      case Term.Deref(ref) =>
        val (refTy, refEff) = typeCheck(ref)
        val sk = freshVar
        val ctnt = freshVar
        constrain(monoOrErr(refTy, ref), Ctx.refTy(ctnt, sk))
        (ctnt, sk | refEff)
      case Term.Quoted(body) =>
        val nestCtx = ctx.nextLevel
        given Ctx = nestCtx
        val (ty, ctxTy, eff) = typeCode(body)
        (Ctx.codeTy(ty, ctxTy), eff)
      case _: Term.Unquoted =>
        (error(msg"Unquote should nest in quasiquote" -> t.toLoc :: Nil), Bot)
      case Term.Error =>
        (Bot, Bot) // TODO: error type?
      case _ =>
        (error(msg"Term shape not yet supported by BbML: ${t.toString}" -> t.toLoc :: Nil), Bot)

  def typePurely(t: Term): GeneralType =
    val (ty, eff) = typeCheck(t)(using initCtx)
    constrain(eff, allocSkolem)(using initCtx)
    ty
