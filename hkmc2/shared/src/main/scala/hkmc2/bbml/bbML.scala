package hkmc2
package bbml

import scala.collection.mutable.{LinkedHashSet, HashMap, ListBuffer}
import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import semantics.*, semantics.Term.*
import syntax.*
import Tree.*

sealed abstract class TypeArg:
  lazy val lvl: Int

case class Wildcard(in: Type, out: Type) extends TypeArg {
  private def printWhenSet(t: Type, in: Bool) = t match
    case Type.Top if !in => N
    case Type.Bot if in => N
    case _ => S(if in then s"in $t" else s"out $t")

  override def toString(): String = s"in $in out $out"
    // (printWhenSet(in, true).toList ++ printWhenSet(out, false).toList).mkString(" ")
  override lazy val lvl: Int = in.lvl.max(out.lvl)
}

object Wildcard:
  def in(ty: Type): Wildcard = Wildcard(ty, Type.Top)
  def out(ty: Type): Wildcard = Wildcard(Type.Bot, ty)
  def empty: Wildcard = Wildcard(Type.Bot, Type.Top)

enum Type extends TypeArg:
  case ClassType(name: ClassSymbol, targs: Ls[TypeArg])
  case InfVar(vlvl: Int, uid: Uid[InfVar], state: VarState)
  case FunType(args: Ls[Type], ret: Type, eff: Type)
  case ComposedType(lhs: Type, rhs: Type, pol: Bool) // * positive -> union
  case NegType(ty: Type)
  case PolymorphicType(tv: Ls[InfVar], body: Type)
  case Top // TODO: level?
  case Bot
  override def toString(): String = this match
    case ClassType(name, targs) =>
      if targs.isEmpty then s"${name.nme}" else s"${name.nme}[${targs.mkString(", ")}]"
    case InfVar(lvl, uid, _) => s"α${uid}_$lvl"
    case FunType(args, ret, eff) => s"(${args.mkString(", ")}) ->{${eff}} ${ret}"
    case ComposedType(lhs, rhs, pol) => s"${lhs} ${if pol then "∨" else "∧"} ${rhs}"
    case NegType(ty) => s"¬${ty}"
    case PolymorphicType(tv, body) => s"forall ${tv.mkString(", ")}: $body"
    case Top => "⊤"
    case Bot => "⊥"
  override lazy val lvl: Int = this match
    case ClassType(name, targs) =>
      targs.map(_.lvl).maxOption.getOrElse(0)
    case InfVar(lvl, _, _) => lvl
    case FunType(args, ret, eff) =>
      (ret :: eff :: args).map(_.lvl).max
    case ComposedType(lhs, rhs, _) =>
      lhs.lvl.max(rhs.lvl)
    case NegType(ty) => ty.lvl
    case PolymorphicType(tv, body) =>
      (body :: tv).map(_.lvl).max
    case Top | Bot => 0

class VarState:
  var lowerBounds: Ls[Type] = Nil
  var upperBounds: Ls[Type] = Nil

object InfVarUid extends Uid.Handler[Type.InfVar]

type EnvType = HashMap[Uid[Symbol], Type]
type clsDefType = HashMap[Str, ClassDef]
type MutSkolemSet = LinkedHashSet[Uid[Type.InfVar]]
final case class Ctx(
  parent: Option[Ctx],
  lvl: Int,
  clsDefs: clsDefType,
  env: EnvType,
  quoteSkolemEnv: HashMap[Uid[Symbol], Type.InfVar], // * SkolemTag for variables in quasiquotes
):
  def +=(p: Symbol -> Type): Unit = env += p._1.uid -> p._2
  def get(sym: Symbol): Option[Type] = env.get(sym.uid) orElse parent.dlof(_.get(sym))(None)
  def *=(cls: ClassDef): Unit = clsDefs += cls.sym.id.name -> cls
  def getDef(name: Str): Option[ClassDef] = clsDefs.get(name) orElse parent.dlof(_.getDef(name))(None)
  def &=(p: Symbol -> Type.InfVar)(using skolems: MutSkolemSet): Unit =
    env += p._1.uid -> Ctx.varTy(p._2)(using this)
    skolems += p._2.uid
    quoteSkolemEnv += p._1.uid -> p._2
  def getSk(sym: Symbol): Option[Type] = quoteSkolemEnv.get(sym.uid) orElse parent.dlof(_.getSk(sym))(None)
  def nest: Ctx = Ctx(Some(this), lvl, HashMap.empty, HashMap.empty, quoteSkolemEnv)
  def nextLevel: Ctx = Ctx(Some(this), lvl + 1, HashMap.empty, HashMap.empty, quoteSkolemEnv)

object Ctx:
  def intTy(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("Int").get.sym, Nil)
  def numTy(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("Num").get.sym, Nil)
  def strTy(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("Str").get.sym, Nil)
  def boolTy(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("Bool").get.sym, Nil)
  private def codeBaseTy(cr: TypeArg, isVar: TypeArg)(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("CodeBase").get.sym, cr :: isVar :: Nil)
  def codeTy(cr: Type)(using ctx: Ctx): Type = codeBaseTy(Wildcard.out(cr), Wildcard.out(Type.Top))
  def varTy(cr: Type)(using ctx: Ctx): Type = codeBaseTy(Wildcard(cr, cr), Wildcard.out(Type.Bot))
  def regionTy(sk: Type)(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("Region").get.sym, Wildcard(sk, sk) :: Nil)
  def refTy(ct: Type, sk: Type)(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("Ref").get.sym, Wildcard(ct, ct) :: Wildcard.out(sk) :: Nil)
  private val builtinClasses = Ls(
    "Any", "Int", "Num", "Str", "Bool", "Nothing", "CodeBase", "Region", "Ref"
  )
  private val infVarState = new InfVarUid.State()
  private val int2IntBinTy =
    (ctx: Ctx) => Type.FunType(intTy(using ctx) :: intTy(using ctx) :: Nil, intTy(using ctx), Type.Bot)
  private val int2BoolBinTy =
    (ctx: Ctx) => Type.FunType(intTy(using ctx) :: intTy(using ctx) :: Nil, boolTy(using ctx), Type.Bot)
  private val int2NumBinTy =
    (ctx: Ctx) => Type.FunType(intTy(using ctx) :: intTy(using ctx) :: Nil, numTy(using ctx), Type.Bot)
  private val num2NumBinTy =
    (ctx: Ctx) => Type.FunType(numTy(using ctx) :: numTy(using ctx) :: Nil, numTy(using ctx), Type.Bot)
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
      val tv: Type.InfVar = Type.InfVar(1, infVarState.nextUid, new VarState())
      Type.PolymorphicType(tv :: Nil, Type.FunType(tv :: tv :: Nil, boolTy(using ctx), Type.Bot))
    })
  )
  private val builtinVals = Map(
    "run" -> ((ctx: Ctx) => Type.FunType(codeTy(Type.Bot)(using ctx) :: Nil, Type.Top, Type.Bot)),
    "error" -> ((ctx: Ctx) => Type.Bot),
    "log" -> ((ctx: Ctx) => Type.FunType(strTy(using ctx) :: Nil, Type.Top, Type.Bot)),
  )
  def isOp(name: Str): Bool = builtinOps.contains(name)
  def init(predefs: Map[Str, Symbol]): Ctx =
    val ctx = new Ctx(None, 0, HashMap.empty, HashMap.empty, HashMap.empty)
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

class BBTyper(raise: Raise, val initCtx: Ctx):
  private val infVarState = new InfVarUid.State()
  private val solver = new ConstraintSolver(raise, infVarState)

  import NormalForm.SkolemSet

  private def freshVar(using ctx: Ctx): Type.InfVar = Type.InfVar(ctx.lvl, infVarState.nextUid, new VarState())
  private def freshWildcard(using ctx: Ctx) = Wildcard(freshVar, freshVar)

  private val allocSkolem = freshVar(using initCtx)

  private def typeCheckArgs(args: Term)(using ctx: Ctx, skolems: MutSkolemSet): (Ls[Type], Ls[Type]) = args match
    case Term.Tup(flds) => flds.flatMap(f =>
      val (ty, eff) = typeCheck(f.value)
      Left(ty) :: Right(eff) :: Nil
    ).partitionMap(x => x)
    case _ => ???

  private def error(msg: Ls[Message -> Opt[Loc]]) =
    raise(ErrorReport(msg))
    Type.Bot // TODO: error type?

  private def extract(asc: Term)(using map: Map[Uid[Symbol], Wildcard], pol: Bool)(using ctx: Ctx): Type = asc match
    case Ref(cls: ClassSymbol) =>
      ctx.getDef(cls.nme) match
        case S(_) =>
          if cls.nme == "Any" then
            Type.Top
          else if cls.nme == "Nothing" then
            Type.Bot
          else
            Type.ClassType(cls, Nil)
        case N => 
          error(msg"Definition not found: ${cls.nme}" -> asc.toLoc :: Nil)
    case Ref(sym: VarSymbol) =>
      map.get(sym.uid) match
        case Some(Wildcard(in, out)) => if pol then out else in
        case _ => ctx.get(sym).getOrElse(error(msg"Type variable not found: ${sym.name}" -> asc.toLoc :: Nil))
    case FunTy(Term.Tup(params), ret) =>
      Type.FunType(params.map {
        case Fld(_, p, _) => extract(p)(using map, !pol)
      }, extract(ret), Type.Bot) // TODO: effect
    case Term.Forall(tvs, body) =>
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      val bd = tvs.map:
        case sym: VarSymbol =>
          val tv = freshVar
          nestCtx += sym -> tv // TODO: a type var symbol may be better...
          tv
      Type.PolymorphicType(bd, extract(body))
    case _ => error(msg"${asc.toString} is not a valid class member type" -> asc.toLoc :: Nil) // TODO

  private def typeType(ty: Term)(using ctx: Ctx, allowPoly: Bool): Type = ty match
    case Ref(sym: VarSymbol) =>
      ctx.get(sym) match
        case Some(ty) => ty
        case _ =>
          error(msg"Variable not found: ${sym.name}" -> ty.toLoc :: Nil)
    case Ref(cls: ClassSymbol) =>
      ctx.getDef(cls.nme) match
        case S(_) =>
          if cls.nme == "Any" then
            Type.Top
          else if cls.nme == "Nothing" then
            Type.Bot
          else
            Type.ClassType(cls, Nil) // TODO: tparams?
        case N => 
          error(msg"Definition not found: ${cls.nme}" -> ty.toLoc :: Nil)
    case FunTy(Term.Tup(params), ret) =>
      Type.FunType(params.map {
        case Fld(_, p, _) => typeType(p)
      }, typeType(ret), Type.Bot) // TODO: effect
    case Term.Forall(tvs, body) if allowPoly =>
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      val bd = tvs.map:
        case sym: VarSymbol =>
          val tv = freshVar
          nestCtx += sym -> tv // TODO: a type var symbol may be better...
          tv
      Type.PolymorphicType(bd, typeType(body))
    case _: Term.Forall =>
      error(msg"Polymorphic type is not allowed here." -> ty.toLoc :: Nil)
    case Term.TyApp(lhs, targs) => typeType(lhs) match
      case Type.ClassType(cls, _) => Type.ClassType(cls, targs.map {
        case Term.WildcardTy(in, out) =>
          Wildcard(
            in.map(t => typeType(t)(using ctx, false)).getOrElse(Type.Bot),
            out.map(t => typeType(t)(using ctx, false)).getOrElse(Type.Top)
          )
        case t => typeType(t)(using ctx, false)
      })
      case _ => error(msg"${lhs.toString} is not a class" -> ty.toLoc :: Nil)
    case CompType(lhs, rhs, pol) =>
      Type.ComposedType(typeType(lhs), typeType(rhs), pol)
    case _ => error(msg"${ty.toString} is not a valid type annotation" -> ty.toLoc :: Nil) // TODO

  private def instantiate(ty: Type)(using map: Map[Uid[Type.InfVar], Type.InfVar]): Type = ty match
    case Type.ClassType(name, targs) =>
      Type.ClassType(name, targs.map {
        case Wildcard(in, out) => Wildcard(instantiate(in), instantiate(out))
        case ty: Type => instantiate(ty)
      })
    case v @ Type.InfVar(lvl, uid, state) =>
      map.get(uid).getOrElse(v)
    case Type.FunType(args, ret, eff) =>
      Type.FunType(args.map(instantiate), instantiate(ret), instantiate(eff))
    case Type.ComposedType(lhs, rhs, pol) =>
      Type.ComposedType(instantiate(lhs), instantiate(rhs), pol)
    case Type.NegType(ty) => Type.NegType(instantiate(ty))
    case Type.PolymorphicType(tv, body) => Type.PolymorphicType(tv, instantiate(body))
    case Type.Top | Type.Bot => ty
  
  @tailrec
  private def constrain(lhs: Type, rhs: Type)(using ctx: Ctx, skolems: MutSkolemSet): Unit = (lhs, rhs) match
    case (Type.PolymorphicType(tvs1, bd1), Type.PolymorphicType(tvs2, bd2)) =>
      if tvs1.length != tvs2.length then
        error(msg"Cannot check polymorphic types ${lhs.toString} and ${rhs.toString}" -> N :: Nil)
      else
        val mapping = tvs1.zip(tvs2).flatMap {
          case (Type.InfVar(_, uid1, _), Type.InfVar(_, uid2, _)) =>
            val nv = freshVar
            uid1 -> nv :: uid2 -> nv :: Nil
        }.toMap
        constrain(instantiate(bd1)(using mapping), instantiate(bd2)(using mapping))
    case (lhs, Type.PolymorphicType(tvs, body)) =>
      constrain(lhs, body)(using ctx, skolems ++ tvs.map(_.uid))
    case (Type.PolymorphicType(tvs, bd), rhs) =>
      constrain(instantiate(bd)(using (tvs.map {
        case Type.InfVar(_, uid, _) =>
          val nv = freshVar
          uid -> nv
      }).toMap), rhs)
    case _ =>
      given SkolemSet = skolems.toSet
      solver.constrain(lhs, rhs)

  private def typeCode(code: Term)(using ctx: Ctx, skolems: MutSkolemSet): (Type, Type) = code match
    case Lit(_) => (Type.Bot, Type.Bot)
    case Ref(sym: Symbol) if sym.nme == "error" => (Type.Bot, Type.Bot)
    case Lam(params, body) =>
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      val bds = params.map:
        case Param(_, sym, _) =>
          val sk = freshVar
          nestCtx &= sym -> sk
          sk
      val (bodyTy, eff) = typeCode(body)
      val res = freshVar(using ctx)
      val uni = Type.ComposedType(bds.foldLeft[Type](Type.Bot)((res, bd) => Type.ComposedType(res, bd, true)), res, true)
      constrain(bodyTy, uni)
      (res, eff)
    case Term.App(Ref(sym: TermSymbol), Term.Tup(rhs)) if Ctx.isOp(sym.nme) =>
      rhs.foldLeft[(Type, Type)]((Type.Bot, Type.Bot))((res, p) =>
        val (ty, eff) = typeCode(p.value)
        (Type.ComposedType(res._1, ty, true), Type.ComposedType(res._2, eff, true))
      )
    case Term.App(lhs, Term.Tup(rhs)) =>
      val (ty1, eff1) = typeCode(lhs)
      val (ty2, eff2) = rhs.foldLeft[(Type, Type)]((Type.Bot, Type.Bot))((res, p) =>
        val (ty, eff) = typeCode(p.value)
        (Type.ComposedType(res._1, ty, true), Type.ComposedType(res._2, eff, true))
      )
      (Type.ComposedType(ty1, ty2, true), Type.ComposedType(eff1, eff2, true))
    case Term.Unquoted(body) =>
      val (ty, eff) = typeCheck(body)
      val tv = freshVar
      constrain(ty, Ctx.codeTy(tv))
      (tv, eff)
    case Term.Blk(LetBinding(pat, rhs) :: Nil, body) => // TODO: more than one?
      val (rhsTy, rhsEff) = typeCode(rhs)(using ctx)
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      val bd = pat match
        case Pattern.Var(sym) =>
          val sk = freshVar
          nestCtx &= sym -> sk
          sk
        case _ => ???
      val (bodyTy, bodyEff) = typeCode(body)
      val res = freshVar(using ctx)
      val uni = Type.ComposedType(bd, res, true)
      constrain(bodyTy, uni)
      (Type.ComposedType(rhsTy, res, true), Type.ComposedType(rhsEff, bodyEff, true))
    case Term.If(Split.Cons(TermBranch.Boolean(cond, Split.Else(cons)), Split.Else(alts))) =>
      val (condTy, condEff) = typeCode(cond)
      val (consTy, consEff) = typeCode(cons)
      val (altsTy, altsEff) = typeCode(alts)
      (Type.ComposedType(condTy, Type.ComposedType(consTy, altsTy, true), true), Type.ComposedType(condEff, Type.ComposedType(consEff, altsEff, true), true))
    case _ =>
      (error(msg"Cannot quote ${code.toString}" -> code.toLoc :: Nil), Type.Bot)

  // TODO: refactor
  private def typeFunDef(sym: Symbol, lam: Term, sig: Opt[Term], t: Term, pctx: Ctx)(using ctx: Ctx, skolems: MutSkolemSet) = lam match
    case Term.Lam(params, body) =>
      // * parameters, return, effect, new skolems
      def rec(sig: Opt[Type]): (Ls[Type], Opt[Type], Opt[Type], Ls[Type.InfVar]) = sig match
        case S(ft @ Type.FunType(args, ret, eff)) => (args, S(ret), S(eff), Nil)
        case S(Type.PolymorphicType(tvs, ty)) => rec(S(ty)) match
          case (p, r, e, s) => (p, r, e, tvs ++ s)
        case _ => (params.map {
          case Param(_, _, S(sign)) =>
            typeType(sign)(using ctx, true)
          case _ => freshVar
        }, N, N, Nil)
      given Bool = true
      val sigTy = sig.map(typeType)
      sigTy.foreach(sig => pctx += sym -> sig) // for recursive types
      val (tvs, retAnno, effAnno, newSkolems) = rec(sigTy)
      val defCtx = sigTy match
        case S(_: Type.PolymorphicType) => ctx.nextLevel
        case _ => ctx.nest
      if params.length != tvs.length then
         error(msg"Cannot type function ${t.toString} as ${sig.toString}" -> t.toLoc :: Nil)
      else
        val argsTy = params.zip(tvs).map:
          case (Param(_, sym, _), ty) =>
            defCtx += sym -> ty
            ty
        given Ctx = defCtx
        given MutSkolemSet = skolems ++ newSkolems.map(_.uid)
        val (bodyTy, eff) = typeCheck(body)
        retAnno.foreach(anno => constrain(bodyTy, anno))
        effAnno.foreach(anno => constrain(eff, anno))
        if sigTy.isEmpty then
          pctx += sym -> Type.FunType(argsTy, bodyTy, eff)
    case _ => ???

  private def typeSplit(split: TermSplit)(using ctx: Ctx, skolems: MutSkolemSet): (Type, Type) = split match
    case Split.Cons(TermBranch.Boolean(cond, Split.Else(cons)), alts) =>
      val (condTy, condEff) = typeCheck(cond)
      val (consTy, consEff) = typeCheck(cons)
      val (altsTy, altsEff) = typeSplit(alts)
      val allEff = Type.ComposedType(condEff, Type.ComposedType(consEff, altsEff, true), true)
      constrain(condTy, Ctx.boolTy)
      (consTy, altsTy) match
        case (lhs: Type.PolymorphicType, rhs) =>
          constrain(lhs, rhs)
          (lhs, allEff)
        case (lhs, rhs: Type.PolymorphicType) =>
          constrain(lhs, rhs)
          (rhs, allEff)
        case (lhs, rhs) => (Type.ComposedType(lhs, rhs, true), allEff)
    case Split.Cons(TermBranch.Match(scrutinee, Split.Cons(PatternBranch(Pattern.Class(sym, _, _), cons), Split.NoSplit)), alts) =>
      val (clsTy, tv, emptyTy) = ctx.getDef(sym.nme) match
        case S(ClassDef.Parameterized(_, tparams, _, _, _)) =>
          (Type.ClassType(sym, tparams.map(_ => freshWildcard)), freshVar, Type.ClassType(sym, tparams.map(_ => Wildcard.empty)))
        case S(ClassDef.Plain(_, tparams, _, _)) =>
          (Type.ClassType(sym, tparams.map(_ => freshWildcard)), freshVar, Type.ClassType(sym, tparams.map(_ => Wildcard.empty)))
        case _ =>
          error(msg"Cannot match ${scrutinee.toString} as ${sym.toString}" -> split.toLoc :: Nil)
          (Type.Bot, Type.Bot, Type.Bot)
      val (scrutineeTy, scrutineeEff) = typeCheck(scrutinee)
      constrain(scrutineeTy, Type.ComposedType(clsTy, Type.ComposedType(tv, Type.NegType(emptyTy), false), true))
      val nestCtx1 = ctx.nest
      val nestCtx2 = ctx.nest
      scrutinee match // * refine
        case Ref(sym: VarSymbol) =>
          nestCtx1 += sym -> clsTy
          nestCtx2 += sym -> tv
        case _ => ()
      val (consTy, consEff) = typeSplit(cons)(using nestCtx1)
      val (altsTy, altsEff) = typeSplit(alts)(using nestCtx2)
      val allEff = Type.ComposedType(scrutineeEff, Type.ComposedType(consEff, altsEff, true), true)
      (consTy, altsTy) match
        case (lhs: Type.PolymorphicType, rhs) =>
          constrain(lhs, rhs)
          (lhs, allEff)
        case (lhs, rhs: Type.PolymorphicType) =>
          constrain(lhs, rhs)
          (rhs, allEff)
        case (lhs, rhs) => (Type.ComposedType(lhs, rhs, true), allEff)
    case Split.Else(alts) => typeCheck(alts)

  
  private def typeCheck(t: Term)(using ctx: Ctx, skolems: MutSkolemSet): (Type, Type) = t match
    case Ref(sym: VarSymbol) =>
      ctx.get(sym) match
        case Some(ty) => (ty, Type.Bot)
        case _ =>
          (error(msg"Variable not found: ${sym.name}" -> t.toLoc :: Nil), Type.Bot)
    case Ref(sym: TermSymbol) =>
      ctx.get(sym) match
        case Some(ty) => (ty, Type.Bot)
        case _ =>
          (error(msg"Definition not found: ${sym.nme}" -> t.toLoc :: Nil), Type.Bot)
    case Blk(stats, res) =>
      val nestCtx = ctx.nest
      given Ctx = nestCtx
      val effBuff = ListBuffer.empty[Type]
      stats.foreach:
        case term: Term => typeCheck(term)
        case LetBinding(Pattern.Var(sym), rhs) =>
          val (rhsTy, eff) = typeCheck(rhs)
          effBuff += eff
          nestCtx += sym -> rhsTy
        case TermDefinition(Fun, sym, Some(params), sig, Some(body), _) =>
          typeFunDef(sym, Term.Lam(params, body), sig, t, ctx)
        case TermDefinition(Fun, sym, N, sig, Some(body), _) =>
          typeFunDef(sym, body, sig, t, ctx)
        case clsDef: ClassDef => ctx *= clsDef
        case _ => () // TODO
      val (ty, eff) = typeCheck(res)
      (ty, effBuff.foldLeft(eff)((res, e) => Type.ComposedType(res, e, true)))
    case Lit(lit) => ((lit match
      case _: IntLit => Ctx.intTy
      case _: DecLit => Ctx.numTy
      case _: StrLit => Ctx.strTy
      case _: UnitLit => Type.Top
      case _: BoolLit => Ctx.boolTy), Type.Bot)
    case Lam(params, body) =>
      val nestCtx = ctx.nest
      given Ctx = nestCtx
      val tvs = params.map:
        case Param(_, sym, sign) =>
          given Bool = true
          val ty = sign.map(typeType).getOrElse(freshVar)
          nestCtx += sym -> ty
          ty
      val (bodyTy, eff) = typeCheck(body) 
      (Type.FunType(tvs, bodyTy, eff), Type.Bot)
    case Term.App(Term.Sel(Term.Ref(cls: ClassSymbol), field), Term.Tup(Fld(_, term, asc) :: Nil)) => // * Sel
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
          constrain(ty, Type.ClassType(cls, targs))
          (params.map {
            case Param(_, sym, sign) =>
              if sym.nme == field.name then sign else N
          }.filter(_.isDefined)) match
            case S(res) :: Nil => (extract(res)(using map.toMap, true), eff)
            case _ => (error(msg"${field.name} is not a valid member in class ${cls.nme}" -> t.toLoc :: Nil), Type.Bot)
        case S(ClassDef.Plain(_, tparams, _, _)) =>
          ???
        case N => 
          (error(msg"Definition not found: ${cls.nme}" -> t.toLoc :: Nil), Type.Bot)
    case Term.App(lhs, rhs) => typeCheck(lhs) match
      case (Type.FunType(args, ret, eff), lhsEff) => // * if the function type is known, we can directly use it
        val (argTy, argEff) = typeCheckArgs(rhs)
        if args.length != argTy.length then
          (error(msg"The number of parameters is incorrect" -> t.toLoc :: Nil), Type.Bot)
        else
          argTy.zip(args).foreach:
            case (lhs, rhs) => constrain(lhs, rhs)
          (ret, argEff.foldLeft[Type](Type.ComposedType(eff, lhsEff, true))((res, e) => Type.ComposedType(res, e, true)))
      case (Type.PolymorphicType(tvs, body), lhsEff) => instantiate(body)(using (tvs.map {
        case Type.InfVar(_, uid, _) =>
          val nv = freshVar
          uid -> nv
      }).toMap) match // TODO: refactor
        case Type.FunType(args, ret, eff) => 
          val (argTy, argEff) = typeCheckArgs(rhs)
          if args.length != argTy.length then
            (error(msg"The number of parameters is incorrect" -> t.toLoc :: Nil), Type.Bot)
          else
            argTy.zip(args).foreach:
              case (lhs, rhs) => constrain(lhs, rhs)
            (ret, argEff.foldLeft[Type](Type.ComposedType(eff, lhsEff, true))((res, e) => Type.ComposedType(res, e, true)))
        case _ => ???
      case (funTy, lhsEff) =>
        val (argTy, argEff) = typeCheckArgs(rhs)
        val effVar = freshVar
        val retVar = freshVar
        constrain(funTy, Type.FunType(argTy, retVar, effVar))
        (retVar, argEff.foldLeft[Type](Type.ComposedType(effVar, lhsEff, true))((res, e) => Type.ComposedType(res, e, true)))
    case Term.New(cls, args) =>
      ctx.getDef(cls.nme) match
        case S(ClassDef.Parameterized(_, tparams, params, _, _)) =>
          if args.length != params.length then
            (error(msg"The number of parameters is incorrect" -> t.toLoc :: Nil), Type.Bot)
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
                val (ty, eff) = typeCheck(arg)
                constrain(ty, extract(sign)(using map.toMap, true))
                effBuff += eff
              case _ => ???
            }
            (Type.ClassType(cls, targs), effBuff.foldLeft[Type](Type.Bot)((res, e) => Type.ComposedType(res, e, true)))
        case S(ClassDef.Plain(_, tparams, _, _)) =>
          ???
        case N => 
          (error(msg"Definition not found: ${cls.nme}" -> t.toLoc :: Nil), Type.Bot)
    case Term.Asc(term, ty) =>
      given Bool = true
      val res = typeType(ty)
      val (tty, eff) = typeCheck(term)
      constrain(tty, res)
      (res, eff)
    case Term.Forall(tvs, body) =>
      val nestCtx = ctx.nextLevel
      val bds = tvs.map:
        case sym: VarSymbol =>
          val tv = freshVar(using nestCtx)
          nestCtx += sym -> tv // TODO: a type var symbol may be better...
          tv
      val (bodyTy, eff) = typeCheck(body)(using nestCtx, skolems ++ bds.map(_.uid))
      constrain(eff, Type.Bot) // * never generalize terms with effects
      (Type.PolymorphicType(bds, bodyTy), Type.Bot)
    case Term.If(branches) => typeSplit(branches)
    case Term.Region(sym, body) =>
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      val sk = freshVar
      nestCtx += sym -> Ctx.regionTy(sk)
      skolems += sk.uid
      val (res, eff) = typeCheck(body)
      val tv = freshVar(using ctx)
      constrain(eff, Type.ComposedType(tv, sk, true))
      (res, Type.ComposedType(tv, allocSkolem, true))
    case Term.RegRef(reg, value) =>
      val (regTy, regEff) = typeCheck(reg)
      val (valTy, valEff) = typeCheck(value)
      val sk = freshVar
      constrain(regTy, Ctx.regionTy(sk))
      (Ctx.refTy(valTy, sk), Type.ComposedType(sk, Type.ComposedType(regEff, valEff, true), true))
    case Term.Set(lhs, rhs) =>
      val (lhsTy, lhsEff) = typeCheck(lhs)
      val (rhsTy, rhsEff) = typeCheck(rhs)
      val sk = freshVar
      constrain(lhsTy, Ctx.refTy(rhsTy, sk))
      (rhsTy, Type.ComposedType(sk, Type.ComposedType(lhsEff, rhsEff, true), true))
    case Term.Deref(ref) =>
      val (refTy, refEff) = typeCheck(ref)
      val sk = freshVar
      val ctnt = freshVar
      constrain(refTy, Ctx.refTy(ctnt, sk))
      (ctnt, Type.ComposedType(sk, refEff, true))
    case Term.Quoted(body) =>
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      val (ctxTy, eff) = typeCode(body)
      (Ctx.codeTy(ctxTy), eff)
    case _: Term.Unquoted =>
      (error(msg"Unquote should nest in quasiquote" -> t.toLoc :: Nil), Type.Bot)
    case Term.Error =>
      (Type.Bot, Type.Bot) // TODO: error type?

  def typePurely(t: Term): Type =
    val (ty, eff) = typeCheck(t)(using initCtx, LinkedHashSet(allocSkolem.uid))
    constrain(eff, allocSkolem)(using initCtx, LinkedHashSet(allocSkolem.uid))
    ty
