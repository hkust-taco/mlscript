package hkmc2
package bbml

import scala.collection.mutable
import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import semantics.*, semantics.Term.*
import syntax.*
import Tree.*

sealed abstract class TypeArg:
  def lvl(using skolems: NormalForm.SkolemSet): Int

case class Wildcard(in: Type, out: Type) extends TypeArg {
  private def printWhenSet(t: Type, in: Bool) = t match
    case Type.Top if !in => N
    case Type.Bot if in => N
    case _ => S(if in then s"in $t" else s"out $t")

  override def toString(): String =
    (printWhenSet(in, true).toList ++ printWhenSet(out, false).toList).mkString(" ")
  override def lvl(using skolems: NormalForm.SkolemSet): Int = in.lvl.max(out.lvl)
}

enum Type extends TypeArg:
  case ClassType(name: ClassSymbol, targs: Ls[TypeArg])
  case InfVar(lvl: Int, uid: Uid[InfVar], state: VarState)
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
  override def lvl(using skolems: NormalForm.SkolemSet): Int = this match
    case ClassType(name: ClassSymbol, targs: Ls[TypeArg]) =>
      targs.map(_.lvl).maxOption.getOrElse(0)
    case InfVar(lvl: Int, uid: Uid[InfVar], _) =>
      if skolems(uid) then Int.MaxValue else lvl
    case FunType(args: Ls[Type], ret: Type, eff: Type) =>
      (ret :: eff :: args).map(_.lvl).max
    case ComposedType(lhs: Type, rhs: Type, _) =>
      lhs.lvl.max(rhs.lvl)
    case NegType(ty: Type) => ty.lvl
    case PolymorphicType(tv: Ls[InfVar], body: Type) =>
      (body :: tv).map(_.lvl).max
    case Top | Bot => 0
  

type RefType = Type.ClassType
object RefType:
  def apply(cnt: TypeArg, reg: TypeArg): RefType = Type.ClassType(ClassSymbol(Tree.Ident("Ref")), cnt :: reg :: Nil)

type RegionType = Type.ClassType
object RegionType:
  def apply(skolem: TypeArg): RegionType = Type.ClassType(ClassSymbol(Tree.Ident("Region")), skolem :: Nil)

type CodeBaseType = Type.ClassType
object CodeBaseType:
  def apply(cr: TypeArg, isVar: TypeArg): CodeBaseType = Type.ClassType(ClassSymbol(Tree.Ident("CodeBase")), cr :: isVar :: Nil)

type CodeType = CodeBaseType
object CodeType:
  def apply(cr: TypeArg): CodeType = CodeBaseType(cr, Type.Top)

type VarType = CodeBaseType
object VarType:
  def apply(cr: TypeArg): VarType = CodeBaseType(cr, Type.Bot)

class VarState:
  var lowerBounds: Ls[Type] = Nil
  var upperBounds: Ls[Type] = Nil

object InfVarUid extends Uid.Handler[Type.InfVar]

type EnvType = mutable.HashMap[Uid[Symbol], Type]
type clsDefType = mutable.HashMap[Str, ClassDef]
final case class Ctx(parent: Option[Ctx], lvl: Int, clsDefs: clsDefType, env: EnvType): // TODO: skolem
  def +=(p: Symbol -> Type): Unit = env += p._1.uid -> p._2
  def get(sym: Symbol): Option[Type] = env.get(sym.uid) orElse parent.dlof(_.get(sym))(None)
  def *=(cls: ClassDef): Unit = clsDefs += cls.sym.id.name -> cls
  def getDef(name: Str): Option[ClassDef] = clsDefs.get(name) orElse parent.dlof(_.getDef(name))(None)
  def nest: Ctx = Ctx(Some(this), lvl, mutable.HashMap.empty, mutable.HashMap.empty)
  def nextLevel: Ctx = Ctx(Some(this), lvl + 1, mutable.HashMap.empty, mutable.HashMap.empty)

object Ctx:
  def intTy(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("Int").getOrElse(???).sym, Nil)
  def numTy(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("Num").getOrElse(???).sym, Nil)
  def strTy(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("Str").getOrElse(???).sym, Nil)
  def boolTy(using ctx: Ctx): Type = Type.ClassType(ctx.getDef("Bool").getOrElse(???).sym, Nil) // TODO: ???
  private val builtinClasses = Ls(
    "Any", "Int", "Num", "Str", "Bool" // TODO
  )
  private val int2IntBinTy =
    (ctx: Ctx) => Type.FunType(intTy(using ctx) :: intTy(using ctx) :: Nil, intTy(using ctx), Type.Bot)
  private val int2BoolBinTy =
    (ctx: Ctx) => Type.FunType(intTy(using ctx) :: intTy(using ctx) :: Nil, boolTy(using ctx), Type.Bot)
  private val int2NumBinTy =
    (ctx: Ctx) => Type.FunType(intTy(using ctx) :: intTy(using ctx) :: Nil, numTy(using ctx), Type.Bot)
  private val builtinFuns = Map(
    "+" -> int2IntBinTy,
    "-" -> int2IntBinTy,
    "*" -> int2IntBinTy,
    "/" -> int2NumBinTy,
    "<" -> int2BoolBinTy,
    ">" -> int2BoolBinTy,
    // TODO
  )
  def init(predefs: Map[Str, Symbol]): Ctx =
    val ctx = new Ctx(None, 0, mutable.HashMap.empty, mutable.HashMap.empty)
    builtinClasses.foreach(
      cls =>
        predefs.get(cls) match
          case Some(cls: ClassSymbol) => ctx *= ClassDef.Plain(cls, Nil, ObjBody(Term.Blk(Nil, Term.Lit(Tree.UnitLit(true)))), None)
          case _ => ???
    )
    builtinFuns.foreach(
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

  private def typeCheckArgs(args: Term)(using ctx: Ctx, skolems: SkolemSet): Ls[Type] = args match
    case Term.Tup(flds) => flds.map(f => typeCheck(f.value))
    case _ => ???

  private def error(msg: Ls[Message -> Opt[Loc]]) =
    raise(ErrorReport(msg))
    Type.Bot // TODO: error type?

  private def extract(asc: Term)(using map: Map[Uid[Symbol], Wildcard], pol: Bool)(using ctx: Ctx): Type = asc match
    case Ref(cls: ClassSymbol) =>
      ctx.getDef(cls.nme) match
        case S(_) => Type.ClassType(cls, Nil)
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
        case S(_) => Type.ClassType(cls, Nil) // TODO: tparams?
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
  private def constrain(lhs: Type, rhs: Type)(using ctx: Ctx, skolems: SkolemSet): Unit = (lhs, rhs) match
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
    case _ => solver.constrain(lhs, rhs)

  def typeCheck(t: Term)(using ctx: Ctx, skolems: SkolemSet): Type = t match
    case Ref(sym: VarSymbol) =>
      ctx.get(sym) match
        case Some(ty) => ty
        case _ =>
          error(msg"Variable not found: ${sym.name}" -> t.toLoc :: Nil)
    case Ref(sym: TermSymbol) =>
      ctx.get(sym) match
        case Some(ty) => ty
        case _ =>
          error(msg"Definition not found: ${sym.nme}" -> t.toLoc :: Nil)
    case Blk(stats, res) =>
      val nestCtx = ctx.nest
      given Ctx = nestCtx
      stats.foreach:
        case term: Term => typeCheck(term)
        case LetBinding(Pattern.Var(sym), rhs) =>
          val rhsTy = typeCheck(rhs)
          nestCtx += sym -> rhsTy
        case TermDefinition(Fun, sym, Some(params), sig, Some(body), _) =>
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
          val (tvs, retAnno, effAnno, newSkolems) = rec(sigTy)
          val defCtx = sigTy match
            case S(_: Type.PolymorphicType) => nestCtx.nextLevel
            case _ => nestCtx.nest
          if params.length != tvs.length then
             error(msg"Cannot type function ${t.toString} as ${sig.toString}" -> t.toLoc :: Nil)
          else
            val argsTy = params.zip(tvs).map:
              case (Param(_, sym, _), ty) =>
                defCtx += sym -> ty
                ty

            given Ctx = defCtx
            given SkolemSet = skolems ++ newSkolems.map(_.uid)
            val bodyTy = typeCheck(body)
            retAnno.foreach(anno => constrain(bodyTy, anno))
            ctx += sym -> sigTy.getOrElse(Type.FunType(argsTy, bodyTy, Type.Bot)) // TODO: eff
        case clsDef: ClassDef => ctx *= clsDef
        case _ => () // TODO
      typeCheck(res)
    case Lit(lit) => lit match
      case _: IntLit => Ctx.intTy
      case _: DecLit => Ctx.numTy
      case _: StrLit => Ctx.strTy
      case _: UnitLit => Type.Top
      case _: BoolLit => Ctx.boolTy
    case Lam(params, body) =>
      val nestCtx = ctx.nest
      given Ctx = nestCtx
      val tvs = params.map:
        case Param(_, sym, sign) =>
          given Bool = true
          val ty = sign.map(typeType).getOrElse(freshVar)
          nestCtx += sym -> ty
          ty
      Type.FunType(tvs, typeCheck(body), Type.Bot) // TODO: effect
    case Term.App(Term.Sel(Term.Ref(cls: ClassSymbol), field), Term.Tup(Fld(_, term, asc) :: Nil)) => // * Sel
      val ty = typeCheck(term)
      ctx.getDef(cls.nme) match
        case S(ClassDef.Parameterized(_, tparams, params, _, _)) =>
          val map = mutable.HashMap[Uid[Symbol], Wildcard]()
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
            case S(res) :: Nil => extract(res)(using map.toMap, true)
            case _ => error(msg"${field.name} is not a valid member in class ${cls.nme}" -> t.toLoc :: Nil)
        case S(ClassDef.Plain(_, tparams, _, _)) =>
          ???
        case N => 
          error(msg"Definition not found: ${cls.nme}" -> t.toLoc :: Nil)
    case Term.App(lhs, rhs) => typeCheck(lhs) match
      case Type.FunType(args, ret, eff) => // * if the function type is known, we can directly use it
        val argTy = typeCheckArgs(rhs)
        if args.length != argTy.length then
          error(msg"The number of parameters is incorrect" -> t.toLoc :: Nil)
        else
          argTy.zip(args).foreach:
            case (lhs, rhs) => constrain(lhs, rhs)
          ret
      case funTy =>
        val argTy = typeCheckArgs(rhs)
        val effVar = freshVar
        val retVar = freshVar
        constrain(funTy, Type.FunType(argTy, retVar, effVar))
        retVar
    case Term.New(cls, args) =>
      ctx.getDef(cls.nme) match
        case S(ClassDef.Parameterized(_, tparams, params, _, _)) =>
          if args.length != params.length then
            error(msg"The number of parameters is incorrect" -> t.toLoc :: Nil)
          else
            val map = mutable.HashMap[Uid[Symbol], Wildcard]()
            val targs = tparams.map {
              case TyParam(_, targ) =>
                val ty = freshWildcard
                map += targ.uid -> ty
                ty
            }
            args.iterator.zip(params).foreach {
              case (arg, Param(_, _, S(sign))) =>
                constrain(typeCheck(arg), extract(sign)(using map.toMap, true))
              case _ => ???
            }
            Type.ClassType(cls, targs)
        case S(ClassDef.Plain(_, tparams, _, _)) =>
          ???
        case N => 
          error(msg"Definition not found: ${cls.nme}" -> t.toLoc :: Nil)
    case Term.Asc(term, ty) =>
      given Bool = true
      val res = typeType(ty)
      constrain(typeCheck(term), res)
      res
    case Term.Forall(tvs, body) =>
      val nestCtx = ctx.nextLevel
      val bds = tvs.map:
        case sym: VarSymbol =>
          val tv = freshVar(using nestCtx)
          nestCtx += sym -> tv // TODO: a type var symbol may be better...
          tv
      Type.PolymorphicType(bds, typeCheck(body)(using nestCtx, skolems ++ bds.map(_.uid)))
    case Term.If(Split.Cons(TermBranch.Boolean(cond, Split.Else(cons)), Split.Else(alts))) =>
      constrain(typeCheck(cond), Ctx.boolTy)
      (typeCheck(cons), typeCheck(alts)) match
        case (lhs: Type.PolymorphicType, rhs) =>
          constrain(lhs, rhs)
          lhs
        case (lhs, rhs: Type.PolymorphicType) =>
          constrain(lhs, rhs)
          rhs
        case (lhs, rhs) => Type.ComposedType(lhs, rhs, true)
    case Term.Error =>
      Type.Bot // TODO: error type?
