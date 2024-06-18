package hkmc2
package bbml

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import semantics.*, semantics.Term.*
import syntax.*
import Tree.*

sealed abstract class TypeArg

case class Wildcard(in: Type, out: Type) extends TypeArg {
  private def printWhenSet(t: Type, in: Bool) = t match
    case Type.InfVar(_, _, state) =>
      if in && !state.upperBounds.isEmpty then S(s"in $t")
      else if !in && !state.lowerBounds.isEmpty then S(s"out $t")
      else N
    case _ => S(t.toString())

  override def toString(): String =
    Ls(printWhenSet(in, true), printWhenSet(out, false)).filter(_.isDefined).map(_.get).mkString(" ")
}

enum Type extends TypeArg:
  case ClassType(name: ClassSymbol, targs: Ls[TypeArg])
  case InfVar(lvl: Int, uid: Uid[InfVar], state: VarState)
  case FunType(args: Ls[Type], ret: Type, eff: Type)
  case ComposedType(lhs: Type, rhs: Type, pol: Bool) // * positive -> union
  case NegType(ty: Type)
  case PolymorphicType(lvl: Int, tv: Ls[InfVar], body: Type)
  case Top // TODO: level?
  case Bot
  override def toString(): String = this match
    case ClassType(name, targs) =>
      if targs.isEmpty then s"${name.nme}" else s"${name.nme}[${targs.mkString(", ")}]"
    case InfVar(lvl, uid, state) => s"α${uid}" // TODO: bounds?
    case FunType(args, ret, eff) => s"(${args.mkString(", ")}) ->{${eff}} ${ret}"
    case ComposedType(lhs, rhs, pol) => s"${lhs} ${if pol then "∨" else "∧"} ${rhs}"
    case NegType(ty) => s"¬${ty}"
    case PolymorphicType(lvl, tv, body) => s"forall($lvl) ${tv.mkString(", ")}: $body"
    case Top => "⊤"
    case Bot => "⊥"

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

type IntType = Type.ClassType
object IntType:
  def apply(): IntType = Type.ClassType(ClassSymbol(Tree.Ident("Int")), Nil)

type NumType = Type.ClassType
object NumType:
  def apply(): NumType = Type.ClassType(ClassSymbol(Tree.Ident("Num")), Nil)

type StrType = Type.ClassType
object StrType:
  def apply(): StrType = Type.ClassType(ClassSymbol(Tree.Ident("Str")), Nil)

type BoolType = Type.ClassType
object BoolType:
  def apply(): BoolType = Type.ClassType(ClassSymbol(Tree.Ident("Bool")), Nil)

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
  private val int2NumBinTy =
    (ctx: Ctx) => Type.FunType(intTy(using ctx) :: intTy(using ctx) :: Nil, numTy(using ctx), Type.Bot)
  private val builtinFuns = Map(
    "+" -> int2IntBinTy,
    "-" -> int2IntBinTy,
    "*" -> int2IntBinTy,
    "/" -> int2NumBinTy,
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
  private val solver = new ConstraintSolver(raise)

  private def freshVar(using ctx: Ctx): Type.InfVar = Type.InfVar(ctx.lvl, infVarState.nextUid, new VarState())
  private def freshWildcard(using ctx: Ctx) = Wildcard(freshVar, freshVar)

  private def typeCheckArgs(args: Term)(using ctx: Ctx): Ls[Type] = args match
    case Term.Tup(flds) => flds.map(f => typeCheck(f.value))
    case _ => ???

  private def error(msg: Ls[Message -> Opt[Loc]]) =
    raise(ErrorReport(msg))
    Type.Bot // TODO: error type?

  private def extract(asc: Term)(using map: Map[Uid[Symbol], Wildcard], pol: Bool)(using ctx: Ctx): Type = asc match
    case Ref(cls: ClassSymbol) =>
      ctx.getDef(cls.nme) match
        case S(_) => Type.ClassType(cls, Nil) // TODO: tparams?
        case N => 
          error(msg"Definition not found: ${cls.nme}" -> asc.toLoc :: Nil)
    case Ref(sym: VarSymbol) =>
      map.get(sym.uid) match
        case Some(Wildcard(in, out)) => if pol then out else in
        case _ =>
          error(msg"Type variable not found: ${sym.name}" -> asc.toLoc :: Nil)
    case FunTy(Term.Tup(params), ret) =>
      Type.FunType(params.map {
        case Fld(_, p, _) => extract(p)(using map, !pol)
      }, extract(ret), Type.Bot) // TODO: effect
    case _ => error(msg"${asc.toString} is not a valid class member type" -> asc.toLoc :: Nil) // TODO

  private def typeType(ty: Term)(using ctx: Ctx): Type = ty match
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
    case ForallTy(tvs, body) =>
      val nestCtx = ctx.nextLevel
      given Ctx = nestCtx
      val bd = tvs.map:
        case sym: VarSymbol =>
          val tv = freshVar
          nestCtx += sym -> tv // TODO: a type var symbol may be better...
          tv
      Type.PolymorphicType(nestCtx.lvl, bd, typeType(body))
    case _ => error(msg"${ty.toString} is not a valid type annotation" -> ty.toLoc :: Nil) // TODO

  def typeCheck(t: Term)(using ctx: Ctx): Type = t match
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
          def rec(sig: Opt[Type]): (Ls[Type], Opt[Type], Opt[Type]) = sig match
            case S(ft @ Type.FunType(args, ret, eff)) => (args, S(ret), S(eff))
            case S(Type.PolymorphicType(_, _, ty)) => rec(S(ty))
            case _ => (params.map(_ => freshVar), N, N)
          val sigTy = sig.map(typeType)
          val (tvs, retAnno, effAnno) = rec(sigTy)
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
            val bodyTy = typeCheck(body)(using defCtx)
            retAnno.foreach(anno => solver.constrain(bodyTy, anno))
            sigTy match
              case S(Type.PolymorphicType(lvl, bds, _)) =>
                ctx += sym -> Type.PolymorphicType(lvl, bds, Type.FunType(argsTy, bodyTy, Type.Bot)) // TODO: eff
              case _ =>
                ctx += sym -> Type.FunType(argsTy, bodyTy, Type.Bot) // TODO: eff
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
      val tvs = params.map(
        sym =>
          val v = freshVar
          nestCtx += sym -> v
          v
      )
      Type.FunType(tvs, typeCheck(body), Type.Bot) // TODO: effect
    case Term.App(Term.Sel(Term.Ref(cls: ClassSymbol), field), Term.Tup(Fld(_, term, asc) :: Nil)) =>
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
          solver.constrain(ty, Type.ClassType(cls, targs))
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
    case Term.App(lhs, rhs) =>
      val funTy = typeCheck(lhs)
      val argTy = typeCheckArgs(rhs)
      val effVar = freshVar
      val retVar = freshVar
      solver.constrain(funTy, Type.FunType(argTy, retVar, effVar))
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
                solver.constrain(typeCheck(arg), extract(sign)(using map.toMap, true))
              case _ => ???
            }
            Type.ClassType(cls, targs)
        case S(ClassDef.Plain(_, tparams, _, _)) =>
          ???
        case N => 
          error(msg"Definition not found: ${cls.nme}" -> t.toLoc :: Nil)
    case Term.Asc(term, ty) =>
      val res = typeType(ty) // TODO: poly
      solver.constrain(typeCheck(term), res)
      res
    case Term.Error =>
      Type.Bot // TODO: error type?
