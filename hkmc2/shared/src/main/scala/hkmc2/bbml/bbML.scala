package hkmc2
package bbml

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import semantics.*, semantics.Term.*
import syntax.*
import Tree.*

sealed abstract class TypeArg

case class Wildcard(in: Type, out: Type) extends TypeArg

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
    case ClassType(name, targs) => s"${name.nme}" // TODO: targs
    case InfVar(lvl, uid, state) => s"α${uid}" // TODO: bounds?
    case FunType(args, ret, eff) => s"(${args.mkString(", ")}) ->{${eff}} ${ret}"
    case ComposedType(lhs, rhs, pol) => ???
    case NegType(ty) => ???
    case PolymorphicType(lvl, tv, body) => ???
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

// TODO: builtin functions

class VarState:
  var lowerBounds: Ls[Type] = Nil
  var upperBounds: Ls[Type] = Nil

object InfVarUid extends Uid.Handler[Type.InfVar]

final case class Ctx(parent: Option[Ctx], lvl: Int, env: mutable.HashMap[Uid[Symbol], Type]):
  def +=(p: VarSymbol -> Type): Unit = env += p._1.uid -> p._2
  def get(sym: VarSymbol): Option[Type] = env.get(sym.uid) orElse parent.dlof(_.get(sym))(None)
  def nest: Ctx = Ctx(Some(this), lvl, mutable.HashMap.empty)
object Ctx:
  def init(): Ctx = new Ctx(None, 0, mutable.HashMap.empty)

class BBTyper(raise: Raise):

  private val infVarState = new InfVarUid.State()
  private def freshVar(using ctx: Ctx) = Type.InfVar(ctx.lvl, infVarState.nextUid, new VarState())

  def typeCheck(t: Term)(using ctx: Ctx): Type = t match
    case Ref(sym: VarSymbol) =>
      ctx.get(sym) match
        case Some(ty) => ty
        case _ =>
          raise(ErrorReport(msg"Variable not found: ${sym.name}" -> t.toLoc :: Nil))
          Type.Bot // TODO: error type?
    case Ref(cls: ClassSymbol) =>
      ???
    case Blk(stats, res) =>
      typeCheck(res) // TODO: stats
    case Lit(lit) => lit match
      case _: IntLit => IntType()
      case _: DecLit => NumType()
      case _: StrLit => StrType()
      case _: UnitLit => Type.Top
      case _: BoolLit => BoolType()
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
