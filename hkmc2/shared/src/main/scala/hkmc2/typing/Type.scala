package hkmc2
package typing

import mlscript.utils.*, shorthands.*
import semantics.{TypeSymbol, VarSymbol}

object Type:
end Type

sealed trait TypeArg:
  def subst(f: PartialFunction[Type.Ref, Type]): this.type
  def show: Str
  
  def ub = this match
    case Wildcard(_, out) => out
    case ty: Type => ty
  def lb = this match
    case Wildcard(in, _) => in
    case ty: Type => ty
end TypeArg

enum Type extends TypeArg:
  case Error
  case Top
  case Bot
  case Ref(sym: TypeSymbol | VarSymbol, args: Ls[TypeArg])
  case Fun(args: Ls[Type], ret: Type, eff: Opt[Type])
  case Neg(t: Type)
  case Union(lhs: Type, rhs: Type)
  case Inter(lhs: Type, rhs: Type)
  
  override def show: Str = this match
    case Error => "‹error›"
    case Top => "⊤"
    case Bot => "⊥"
    case Ref(sym, Nil) => sym.nme
    case Ref(sym, args) =>
      s"${sym.nme}[${args.map(_.show).mkString(", ")}]"
    case Fun(args, ret, eff) =>
      val effStr = eff.map(e => s" ! ${e.show}").getOrElse("")
      s"(${args.map(_.show).mkString(", ")}) -> ${ret.show}$effStr"
    case Neg(t) =>
      s"¬${t.show}"
    case Union(l, r) =>
      s"(${l.show} ∨ ${r.show})"
    case Inter(l, r) =>
      s"(${l.show} ∧ ${r.show})"
  
  override def subst(f: PartialFunction[Ref, Type]): this.type =
    this.match
      case Error => Error
      case Top => Top
      case Bot => Bot
      case ref: Ref if f.isDefinedAt(ref) =>
        f(ref)
      case ref: Ref =>
        Ref(ref.sym, ref.args.map(_.subst(f)))
      case Fun(args, ret, eff) =>
        Fun(args.map(_.subst(f)), ret.subst(f), eff.map(_.subst(f)))
      case Neg(t) =>
        Neg(t.subst(f))
      case Union(l, r) =>
        Union(l.subst(f), r.subst(f))
      case Inter(l, r) =>
        Inter(l.subst(f), r.subst(f))
    .asInstanceOf[this.type]
  
end Type

case class Wildcard(in: Type, out: Type) extends TypeArg:
  
  override def subst(f: PartialFunction[Type.Ref, Type]): this.type =
    Wildcard(in.subst(f), out.subst(f)).asInstanceOf
  
  override def show: Str =
    s"? <: ${out.show} >: ${in.show}"

end Wildcard


