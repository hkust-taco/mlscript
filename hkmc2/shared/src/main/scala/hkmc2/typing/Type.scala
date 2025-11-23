package hkmc2
package typing

import mlscript.utils.*, shorthands.*
import semantics.{TypeSymbol, VarSymbol}

sealed trait TypeArg:
  def subst(f: PartialFunction[Type.Ref, Type]): this.type
  def show: Str
  def showDbg: Str
  
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
  
  // A placeholder for types that are not yet implemented.
  case NotImplemented
  
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
    case NotImplemented => "‹not implemented›"
  
  override def showDbg: Str = this match
    case Error => "‹error›"
    case Top => "⊤"
    case Bot => "⊥"
    case Ref(sym, Nil) => s"${sym}"
    case Ref(sym, args) =>
      s"${sym}[${args.map(_.showDbg).mkString(", ")}]"
    case Fun(args, ret, eff) =>
      val effStr = eff.map(e => s" ! ${e.showDbg}").getOrElse("")
      s"(${args.map(_.showDbg).mkString(", ")}) -> ${ret.showDbg}$effStr"
    case Neg(t) =>
      s"¬${t.showDbg}"
    case Union(l, r) =>
      s"(${l.showDbg} ∨ ${r.showDbg})"
    case Inter(l, r) =>
      s"(${l.showDbg} ∧ ${r.showDbg})"
    case NotImplemented => "‹not implemented›"
  
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
      case NotImplemented => NotImplemented
    .asInstanceOf[this.type]
  
  def symbol: Opt[TypeSymbol | VarSymbol] = this match
    case Ref(sym, _) => S(sym)
    case _ => N
  
end Type

case class Wildcard(in: Type, out: Type) extends TypeArg:
  
  override def subst(f: PartialFunction[Type.Ref, Type]): this.type =
    Wildcard(in.subst(f), out.subst(f)).asInstanceOf
  
  override def show: Str =
    s"? <: ${out.show} >: ${in.show}"
  
  override def showDbg: Str =
    s"? <: ${out.showDbg} >: ${in.showDbg}"
  
end Wildcard


