package hkmc2
package semantics

import mlscript.utils.*, shorthands.*

object Type:
end Type

sealed trait TypeArgImpl:
  self: Type =>
end TypeArgImpl

type TypeArg = Type & TypeArgImpl

enum Type extends TypeArgImpl:
  case Error
  case Top
  case Bot
  case Ref(sym: TypeSymbol | VarSymbol)
  case App(base: Type, args: Ls[TypeArg])
  case Fun(args: Ls[Type], ret: Type, eff: Opt[Type])
  case Neg(t: Type)
  case Union(lhs: Type, rhs: Type)
  case Inter(lhs: Type, rhs: Type)
  case Wildcard(in: Type, out: Type)
  
  def show: Str = this match
    case Error => "‹error›"
    case Top => "⊤"
    case Bot => "⊥"
    case Ref(sym) => sym.nme
    case App(base, args) =>
      s"${base.show}[${args.map(_.show).mkString(", ")}]"
    case Fun(args, ret, eff) =>
      val effStr = eff.map(e => s" ! ${e.show}").getOrElse("")
      s"(${args.map(_.show).mkString(", ")}) -> ${ret.show}$effStr"
    case Neg(t) =>
      s"¬${t.show}"
    case Union(l, r) =>
      s"(${l.show} ∨ ${r.show})"
    case Inter(l, r) =>
      s"(${l.show} ∧ ${r.show})"
    case Wildcard(i, o) =>
      s"in ${i.show} out ${o.show}"
  
  def subst(f: Ref => Type): Type = 
    this match
    case Error => Error
    case Top => Top
    case Bot => Bot
    case ref @ Ref(sym) =>
      f(ref)
    case App(base, args) =>
      App(base.subst(f), args.map(_.subst(f)))
    case Fun(args, ret, eff) =>
      Fun(args.map(_.subst(f)), ret.subst(f), eff.map(_.subst(f)))
    case Neg(t) =>
      Neg(t.subst(f))
    case Union(l, r) =>
      Union(l.subst(f), r.subst(f))
    case Inter(l, r) =>
      Inter(l.subst(f), r.subst(f))
    case Wildcard(i, o) =>
      Wildcard(i.subst(f), o.subst(f))
  
end Type

