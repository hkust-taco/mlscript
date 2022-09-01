package mlscript.codegen

import mlscript._, mlscript.utils.shorthands._
import scala.collection.immutable.{Map, Set}
import scala.collection.mutable.{Set => MutSet}

object Helpers {
  /**
    * Show how a term is actually structured.
    */
  def inspect(t: Term)(implicit visited: MutSet[Term] = MutSet()): Str = {
    if (visited.contains(t)) return "<circle>"
    visited += t
    t match {
      case Var(name)     => s"Var(\"$name\")"
      case Lam(lhs, rhs) => s"Lam(${inspect(lhs)}, ${inspect(rhs)})"
      case App(lhs, rhs) => s"App(${inspect(lhs)}, ${inspect(rhs)})"
      case Tup(fields) =>
        lazy val entries = fields.iterator.map {
          case (S(name), Fld(m, s, value)) => s"\"$name\": Fld($m, $s, ${inspect(value)})"
          case (N, Fld(m, s, value))       => s"_: Fld($m, $s, ${inspect(value)})"
        }.mkString("", " :: ", " :: Nil")
        s"Tup(${if (fields.isEmpty) "Nil" else entries})"
      case Rcd(fields) =>
        val entries = fields.iterator
          .map { case k -> Fld(_, _, v) => s"${inspect(k)} = ${inspect(v)}" }
          .mkString(", ")
        s"Rcd($entries})"
      case Sel(receiver, fieldName)    => s"Sel(${inspect(receiver)}, $fieldName)"
      case Let(isRec, name, rhs, body) => s"Let($isRec, $name, ${inspect(rhs)}, ${inspect(body)})"
      case Blk(stmts)                  => s"Blk(...)"
      case Bra(rcd, trm)               => s"Bra(rcd = $rcd, ${inspect(trm)})"
      case Asc(trm, ty)                => s"Asc(${inspect(trm)}, $ty)"
      case Bind(lhs, rhs)              => s"Bind(${inspect(lhs)}, ${inspect(rhs)})"
      case Test(trm, ty)               => s"Test(${inspect(trm)}, ${inspect(ty)})"
      case With(trm, fields) =>
        s"With(${inspect(trm)}, ${inspect(fields)})"
      case CaseOf(trm, cases) =>
        def inspectCaseBranches(br: CaseBranches): Str = br match {
          case Case(clsNme, body, rest) =>
            s"Case($clsNme, ${inspect(t)}, ${inspectCaseBranches(rest)})"
          case Wildcard(body) => s"Wildcard(${inspect(body)})"
          case NoCases        => "NoCases"
        }
        s"CaseOf(${inspect(trm)}, ${inspectCaseBranches(cases)}"
      case IntLit(value)  => s"IntLit($value)"
      case DecLit(value)  => s"DecLit($value)"
      case StrLit(value)  => s"StrLit($value)"
      case UnitLit(value)  => s"UnitLit($value)"
      case Subs(arr, idx) => s"Subs(${inspect(arr)}, ${inspect(idx)})"
      case Assign(f, v)   => s"Assign(${inspect(f)}, ${inspect(v)})"
      case Splc(fs)       => 
        val elems = fs.map{case L(l) => s"...${inspect(l)}" case R(Fld(_, _, r)) => inspect(r)}.mkString(", ")
        s"Splc($elems)"
      case If(bod, els) => s"If(${inspect(bod)}, ${els.map(inspect)})"
      case New(base, body) => s"New(${base}, ${body})"
      case TyApp(base, targs) => s"TyApp(${inspect(base)}, ${targs})"
    }
  }

  def inspect(t: IfBody): Str = t match {
    case IfThen(expr, rhs) => s"IfThen(expr := ${inspect(expr)}, rhs := ${inspect(rhs)})"
    case IfElse(expr) => s"IfElse(expr := ${inspect(expr)})"
    case IfLet(isRec, name, rhs, body) =>
      s"IfLet(isRec := $isRec, name := '$name', rhs := ${inspect(rhs)}, body := ${inspect(body)})"
    case IfOpApp(lhs, Var(op), rhs) =>
      s"IfOpApp(lhs := ${inspect(lhs)}, op := $op, rhs := ${inspect(rhs)})"
    case IfOpsApp(lhs, opsRhss) =>
      val opsRhsss = opsRhss.iterator.map {
        case (Var(op), rhs) => s"'$op' -> ${inspect(rhs)}"
      }.mkString("(", ", ", ")")
      s"IfOpsApp(lhs := ${inspect(lhs)}, opsRhss := $opsRhsss)"
    case IfBlock(lines) => lines.map {
      case L(body) => inspect(body)
      case R(stmt) => inspect(stmt)
    }.mkString("IfBlock(", "; ", ")")
  }
  
  def inspect(t: Statement): Str = t match {
    case term: Term => inspect(term)
    case DataDefn(body) => s"DataDefn(${inspect(body)})"
    // Cases below are not implemented.
    case Def(rec, Var(name), rhs) => "Def(...)"
      // s"Def(rec := $rec, $name, ${inspect(rhs)})"
    case TypeDef(kind, nme, tparams, body, mthDecls, mthDefs, positionals) => "TypeDef(...)"
    case NuFunDef(nme, targs, rhs) => "NuFunDef(...)"
    case LetS(isRec, pat, rhs) => "LetS(...)"
    case NuTypeDef(kind, nme, tparams, params, parents, body) => "NuTypeDef(...)"
    case DatatypeDefn(head, body) => "DatatypeDefn(...)"
  }

  def inspect(t: TypingUnit): Str =
    t.entities.iterator.map(inspect).mkString("TypingUnit(", "; ", ")")
}
