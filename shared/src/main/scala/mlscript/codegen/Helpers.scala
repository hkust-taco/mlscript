package mlscript.codegen

import mlscript._, mlscript.utils.shorthands._
import scala.collection.immutable.{Map, Set}

object Helpers {
  /**
    * Show how a term is actually structured.
    */
  def inspect(t: Terms): Str = t match {
    case Var(name)     => s"Var($name)"
    case Lam(lhs, rhs) => s"Lam(${inspect(lhs)}, ${inspect(rhs)})"
    case App(lhs, rhs) => s"App(${inspect(lhs)}, ${inspect(rhs)})"
    case Tup(fields) =>
      val entries = fields map {
        case (S(name), Fld(_, _, value)) => s"$name: ${inspect(value)}"
        case (N, Fld(_, _, value))       => s"_: ${inspect(value)}"
      }
      s"Tup(${entries mkString ", "})"
    case Rcd(fields) =>
      val entries = fields.iterator
        .map { case k -> Fld(_, _, v) => s"${inspect(k)} = ${inspect(v)}" }
        .mkString(", ")
      s"Rcd($entries)"
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
          s"Case($clsNme, ${inspect(body)}, ${inspectCaseBranches(rest)})"
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
    case Def(rec, nme, rhs, isByname) =>
      s"Def($rec, $nme, ${rhs.fold(inspect, "" + _)}, $isByname)"
  }

  def inspect(body: IfBody): Str = body match {
    case IfElse(expr) => s"IfElse(${inspect(expr)}"
    case IfThen(expr, rhs) => s"IfThen(${inspect(expr)}, ${inspect(rhs)}"
    case IfBlock(lines) => s"IfBlock(${
      lines.iterator.map {
        case L(body) => inspect(body)
        case R(NuFunDef(S(isRec), nme, _, L(rhs))) =>
          s"Let($isRec, ${nme.name}, ${inspect(rhs)})"
        case R(_) => ???
      }.mkString(";")
    })"
    case IfOpsApp(lhs, opsRhss) => s"IfOpsApp(${inspect(lhs)}, ${
      opsRhss.iterator.map { case (op, body) =>
        s"$op -> ${inspect(body)}"
      }
    }".mkString("; ")
    case IfLet(isRec, name, rhs, body) => ???
    case IfOpApp(lhs, op, rhs) =>
      s"IfOpApp(${inspect(lhs)}, ${inspect(op)}, ${inspect(rhs)}"
  }
  def inspect(t: TypingUnit): Str = t.entities.iterator
    .map {
      case term: Term => inspect(term)
      case NuFunDef(lt, nme, targs, L(term)) =>
        s"NuFunDef(${lt}, ${nme.name}, ${targs.mkString("[", ", ", "]")}, ${inspect(term)})"
      case NuFunDef(lt, nme, targs, R(ty)) =>
        s"NuFunDef(${lt}, ${nme.name}, ${targs.mkString("[", ", ", "]")}, $ty)"
      case NuTypeDef(kind, nme, tparams, params, parents, body) =>
        s"NuTypeDef(${kind.str}, ${nme.name}, ${tparams.mkString("(", ", ", ")")}, ${
          inspect(params)}, ${parents.map(inspect).mkString("(", ", ", ")")}, ${inspect(body)})"
      case others => others.toString()
    }
    .mkString("TypingUnit(", ", ", ")")
}
