package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


enum Term extends Statement with Located:
  case Error
  case Lit(lit: Literal)
  case Ref(symbol: Symbol)
  case App(lhs: Term, rhs: Term)
  case Tup(fields: Ls[Fld])
  case If(body: TermSplit)
  case Lam(params: Ls[VarSymbol], body: Term)
  case Blk(stats: Ls[Statement], res: Term)
  
  def describe: Str = ???
  def children: Ls[Located] = ???
import Term.*

trait Statement extends Located:
  def showDbg: Str = this match
    case Lit(lit) => lit.idStr
    case Ref(symbol) => symbol.toString
    case App(lhs, tup: Tup) => s"${lhs.showDbg}${tup.showDbg}"
    case App(lhs, rhs) => s"${lhs.showDbg}(...${rhs.showDbg})"
    case If(body) => s"if $body"
    // case Lam(params, body) => s"λ${params.map(_.name).join(", ")}. $body"
    case Blk(stats, res) =>
      (stats.map(_.showDbg + "; ") :+ (res match { case Lit(Tree.UnitLit(true)) => "" case x => x.showDbg + " " }))
      .mkString("{ ", "", "}")
    case LetBinding(pat, rhs) => s"let ${pat.showDbg} = ${rhs.showDbg}"
    case Error => "<error>"
    case Tup(fields) => fields.map(_.showDbg).mkString("(", ", ", ")")
    case TermDefinition(sym, body) => s"fun ${sym}${
      body match
        case S(x) => " = " + x.showDbg
        case N => ""
      }"

final case class LetBinding(pat: Pattern, rhs: Term) extends Statement:
  def children: Ls[Located] = ???

final case class TermDefinition(sym: TermSymbol, body: Opt[Term]) extends Statement:
  def children: Ls[Located] = ???

final case class FldFlags(mut: Bool, spec: Bool, genGetter: Bool) extends Located:
  def children: Ls[Located] = ???
  def showDbg: Str = (if mut then "mut " else "") + (if spec then "spec " else "") + (if genGetter then "genGetter " else "")

final case class Fld(flags: FldFlags, value: Term) extends FldImpl

object FldFlags { val empty: FldFlags = FldFlags(false, false, false) }

trait FldImpl extends Located:
  self: Fld =>
  def children: Ls[Located] = self.value :: Nil
  def showDbg: Str = flags.showDbg + self.value.showDbg
  def describe: Str =
    (if self.flags.spec then "specialized " else "") +
    (if self.flags.mut then "mutable " else "") +
    self.value.describe


