package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


enum Term extends Located:
  case Lit(lit: Literal)
  case Var(symbol: VarSymbol)
  case App(lhs: Term, rhs: Term)
  case Tup(fields: Ls[Fld])
  case If(body: TermSplit)
  case Lam(params: Ls[VarSymbol], body: Term)
  
  def describe: Str = ???
  def children: Ls[Located] = ???


final case class FldFlags(mut: Bool, spec: Bool, genGetter: Bool) extends Located:
  def children: Ls[Located] = ???

final case class Fld(flags: FldFlags, value: Term) extends FldImpl

object FldFlags { val empty: FldFlags = FldFlags(false, false, false) }

trait FldImpl extends Located:
  self: Fld =>
  def children: Ls[Located] = self.value :: Nil
  def describe: Str =
    (if self.flags.spec then "specialized " else "") +
    (if self.flags.mut then "mutable " else "") +
    self.value.describe


