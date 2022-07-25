package mlscript.mono

import mlscript.{App, Asc, Assign, Bind, Blk, Block, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var, Fld, If}
import mlscript.{IfBody, IfTerm, IfThen, IfElse, IfLet, IfOpApp, IfOpsApp, IfBlock}
import mlscript.CaseBranches

object Helpers:
  def toFuncParams(term: Term): IterableOnce[Expr.Ref] = term match
    case Tup(fields) => fields.iterator.map {
      case (_, Fld(mut, spec, Var(name))) => Expr.Ref(name)
      case _ => throw new MonomorphError("only `Var` can be parameters")
    }
    case _ => throw MonomorphError("expect the list of parameters to be a `Tup`")
  
  def toFuncArgs(term: Term): IterableOnce[Term] = term match
    case Tup(fields) => fields.iterator.map(_._2.value)
    case _ => Some(term)
