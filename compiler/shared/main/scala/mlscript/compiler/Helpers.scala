package mlscript.compiler

import mlscript.{App, Asc, Assign, Bind, Blk, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var, Fld, If}
import mlscript.{IfBody, IfThen, IfElse, IfLet, IfOpApp, IfOpsApp, IfBlock}
import mlscript.UnitLit
import mlscript.codegen.Helpers.inspect as showStructure
import mlscript.compiler.mono.MonomorphError

object Helpers:
  /**
   * Extract parameters for monomorphization from a `Tup`.
   */
  def toFuncParams(term: Term): Iterator[Parameter] = term match
    case Tup(fields) => fields.iterator.flatMap {
      // The new parser emits `Tup(_: UnitLit(true))` from `fun f() = x`.
      case (_, Fld(_, _, UnitLit(true))) => None
      case (_, Fld(_, spec, Var(name))) => Some((spec, Expr.Ref(name)))
      case _ => throw new MonomorphError(
        s"only `Var` can be parameters but we meet ${showStructure(term)}"
      )
    }
    case _ => throw MonomorphError("expect the list of parameters to be a `Tup`")
  
  def toFuncArgs(term: Term): IterableOnce[Term] = term match
    // The new parser generates `(undefined, )` when no arguments.
    // Let's do this temporary fix.
    case Tup((_, Fld(_, _, UnitLit(true))) :: Nil) => Iterable.empty
    case Tup(fields) => fields.iterator.map(_._2.value)
    case _ => Some(term)
