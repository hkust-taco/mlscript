package mlscript.mono

import mlscript.Term
import mlscript.{TypingUnit, NuTypeDef, NuFunDef}
import mlscript.{App, Asc, Assign, Bind, Blk, Block, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var}
import mlscript.{IntLit, DecLit, StrLit, UnitLit}
import mlscript.{CaseBranches, Case, Wildcard, NoCases}

// This converts MLscript syntax trees to monomorphization syntax trees.
// This is deprecated.
object Converter
