package mlscript.ucs.stages

import mlscript.{Case, CaseOf, Let, NoCases, Term, Var, Wildcard}
import mlscript.pretyper.{Symbol}
import mlscript.utils._, shorthands._
import mlscript.CaseBranches

trait PostProcessing { self: mlscript.pretyper.Traceable =>
  def postProcess(term: Term): Term = trace(s"postProcess <== ${term.describe}") {
    // Normalized terms are constructed using `Let` and `CaseOf`.
    term match {
      case top @ CaseOf(scrutinee: Var, fst @ Case(pattern, body, NoCases)) =>
        println(s"found a UNARY case: $scrutinee is $pattern")
        top.copy(cases = fst.copy(body = postProcess(body)))
      case top @ CaseOf(scrutinee: Var, fst @ Case(pattern, trueBranch, snd @ Wildcard(falseBranch))) =>
        println(s"found a BINARY case: $scrutinee is $pattern")
        println("post-processing the true branch")
        val processedTrueBranch = postProcess(trueBranch)
        println("post-processing the false branch")
        val processedFalseBranch = postProcess(falseBranch)
        // Check if the false branch is another `CaseOf` with the same scrutinee.
        processedFalseBranch match {
          case CaseOf(otherScrutinee: Var, actualFalseBranch) =>
            if (scrutinee.symbol === otherScrutinee.symbol) {
              println(s"identical: $scrutinee === $otherScrutinee")
              if (scrutinee.name =/= otherScrutinee.name) {
                // TODO: solve name collision by creating a lifted `Let`
                ???
              }
              println(s"actual false branch: $actualFalseBranch")
              top.copy(cases = fst.copy(body = processedTrueBranch, rest = actualFalseBranch))
            } else {
              println(s"different: $scrutinee =/= $otherScrutinee")
              top.copy(cases = fst.copy(body = processedTrueBranch, rest = snd.copy(body = processedFalseBranch)))
            }
          case other => top
        }
      // We recursively process the body of `Let` bindings.
      case let @ Let(_, _, _, body) => let.copy(body = postProcess(body))
      // Otherwise, this is not a part of a normalized term.
      case other => println(s"CANNOT post-process"); other
    }
  }()

  private def hasScrutinee(term: Term, symbol: Symbol): Bool = {
    term match {
      case CaseOf(scrutinee: Var, Case(pattern, trueBranch, Wildcard(falseBranch))) =>
        if (scrutinee.symbolOption.exists(_ === symbol)) true
        else hasScrutinee(trueBranch, symbol) || hasScrutinee(falseBranch, symbol)
      case Let(_, _, _, body) => hasScrutinee(body, symbol)
      case _ => false
    }
  }

  private def separateCaseBranches(term: Term)(implicit scrutinee: Symbol): (CaseBranches, Term) = ???
}

object PostProcessing {

}
