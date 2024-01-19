package mlscript.ucs.stages

import mlscript.{Case, CaseBranches, CaseOf, Let, Lit, Loc, NoCases, Term, Var, Wildcard}
import mlscript.{Diagnostic, ErrorReport, WarningReport}
import mlscript.Message, Message.MessageContext
import mlscript.ucs.Desugarer
import mlscript.ucs.context.{Context, CaseSet, NamedScrutinee, MatchRegistry, Scrutinee, SeenRegistry}
import mlscript.pretyper.Traceable
import mlscript.pretyper.symbol._
import mlscript.utils._, shorthands._

trait CoverageChecking { self: Desugarer with Traceable =>
  import CoverageChecking._

  def checkCoverage(term: Term)(implicit context: Context): Ls[Diagnostic] = {
    val registry = context.toMatchRegistry
    println("collected match registry: " + showRegistry(registry))
    checkCoverage(term, Map.empty, registry, Map.empty)
  }

  private def checkCoverage(
      term: Term,
      pending: MatchRegistry,
      working: MatchRegistry,
      seen: SeenRegistry
  )(implicit context: Context): Ls[Diagnostic] = {
    term match {
      case Let(_, nme, _, body) =>
        println(s"checkCoverage <== LET `${nme.name}`")
        checkCoverage(body, pending, working, seen)
      case CaseOf(scrutineeVar: Var, Case(Var("true"), body, NoCases)) if context.isTestVar(scrutineeVar) =>
        raiseDesugaringError(msg"missing else branch" -> body.toLoc)
        Nil
      case CaseOf(scrutineeVar: Var, Case(Var("true"), whenTrue, Wildcard(whenFalse))) if context.isTestVar(scrutineeVar) =>
        println(s"checkCoverage <== TEST `${scrutineeVar.name}`")
        checkCoverage(whenTrue, pending, working, seen) ++
          checkCoverage(whenFalse, pending, working, seen)
      case CaseOf(Scrutinee.WithVar(scrutinee, scrutineeVar), cases) =>
        trace(s"checkCoverage <== ${pending.size} pending, ${working.size} working, ${seen.size} seen") {
          println(s"CASE ${scrutineeVar.name}")
          println(s"SEEN: ${seen.showDbg}")
          // If the scrutinee is still pending (i.e., not matched yet), then we
          // remove it from the pending list. If the scrutinee is matched, and
          // there are still classes to be matched, then we find the remaining
          // classes from the working list. If neither of the above is true,
          // there are two possible cases:
          // 1. The scrutinee has been never visited, which is an error.
          // 2. It has been matched to be an instance of some class. Therefore,
          //    we need to check if this is a contradiction.
          val namedScrutinee = scrutineeVar -> scrutinee
          val (unseenPatterns, newPending) = pending.get(namedScrutinee) match {
            case S(matchedClasses) => matchedClasses -> (pending - namedScrutinee)
            case N => working.get(namedScrutinee) match {
              case S(unseenPatterns) => unseenPatterns -> pending
              case N =>
                // Neither in the working list nor in the pending list.
                seen.get(namedScrutinee) match {
                  // The scrutine may have been matched.
                  case S((_, _, remainingPatterns)) => remainingPatterns -> pending
                  case N =>
                    // The scrutinee has never been visited. This should not happen.
                    println("working list: " + showRegistry(working))
                    throw new Exception(s"Scrutinee ${scrutineeVar.name} is not in the working list.")
                }
            }
          }
          // We go through cases and keep removing the current pattern from the
          // unseen pattern set.
          // Meanwhile, we keep adding diagnostics if we meet warnings and errors.
          cases.foldLeft((unseenPatterns, Nil: Ls[Diagnostic]))({
            case ((unseenPatterns, diagnostics), (boolLit: Var) -> body)
                if boolLit.name === "true" || boolLit.name === "false" =>
              (
                unseenPatterns.remove(boolLit),
                diagnostics ++ checkCoverage(body, newPending, working - namedScrutinee, seen)
              )
            case ((unseenPatterns, diagnostics), (className: Var) -> body) =>
              val classSymbol = className.symbolOption.flatMap(_.typeSymbolOption).getOrElse {
                throw new Exception(s"$className is not associated with a type symbol")
              }
              println(s"class symbol: `${classSymbol.name}`")
              unseenPatterns.split(classSymbol) match {
                case S((pattern, refiningPatterns, remainingPatterns)) =>
                  println(s"REMOVE `${className.name}` from working")
                  println(s"unseen: ${unseenPatterns.showInDiagnostics}")
                  println(s"remaining: ${remainingPatterns.showInDiagnostics}")
                  // Remove the scrutinee from the working list.
                  val newWorking = if (remainingPatterns.isEmpty)
                    working - namedScrutinee
                  else
                    working.updated(namedScrutinee, remainingPatterns)
                  // Add "`scrutinee` is `className`" to the seen registry.
                  val newSeen = seen + (namedScrutinee -> (classSymbol, pattern.locations, refiningPatterns))
                  (
                    remainingPatterns,
                    diagnostics ++ checkCoverage(body, newPending, newWorking, newSeen)
                  )
                case N =>
                  println(s"cannot split the set by ${classSymbol.name}")
                  unseenPatterns -> (diagnostics :+ (seen.get(namedScrutinee) match {
                    case S((`classSymbol`, _, _)) => WarningReport("tautology", Nil, Diagnostic.Desugaring)
                    case S(_) => ErrorReport("contradiction", Nil, Diagnostic.Desugaring)
                    case N => ErrorReport("unvisited scrutinee", Nil, Diagnostic.Desugaring)
                  }))
              }
            case ((unseenPatterns, diagnostics), (literal: Lit) -> body) =>
              (
                unseenPatterns.remove(literal),
                diagnostics ++ checkCoverage(body, newPending, working - namedScrutinee, seen)
              )
          }) {
            case ((missingCases, diagnostics), N) =>
              println(s"remaining cases are not covered: ${missingCases.showInDiagnostics}")
              diagnostics ++ explainMissingCases(namedScrutinee, seen, missingCases)
            case ((remainingCases, diagnostics), S(default)) =>
              println("remaining cases should be covered by the wildcard")
              checkCoverage(default, newPending, working.updated(namedScrutinee, remainingCases), seen)
          }
        }(ls => s"checkCoverage ==> ${ls.length} diagnostics")
      case other =>
        println(s"checkCoverage <== TERM ${other.showDbg}")
        Nil
    }
  }
}

object CoverageChecking {
  /** Create an `ErrorReport` that explains missing cases. */
  private def explainMissingCases(
      scrutinee: NamedScrutinee,
      seen: SeenRegistry,
      missingCases: CaseSet
  )(implicit context: Context): Opt[ErrorReport] =
    if (missingCases.isEmpty) {
      N
    } else {
      S(ErrorReport({
        val readableName = scrutinee._2.getReadableName(scrutinee._1)
        val lines = (msg"$readableName has ${"missing case".pluralize(missingCases.size, true)}" -> scrutinee._1.toLoc) ::
          (missingCases.patterns.iterator.flatMap { pattern =>
            (msg"it can be ${pattern.showInDiagnostics}" -> pattern.firstOccurrence) :: Nil
          }.toList)
        if (seen.isEmpty) {
          lines
        } else {
          seen.iterator.zipWithIndex.map { case ((scrutineeVar -> scrutinee, (classSymbol, locations, cases)), i) =>
            val prologue = if (i === 0) "when " else ""
            val epilogue = if (seen.size === 1) "" else if (i === seen.size - 2) ", and" else ","
            val scrutineeName = scrutinee.getReadableName(scrutineeVar)
            msg"$prologue$scrutineeName is `${classSymbol.name}`$epilogue" -> locations.headOption
          }.toList ::: lines
        }
      }, true, Diagnostic.Desugaring))
    }

  /** A helper function that prints entries from the given registry line by line. */
  private def showRegistry(registry: MatchRegistry): Str =
    if (registry.isEmpty) "empty" else
      registry.iterator.map { case (scrutineeVar -> scrutinee, matchedClasses) =>
        matchedClasses.patterns.iterator.map(_.showInDiagnostics).mkString(s">>> ${scrutineeVar.name} => [", ", ", "]")
      }.mkString("\n", "\n", "")
}
