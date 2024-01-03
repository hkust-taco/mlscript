package mlscript.ucs.stages

import mlscript.{Case, CaseBranches, CaseOf, Let, Lit, Loc, NoCases, Term, Var, Wildcard}
import mlscript.{Diagnostic, ErrorReport, WarningReport}
import mlscript.Message, Message.MessageContext
import mlscript.ucs.context.{Context, CaseSet, NamedScrutineeData, MatchRegistry, ScrutineeData, SeenRegistry}
import mlscript.pretyper.symbol._
import mlscript.utils._, shorthands._

trait CoverageChecking { self: mlscript.pretyper.Traceable =>
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
  )(implicit context: Context): Ls[Diagnostic] =
    trace(s"checkCoverage <== ${term.showDbg}, ${pending.size} pending, ${working.size} working, ${seen.size} seen") {
      println(s"seen: " + (if (seen.isEmpty) "empty" else
        seen.iterator.map { case ((k, _), (s, _, _)) => s"${k.name} is ${s.name}" }.mkString(", ")
      ))
      term match {
        case Let(_, _, _, body) => checkCoverage(body, pending, working, seen)
        case CaseOf(ScrutineeData.WithVar(scrutinee, scrutineeVar), cases) =>
          println(s"scrutinee: ${scrutineeVar.name}")
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
            case ((unseenPatterns, diagnostics), (className: Var) -> body) =>
              val classSymbol = className.symbolOption.flatMap(_.typeSymbolOption).getOrElse {
                throw new Exception(s"$className is not associated with a type symbol")
              }
              println(s"class symbol: ${classSymbol.name}")
              unseenPatterns.split(classSymbol) match {
                case S((locations, refiningPatterns, remainingPatterns)) =>
                  println(s"remove ${className} and it's unrelated patterns from working")
                  println("unseen patterns: " + unseenPatterns.patterns.mkString("[", ", ", "]"))
                  println("remaining patterns: " + remainingPatterns.patterns.mkString("[", ", ", "]"))
                  // Remove the scrutinee from the working list.
                  val newWorking = if (remainingPatterns.isEmpty)
                    working - namedScrutinee
                  else
                    working.updated(namedScrutinee, remainingPatterns)
                  // Add "`scrutinee` is `className`" to the seen registry.
                  val newSeen = seen + (namedScrutinee -> (classSymbol, locations, refiningPatterns))
                  (
                    remainingPatterns,
                    diagnostics ++ checkCoverage(body, newPending, newWorking, newSeen)
                  )
                case N =>
                  unseenPatterns -> (diagnostics :+ (seen.get(namedScrutinee) match {
                    case S((`classSymbol`, _, _)) => WarningReport("tautology", Nil, Diagnostic.PreTyping)
                    case S(_) => ErrorReport("contradiction", Nil, Diagnostic.PreTyping)
                    case N => ErrorReport("unvisited scrutinee", Nil, Diagnostic.PreTyping)
                  }))
              }
            case ((unseenPatterns, diagnostics), (literal: Lit) -> body) =>
              (
                unseenPatterns.remove(literal),
                diagnostics ++ checkCoverage(body, newPending, working - namedScrutinee, seen)
              )
          }) {
            case ((missingCases, diagnostics), N) =>
              println("remaining cases should are not covered")
              println("MISSING cases: " + missingCases.patterns.mkString("[", ", ", "]"))
              diagnostics ++ explainMissingCases(namedScrutinee, seen, missingCases)
            case ((remainingCases, diagnostics), S(default)) =>
              println("remaining cases should be covered by the wildcard")
              checkCoverage(default, newPending, working.updated(namedScrutinee, remainingCases), seen)
          }
        case other => println("STOP"); Nil
      }
    }(ls => s"checkCoverage ==> ${ls.length} diagnostics")
}

object CoverageChecking {
  /** Create an `ErrorReport` that explains missing cases. */
  private def explainMissingCases(scrutinee: NamedScrutineeData, seen: SeenRegistry, missingCases: CaseSet): Opt[ErrorReport] =
    if (missingCases.isEmpty) {
      N
    } else {
      S(ErrorReport({
        val lines = (msg"Scrutinee `${scrutinee._1.name}` has ${"missing case".pluralize(missingCases.size, true)}" -> scrutinee._1.toLoc) ::
          (missingCases.cases.iterator.flatMap { case (pattern, locations) =>
            (msg"It can be ${pattern.toString}" -> locations.headOption) :: Nil
          }.toList)
        if (seen.isEmpty) {
          lines
        } else {
          seen.iterator.zipWithIndex.map { case ((scrutinee, (classSymbol, locations, cases)), i) =>
            val prologue = if (i === 0) "When " else ""
            val epilogue = if (seen.size === 1) "" else if (i === seen.size - 1) ", and" else ","
            msg"${prologue}scrutinee `${scrutinee._1.name}` is `${classSymbol.name}`$epilogue" -> locations.headOption
          }.toList ::: lines
        }
      }, true, Diagnostic.PreTyping))
    }

  /** A helper function that prints entries from the given registry line by line. */
  private def showRegistry(registry: MatchRegistry): Str =
    if (registry.isEmpty) "empty" else
      registry.iterator.map { case (scrutineeVar -> scrutinee, matchedClasses) =>
        matchedClasses.patterns.mkString(s">>> ${scrutineeVar.name} => [", ", ", "]")
      }.mkString("\n", "\n", "")
}
