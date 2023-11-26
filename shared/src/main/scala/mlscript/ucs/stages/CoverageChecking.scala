package mlscript.ucs.stages

import mlscript.{Case, CaseBranches, CaseOf, Let, Loc, NoCases, Term, Var, Wildcard}
import mlscript.pretyper.{ScrutineeSymbol, Symbol}
import mlscript.utils._, shorthands._
import mlscript.Message, Message.MessageContext
import mlscript.pretyper.shortName
import scala.annotation.tailrec
import mlscript.{SimpleTerm, Diagnostic, ErrorReport, WarningReport}

trait CoverageChecking { self: mlscript.pretyper.Traceable =>
  import CoverageChecking._

  def checkCoverage(term: Term): Ls[Diagnostic] = {
    val registry = collectRegistry(term)
    println("collected match register: " + showRegistry(registry))
    checkCoverage(term, Map.empty, registry, Map.empty)
  }

  private def collectRegistry(term: Term): MatchRegistry = {
    @tailrec
    def rec(acc: MatchRegistry, rest: Ls[Term]): MatchRegistry = rest match {
      case Nil => acc
      case head :: tail => head match {
        case Let(_, _, _, body) => rec(acc, body :: tail)
        case CaseOf(Scrutinee(_, scrutinee), cases) =>
          rec(
            acc.updatedWith(scrutinee)(vs => S(cases.foldLeft(vs.getOrElse(Set.empty))({ 
              case (acc, (className: Var) -> _) => acc + className
              case (acc, _) => acc
            })((x, _) => x))),
            tail ++ cases.foldLeft(Nil: Ls[Term])({ case (acc, _ -> body) => body :: acc })((x, _) => x)
          )
        case _ => rec(acc, tail)
      }
    }
    rec(Map.empty, term :: Nil)
  }

  private def checkCoverage(
      term: Term,
      pending: MatchRegistry,
      working: MatchRegistry,
      assumptions: Map[ScrutineeSymbol, Var]
  ): Ls[Diagnostic] =
    trace(s"checkCoverage <== ${shortName(term)}, ${pending.size} pending, ${working.size} working") {
      println(s"assumptions: " + (if (assumptions.isEmpty) "empty" else
        assumptions.iterator.map { case (k, v) => s"${k.name} is $v" }.mkString(", ")
      ))
      term match {
        case Let(_, _, _, body) => checkCoverage(body, pending, working, assumptions)
        case CaseOf(Scrutinee(scrutineeVar, scrutinee), cases) =>
          println(s"scrutinee: ${scrutinee.name}")
          // If the scrutinee is still pending (i.e., not matched yet), then we
          // remove it from the pending list. If the scrutinee is matched, and
          // there are still classes to be matched, then we find the remaining
          // classes from the working list. If neither of the above is true,
          // there are two possible cases:
          // 1. The scrutinee has been never visited, which is an error.
          // 2. It has been matched to be an instance of some class. Therefore,
          //    we need to check if this is a contradiction.
          val (unseenClasses, newPending) = pending.get(scrutinee) match {
            case S(matchedClasses) => matchedClasses -> (pending - scrutinee)
            case N => working.get(scrutinee) match {
              case S(unseenClasses) => unseenClasses -> pending
              case N => throw new Exception(s"Scrutinee ${scrutinee.name} is not matched.")
            }
          }
          // We keep removing classes from the unseen class list and adding
          // diagnostics (warnings and errors).
          cases.foldLeft((unseenClasses, Nil: Ls[Diagnostic]))({
            case ((red, acc), (className: Var) -> body) =>
              if (red contains className) {
                (
                  // The class is matched. Remove it from the class list.
                  red - className,
                  // We remove the scrutinee from the working list and add
                  // `scrutinee` is `className` to the assumptions.
                  acc ++ checkCoverage(body, newPending, working - scrutinee, assumptions + (scrutinee -> className))
                )
              } else {
                red -> (acc :+ (assumptions.get(scrutinee) match {
                  case S(`className`) => WarningReport("tautology", Nil, Diagnostic.PreTyping)
                  case S(otherClassName) => ErrorReport("contradiction", Nil, Diagnostic.PreTyping)
                  case N => ErrorReport("unvisited scrutinee", Nil, Diagnostic.PreTyping)
                }))
              }
            case (acc, _ -> _) =>
              println("CANNOT check literal patterns")
              acc
          }) {
            case ((missingCases, diagnostics), N) =>
              println("MISSING cases: " + missingCases.iterator.map(className => s"${scrutinee.name} is $className").mkString("[", ", ", "]"))
              diagnostics ++ (missingCases.iterator.map { className  =>
                ErrorReport({
                  val s1 = assumptions.iterator.map {
                    case (scrutinee, className) => s"${scrutinee.name} is $className"
                  }.mkString(", ")
                  val s2 = if (s1.isEmpty) "" else s" $s1, and"
                  msg"missing a case where$s2 ${scrutinee.name} is ${className.name}" -> N ::
                    msg"missing the condition" -> className.toLoc ::
                    assumptions.iterator.zipWithIndex.map({ case (scrutinee, className) -> index =>
                      msg"${if (index > 0) "and" else "when"} ${scrutinee.name} is ${className.name}" -> className.toLoc
                    }).toList
                }, true, Diagnostic.PreTyping)
              })
            case ((unseenClasses, diagnostics), S(default)) =>
              println("wildcard case")
              checkCoverage(default, newPending, working.updated(scrutinee, unseenClasses), assumptions)
          }
        case other => println("STOP"); Nil
      }
    }(ls => s"checkCoverage ==> ${ls.length}")
}

object CoverageChecking {
  type MatchRegistry = Map[ScrutineeSymbol, Set[Var]]

  /** A helper function that prints entries from the given registry line by line. */
  def showRegistry(registry: MatchRegistry): Str =
    if (registry.isEmpty) "empty" else
      registry.iterator.map { case (scrutinee, matchedClasses) =>
        matchedClasses.iterator.mkString(s">>> ${scrutinee.name} => [", ", ", "]")
      }.mkString("\n", "\n", "")
}
