package mlscript.ucs.stages

import annotation.tailrec
import collection.mutable.ListBuffer
import mlscript.{Case, CaseBranches, CaseOf, Let, Lit, Loc, NoCases, Term, Var, Wildcard}
import mlscript.pretyper.symbol._
import mlscript.utils._, shorthands._
import mlscript.Message, Message.MessageContext
import mlscript.{SimpleTerm, Diagnostic, ErrorReport, WarningReport}

trait CoverageChecking { self: mlscript.pretyper.Traceable =>
  import CoverageChecking._

  def checkCoverage(term: Term): Ls[Diagnostic] = {
    val registry = collectRegistry(term)
    println("collected match registry: " + showRegistry(registry))
    checkCoverage(term, Map.empty, registry, Map.empty)
  }

  private def collectRegistry(term: Term): MatchRegistry = {
    @tailrec
    def rec(acc: MatchRegistry, rest: Ls[Term]): MatchRegistry =
      rest match {
        case Nil => println("end"); acc
        case head :: tail =>
          println(s"collect ${inspect.shallow(head)}")
          head match {
            case Let(_, _, _, body) =>
              println(s"continue on ${inspect.shallow(body)}")
              rec(acc, body :: tail)
            case CaseOf(Scrutinee(_, scrutinee), cases) =>
              println(s"scrutinee: ${scrutinee.name}")
              rec(
                acc.updatedWith(scrutinee)(vs => S(cases.foldLeft(vs.getOrElse(CaseSet.empty))({ 
                  case (acc, (className: Var) -> _) =>
                    println(s"found pattern $className (has location = ${className.toLoc.nonEmpty})")
                    val classLikeSymbol = className.symbolOption.flatMap(_.typeSymbolOption).getOrElse {
                      throw new Exception(s"$className is not associated with any type symbol.")
                    }
                    acc.add(classLikeSymbol, className.toLoc)
                  case (acc, (literal: Lit) -> _) =>
                    println(s"TODO: skipped literal $literal")
                    acc
                })((x, _) => x))),
                tail ++ cases.foldLeft
                  (Nil: Ls[Term])
                  ({ case (acc, _ -> body) => body :: acc })
                  ((acc, els) => els.fold(acc)(_ :: acc))
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
      seen: SeenRegistry
  ): Ls[Diagnostic] =
    trace(s"checkCoverage <== ${inspect.shallow(term)}, ${pending.size} pending, ${working.size} working, ${seen.size} seen") {
      println(s"seen: " + (if (seen.isEmpty) "empty" else
        seen.iterator.map { case (k, (s, _, _)) => s"${k.name} is ${s.name}" }.mkString(", ")
      ))
      term match {
        case Let(_, _, _, body) => checkCoverage(body, pending, working, seen)
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
          val (unseenPatterns, newPending) = pending.get(scrutinee) match {
            case S(matchedClasses) => matchedClasses -> (pending - scrutinee)
            case N => working.get(scrutinee) match {
              case S(unseenPatterns) => unseenPatterns -> pending
              case N =>
                // Neither in the working list nor in the pending list.
                seen.get(scrutinee) match {
                  // The scrutine may have been matched.
                  case S((_, _, remainingPatterns)) => remainingPatterns -> pending
                  case N =>
                    // The scrutinee has never been visited. This should not happen.
                    println("working list: " + showRegistry(working))
                    throw new Exception(s"Scrutinee ${scrutinee.name} is not in the working list.")
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
                    working - scrutinee
                  else
                    working.updated(scrutinee, remainingPatterns)
                  // Add "`scrutinee` is `className`" to the seen registry.
                  val newSeen = seen + (scrutinee -> (classSymbol, locations, refiningPatterns))
                  (
                    remainingPatterns,
                    diagnostics ++ checkCoverage(body, newPending, newWorking, newSeen)
                  )
                case N =>
                  unseenPatterns -> (diagnostics :+ (seen.get(scrutinee) match {
                    case S((`classSymbol`, _, _)) => WarningReport("tautology", Nil, Diagnostic.PreTyping)
                    case S(_) => ErrorReport("contradiction", Nil, Diagnostic.PreTyping)
                    case N => ErrorReport("unvisited scrutinee", Nil, Diagnostic.PreTyping)
                  }))
              }
            case (diagnostics, (_: Lit) -> _) =>
              println("CANNOT check literal patterns")
              diagnostics
          }) {
            case ((missingCases, diagnostics), N) =>
              println("remaining cases should are not covered")
              println("MISSING cases: " + missingCases.patterns.mkString("[", ", ", "]"))
              diagnostics ++ explainMissingCases(scrutinee, seen, missingCases)
            case ((remainingCases, diagnostics), S(default)) =>
              println("remaining cases should be covered by the wildcard")
              checkCoverage(default, newPending, working.updated(scrutinee, remainingCases), seen)
          }
        case other => println("STOP"); Nil
      }
    }(ls => s"checkCoverage ==> ${ls.length} diagnostics")
}

object CoverageChecking {
  type MatchRegistry = Map[ScrutineeSymbol, CaseSet]

  type SeenRegistry = Map[ScrutineeSymbol, (TypeSymbol, Ls[Loc], CaseSet)]

  sealed abstract class Pattern {
    override def toString(): String = this match {
      case Pattern.ClassLike(symbol) => s"${symbol.defn.kind.str} `${symbol.name}`"
      case Pattern.Tuple(_) => "tuple"
      case Pattern.Literal(literal) => s"literal ${inspect.deep(literal)}"
    }
  }
  object Pattern {
    final case class ClassLike(symbol: TypeSymbol) extends Pattern
    final case class Tuple(TODO: Nothing) extends Pattern // To be implemented in the near future.
    final case class Literal(literal: Lit) extends Pattern
  }

  /**
    * A `CaseSet` represents all patterns that a particular scrutinee is
    * being matched with within a UCS expression. Each Pattern is associated
    * with the locations where these patterns appear.
    *
    * @param patterns a set of patterns that the scrutinee is matched with.
    * @param hasWildcard if the scrutinee is matched with a wildcard pattern.
    */
  final case class CaseSet(val cases: Map[Pattern, Ls[Loc]], val hasWildcard: Bool) {
    /** TODO: This seems useless. */
    @inline def withWildcard: CaseSet = if (hasWildcard) this else copy(hasWildcard = true)

    /**
      * Split the pattern set into two pattern sets.
      * 
      * For example, let A be the base type of B, C, and D. Plus, class `Z` is
      * unrelated to any of them. Suppose the initial pattern set is
      * `{ A, B, C, Z }`. Splitting the set results in two sets, one set
      * contains classes that are compatible with `A`, and the other set
      * contains classes that are unrelated to `A`.
      * 
      * For example, if we split the set with `A`, then we get `{ B, C }` and
      * set `{ Z }`. Set `{ B, C }` represents that the scrutinee can be further
      * refined to class `B` or `class C`. Set `{ Z }` represents that if the
      * scrutinee is not `A`, then it can be `Z`.
      * 
      * If `A` is sealed to `B`, `C`, and `D`, then we get `{ B, C, D }` and
      * `{ Z }`. Because if the scrutinee is assumed to be `A`, then it can also
      * be `D` other than `B`, `C`.
      *
      * @param classLikeSymbol the type symbol represents the class like type
      * @return If the pattern set doesn't include the given type symbol, this
      *         returns `None`. Otherwise, the function returns a triplet of the
      *         locations where the pattern appears, the related patterns, and
      *         unrelated patterns.
      */
    def split(classLikeSymbol: TypeSymbol): Opt[(Ls[Loc], CaseSet, CaseSet)] = {
      val classLikePattern = Pattern.ClassLike(classLikeSymbol)
      cases.get(classLikePattern).map { locations =>
        val withoutSymbol = cases - classLikePattern
        val relatedPatterns = withoutSymbol.filter {
          case (Pattern.ClassLike(otherSymbol), _) => otherSymbol.baseTypes.contains(classLikeSymbol)
          case (_: Pattern.Tuple | _: Pattern.Literal) -> _ => false
        } ++ classLikeSymbol.sealedDerivedTypes.iterator.map { symbol =>
          Pattern.ClassLike(symbol) -> symbol.defn.nme.toLoc.toList
        }
        val unrelatedPatterns = withoutSymbol.filter {
          case (Pattern.ClassLike(otherSymbol), _) => !otherSymbol.baseTypes.contains(classLikeSymbol)
          case (_: Pattern.Tuple | _: Pattern.Literal) -> _ => true
        }
        (locations, copy(relatedPatterns), copy(unrelatedPatterns))
      }
    }

    /** Add a type sysmbol as a class like pattern to the set. */
    def add(classLikeSymbol: TypeSymbol, location: Opt[Loc]): CaseSet = {
      val classLikePattern = Pattern.ClassLike(classLikeSymbol)
      copy(cases = cases.updatedWith(classLikePattern) {
        case N => S(location.toList)
        case S(locations) => S(location.toList ++ locations)
      })
    }

    /** Get an iterator of only patterns. */
    @inline def patterns: Iterator[Pattern] = cases.iterator.map(_._1)

    @inline def isEmpty: Bool = cases.isEmpty

    @inline def size: Int = cases.size
  }

  object CaseSet {
    lazy val empty: CaseSet = CaseSet(Map.empty, false)
  }

  /** Create an `ErrorReport` that explains missing cases. */
  private def explainMissingCases(scrutinee: ScrutineeSymbol, seen: SeenRegistry, missingCases: CaseSet): Opt[ErrorReport] =
    if (missingCases.isEmpty) {
      N
    } else {
      S(ErrorReport({
        val lines = (msg"Scrutinee `${scrutinee.name}` has ${"missing case".pluralize(missingCases.size, true)}" -> scrutinee.toLoc) ::
          (missingCases.cases.iterator.flatMap { case (pattern, locations) =>
            (msg"It can be ${pattern.toString}" -> locations.headOption) :: Nil
          }.toList)
        if (seen.isEmpty) {
          lines
        } else {
          seen.iterator.zipWithIndex.map { case ((scrutinee, (classSymbol, locations, cases)), i) =>
            val prologue = if (i === 0) "When " else ""
            val epilogue = if (seen.size === 1) "" else if (i === seen.size - 1) ", and" else ","
            msg"${prologue}scrutinee `${scrutinee.name}` is `${classSymbol.name}`$epilogue" -> locations.headOption
          }.toList ::: lines
        }
      }, true, Diagnostic.PreTyping))
    }

  /** A helper function that prints entries from the given registry line by line. */
  private def showRegistry(registry: MatchRegistry): Str =
    if (registry.isEmpty) "empty" else
      registry.iterator.map { case (scrutinee, matchedClasses) =>
        matchedClasses.patterns.mkString(s">>> ${scrutinee.name} => [", ", ", "]")
      }.mkString("\n", "\n", "")
}
