package mlscript
package ucs
package stages

import utils._, shorthands._, Message.MessageContext
import context.{Context, Pattern, Scrutinee}
import pretyper.Traceable, pretyper.symbol._

trait CoverageChecking { self: Desugarer with Traceable =>
  import CoverageChecking._

  def checkCoverage(term: Term)(implicit context: Context): Ls[Diagnostic] = {
    // Collect an immutable map from scrutinees to patterns.
    val registry: ScrutineePatternSetMap = context.scrutinees.flatMap { scrutinee =>
      val caseSet = CaseSet(scrutinee.patternsIterator.toList)
      scrutinee.aliasesIterator.map(alias => (alias -> scrutinee) -> caseSet)
    }.toMap
    println("collected match registry: " + showRegistry(registry))
    checkCoverage(term, Map.empty, registry, Map.empty)
  }

  private def checkCoverage(
      term: Term,
      pending: ScrutineePatternSetMap,
      working: ScrutineePatternSetMap,
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
      case CaseOf(Scrutinee.WithVar(scrutineeVar, scrutinee), cases) =>
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
              val classSymbol = className.getClassLikeSymbol.getOrElse {
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
      scrutinee: Scrutinee.WithVar,
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
  private def showRegistry(registry: ScrutineePatternSetMap): Str =
    if (registry.isEmpty) "empty" else
      registry.iterator.map { case (scrutineeVar -> scrutinee, matchedClasses) =>
        matchedClasses.patterns.iterator.map(_.showInDiagnostics).mkString(s">>> ${scrutineeVar.name} => [", ", ", "]")
      }.mkString("\n", "\n", "")

  type ScrutineePatternSetMap = Map[Scrutinee.WithVar, CaseSet]

  type SeenRegistry = Map[Scrutinee.WithVar, (TypeSymbol, Ls[Loc], CaseSet)]

  implicit class SeenRegistryOps(val self: SeenRegistry) extends AnyVal {
    def showDbg: Str = if (self.isEmpty) "empty" else
      self.iterator.map { case ((k, _), (s, _, _)) => s"${k.name} is ${s.name}" }.mkString(", ")
  }

  /**
    * A `CaseSet` represents all patterns that a particular scrutinee is
    * being matched with within a UCS expression.
    *
    * @param patterns a list of patterns.
    */
  final case class CaseSet(val patterns: List[Pattern]) {
    def showInDiagnostics: Str =
      patterns.iterator.map(_.showInDiagnostics).mkString("[", ", ", "]")

    /** Get a iterator of all class-like patterns. */
    def classLikePatterns: Iterator[Pattern.ClassLike] = patterns.iterator.flatMap {
      case pattern: Pattern.ClassLike => S(pattern)
      case _: Pattern.Literal | _: Pattern.Tuple => N
    }

    /** Separate a class-like pattern if it appears in `patterns`. */
    def separate(classLikeSymbol: ClassLikeSymbol): Opt[(Pattern.ClassLike, Ls[Pattern.ClassLike])] = {
      classLikePatterns.foldRight[(Opt[Pattern.ClassLike], Ls[Pattern.ClassLike])]((N, Nil)) {
        case (pattern, (S(separated), rest)) => (S(separated), pattern :: rest)
        case (pattern, (N, rest)) if pattern.classLikeSymbol === classLikeSymbol => (S(pattern), rest)
        case (pattern, (N, rest)) => (N, pattern :: rest)
      } match {
        case (N, _) => N
        case (S(separated), rest) => S((separated, rest))
      }
    }
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
      * @param classLikeSymbol the type symbol represents the class like type
      * @return If the pattern set doesn't include the given type symbol, this
      *         returns `None`. Otherwise, the function returns a triplet of the
      *         locations where the pattern appears, the related patterns, and
      *         unrelated patterns.
      */
    def split(classLikeSymbol: ClassLikeSymbol): Opt[(Pattern.ClassLike, CaseSet, CaseSet)] = {
      def mk(pattern: Pattern): Opt[Lit \/ TypeSymbol] = pattern match {
        case Pattern.ClassLike(classLikeSymbol, _) => S(R(classLikeSymbol))
        case Pattern.Literal(literal) => S(L(literal))
        case _ => N
      }
      separate(classLikeSymbol) match {
        case N => N
        case S((pattern, patterns)) =>
          val (unrelated, related) = patterns.partitionMap { otherPattern =>
            if (compareCasePattern(mk(otherPattern), mk(pattern))) {
              R(otherPattern)
            } else {
              L(otherPattern)
            }
          }
          S((pattern, CaseSet(related), CaseSet(unrelated)))
      }
    }

    @inline def remove(boolLit: Var): CaseSet = {
      require(boolLit.name === "true" || boolLit.name === "false")
      CaseSet(patterns.filter(!_.matches(boolLit)))
    }

    @inline def remove(literal: Lit): CaseSet =
      CaseSet(patterns.filter(!_.matches(literal)))

    @inline def isEmpty: Bool = patterns.isEmpty

    @inline def size: Int = patterns.size
  }
}
