package mlscript
package ucs
package stages

import annotation.tailrec
import context.{Context, Pattern, Scrutinee}
import pretyper.symbol._
import utils._, shorthands._, Message.MessageContext

trait PostProcessing { self: Desugarer with mlscript.pretyper.Traceable =>
  import PostProcessing._

  def postProcess(term: Term)(implicit context: Context): Term = trace(s"postProcess <== ${term.showDbg}") {
    // Normalized terms are constructed using `Let` and `CaseOf`.
    term match {
      case top @ CaseOf(testVar: Var, fst @ Case(Var("true"), trueBranch, Wildcard(falseBranch))) if context.isTestVar(testVar) =>
        println(s"TEST: ${testVar.name}")
        top.copy(cases = fst.copy(body = postProcess(trueBranch), rest = Wildcard(postProcess(falseBranch)))(refined = fst.refined))
      case top @ CaseOf(Scrutinee(_), Wildcard(body)) => body
      case top @ CaseOf(Scrutinee.WithVar(scrutineeVar, scrutinee), fst @ Case(className: Var, body, NoCases)) =>
        println(s"UNARY: ${scrutineeVar.name} is ${className.name}")
        top.copy(cases = fst.copy(body = postProcess(body))(refined = fst.refined))
      case top @ CaseOf(Scrutinee.WithVar(scrutineeVar, scrutinee), fst @ Case(pat, trueBranch, Wildcard(falseBranch))) =>
        println(s"BINARY: ${scrutineeVar.name} is ${pat.showDbg}")
        println(s"patterns of `${scrutineeVar.name}`: ${scrutinee.showPatternsDbg}")
        // Post-process the true branch.
        println("TRUE")
        val processedTrueBranch = postProcess(trueBranch)
        // Post-process the false branch.
        println("FALSE")
        // Get all patterns, except the current one `pat`.
        val patterns = scrutinee.patternsIterator.filter(!_.matches(pat)).toList
        println(s"found ${patterns.length} patterns to distentangle: ${patterns.iterator.map(_.showDbg).mkString(", ")}")
        val (default, cases) = patterns
          // Search each pattern in `falseBranch`. If there exists a branch for
          // the given pattern, we separate the branch body from the term. The
          // leftover term will be used in next iteration, until there is no
          // term left (i.e., `leftoverTerm` is `N`).
          .foldLeft[Opt[Term] -> Ls[(Pattern, Opt[Loc], Term)]](S(falseBranch) -> Nil) {
            // If the remaining term is not empty, we continue our search.
            case ((S(remainingTerm), cases), pattern) =>
              println(s"searching for branches of pattern ${pattern.showDbg}")
              val (leftoverTerm, extracted) = disentangleTerm(remainingTerm)(
                context, scrutineeVar, scrutinee, pattern)
              trimEmptyTerm(leftoverTerm) -> (extracted match {
                // `remainingTerm` does not have branches for `pattern`.
                case N =>
                  println(s"cannot extract pattern ${pattern.showDbg}")
                  cases
                // We extracted a term and it needs to be further post-processed.
                case terms @ S(extractedTerm) => 
                  println(s"extracted a term of pattern ${pattern.showDbg}")
                  (pattern, pattern.firstOccurrence, postProcess(extractedTerm)) :: cases
              })
            // If no terms are left, we pass on `acc` until the iteration ends.
            case (acc @ (N, _), _) => acc
          }
        println(s"found ${cases.length} case branches")
        println(s"default branch: ${default.fold("<empty>")(_.showDbg)}")
        val postProcessedDefault = default.map(postProcess)
        // Assemble a `CaseBranches`.
        val actualFalseBranch = cases.foldRight[CaseBranches](
          postProcessedDefault.fold[CaseBranches](NoCases)(Wildcard(_))
        ) { case ((pattern, loc, body), rest) =>
          Case(pattern.toCasePattern, body, rest)(refined = pattern.refined)
        }
        // Assemble the final `CaseOf`.
        top.copy(cases = fst.copy(body = processedTrueBranch, rest = actualFalseBranch)
          (refined = fst.refined))
      // We recursively process the body of `Let` bindings.
      case let @ Let(_, _, _, body) => let.copy(body = postProcess(body))
      // Otherwise, this is not a part of a normalized term.
      case other => println(s"CANNOT post-process ${other.showDbg}"); other
    }
  }(res => s"postProcess ==> ${res.showDbg}")

  private def trimEmptyTerm(term: Term): Opt[Term] = term match {
    case k @ CaseOf(_, cases) =>
      trimEmptyCaseBranches(cases).flatMap(_ match {
        case cases: Case => S(k.copy(cases = cases))
        case NoCases => N
        case Wildcard(body) => S(body)
      })
    case let @ Let(_, _, _, body) => trimEmptyTerm(body).map(t => let.copy(body = t))
    case _ => S(term)
  }

  private def trimEmptyCaseBranches(cases: CaseBranches): Opt[CaseBranches] = cases match {
    case NoCases => N
    case w @ Wildcard(body) => trimEmptyTerm(body).map(t => w.copy(body = t))
    case k @ Case(_, body, rest) =>
      (trimEmptyTerm(body), trimEmptyCaseBranches(rest)) match {
        case (N, N) => N
        case (S(body), N) => S(k.copy(body = body, rest = NoCases)(refined = k.refined))
        case (N, S(rest)) => S(rest)
        case (S(body), S(rest)) => S(k.copy(body = body, rest = rest)(refined = k.refined))
      }
  }

  /**
    * Merge two optional terms. If both are not empty we will call the other
    * `mergeTerms`.
    */
  private def mergeTerms(t1: Opt[Term], t2: Opt[Term]): Opt[Term] =
    (t1, t2) match {
      case (N, N) => N
      case (S(t1), N) => S(t1)
      case (N, S(t2)) => S(t2)
      case (S(t1), S(t2)) => S(mergeTerms(t1, t2))
    }

  /**
    * Merge two terms. In most cases, two terms cannot be merged. This function
    * replaces `Wildcard` in `t1` with `t2`.
    */
  private def mergeTerms(t1: Term, t2: Term): Term = {
    def recTerm(lhs: Term, rhs: Term): Term = lhs match {
      case lhs @ Let(_, _, _, body) => lhs.copy(body = mergeTerms(body, rhs))
      case lhs @ CaseOf(scrutinee: Var, cases) =>
        lhs.copy(cases = recCaseBranches(cases, rhs))
      case _ =>
        println("unreachable: " + rhs.describe)
        reportUnreachableCase(rhs, lhs)
    }
    def recCaseBranches(lhs: CaseBranches, rhs: Term): CaseBranches = lhs match {
      case NoCases => Wildcard(rhs).withLocOf(rhs)
      case Wildcard(body) => Wildcard(mergeTerms(body, rhs))
      case lhs @ Case(_, _, rest) =>
        lhs.copy(rest = recCaseBranches(rest, rhs))(refined = lhs.refined)
    }
    trace(s"mergeTerms <==") {
      println(s"LHS: ${t1.showDbg}")
      println(s"RHS: ${t2.showDbg}")
      recTerm(t1, t2)
    }(merged => s"mergedTerms ==> ${merged.showDbg}")
  }

  /**
    * Disentangle case branches that match `scrutinee` against `className` from `term`.
    * The `term` should be obtained from _normalization_. Because there may exists multiple
    * `CaseOf`s which contains such case branches, we merge them on the fly.
    * 
    * @param term the term to disentangle from
    * @param scrutinee the symbol of the scrutinee variable
    * @param className the class name
    * @return the remaining term and the disentangled term
    */
  private def disentangleTerm(term: Term)(implicit
      context: Context,
      scrutineeVar: Var,
      scrutinee: Scrutinee,
      pattern: Pattern
  ): (Term, Opt[Term]) = {
    def rec(term: Term): (Term, Opt[Term]) =
      term match {
        // Disentangle pattern matching
        case top @ CaseOf(Scrutinee.WithVar(otherScrutineeVar, otherScrutinee), cases) =>
          if (scrutinee === otherScrutinee) {
            println(s"found a `CaseOf` that matches on `${scrutineeVar.name}`")
            val (n, y) = disentangleMatchedCaseBranches(cases)
            (top.copy(cases = n), y)
          } else {
            println(s"found a `CaseOf` that does NOT match on ${scrutineeVar.name}")
            val (n, y) = disentangleUnmatchedCaseBranches(cases)
            (top.copy(cases = n), (if (y === NoCases) N else S(top.copy(cases = y))))
          }
        // Disentangle tests with two case branches
        case top @ CaseOf(testVar: Var, Case(Var("true"), whenTrue, Wildcard(whenFalse))) if context.isTestVar(testVar) =>
          println(s"TEST `${testVar.name}`")
          val (n1, y1) = disentangleTerm(whenTrue)
          val (n2, y2) = disentangleTerm(whenFalse)
          (
            CaseOf(testVar, Case(Var("true"), n1, Wildcard(n2))(false)),
            (y1, y2) match {
              case (N, N) => N
              case (S(t1), N) => S(CaseOf(testVar, Case(Var("true"), t1, Wildcard(n2))(false)))
              case (N, S(t2)) => S(CaseOf(testVar, Case(Var("true"), n1, Wildcard(t2))(false)))
              case (S(t1), S(t2)) => S(CaseOf(testVar, Case(Var("true"), t1, Wildcard(t2))(false)))
            }
          )
        // For let bindings, we just go deeper.
        case let @ Let(_, _, _, body) =>
          val (n, y) = rec(body)
          (let.copy(body = n), y.map(t => let.copy(body = t)))
        // Otherwise, the scrutinee does not belong to the UCS term.
        case other =>
          println(s"cannot disentangle ${other.showDbg}. STOP")
          other -> N
      }
    trace[(Term, Opt[Term])](s"disentangleTerm <== ${scrutineeVar.name}: ${pattern.showDbg}") {
      rec(term)
    }({ case (n, y) => s"disentangleTerm ==> `${n.showDbg}` and `${y.fold("<empty>")(_.showDbg)}`" })
  }

  /**
    * Helper function for `disentangleTerm`.
    */
  private def disentangleMatchedCaseBranches(cases: CaseBranches)(implicit
      context: Context,
      scrutineeVar: Var,
      scrutinee: Scrutinee,
      pattern: Pattern
  ): (CaseBranches, Opt[Term]) =
    cases match {
      case NoCases => NoCases -> N
      case wildcard @ Wildcard(body) =>
        println("found a wildcard, go deeper")
        val (n, y) = disentangleTerm(body)
        wildcard.copy(body = n) -> y
      case kase @ Case(pat, body, rest) =>
        println(s"found a case branch matching against ${pat.showDbg}")
        if (pattern.matches(pat)) {
          rest -> S(body)
        } else {
          val (n1, y1) = disentangleTerm(body)
          val (n2, y2) = disentangleMatchedCaseBranches(rest)
          (kase.copy(body = n1, rest = n2)(kase.refined), mergeTerms(y1, y2))
        }
    }

  /** Helper function for `disentangleTerm`. */
  private def disentangleUnmatchedCaseBranches(cases: CaseBranches)(implicit
      context: Context,
      scrutineeVar: Var,
      scrutinee: Scrutinee,
      pattern: Pattern
  ): (CaseBranches, CaseBranches) =
    cases match {
      case NoCases => NoCases -> NoCases
      case wildcard @ Wildcard(body) =>
        println("found a wildcard, go deeper")
        val (n, y) = disentangleTerm(body)
        (wildcard.copy(body = n), y.fold(NoCases: CaseBranches)(Wildcard(_)))
      case kase @ Case(_, body, rest) =>
        println(s"found a case branch")
        val (n1, y1) = disentangleTerm(body)
        val (n2, y2) = disentangleUnmatchedCaseBranches(rest)
        (kase.copy(body = n1, rest = n2)(kase.refined), (y1 match {
          case S(term) => kase.copy(body = term, rest = y2)(kase.refined)
          case N => y2
        }))
    }
}

object PostProcessing {
  private object typeSymbolOrdering extends Ordering[TypeSymbol] {
    override def compare(x: TypeSymbol, y: TypeSymbol): Int = {
      (x.defn.toLoc, y.defn.toLoc) match {
        case (S(xLoc), S(yLoc)) => xLoc.spanStart.compare(yLoc.spanStart)
        case (_, _) => x.defn.name.compare(y.defn.name)
      }
    }
  }
}
