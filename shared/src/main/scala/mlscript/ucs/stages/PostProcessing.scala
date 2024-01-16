package mlscript.ucs.stages

import mlscript.{Case, CaseBranches, CaseOf, Let, Lit, Loc, NoCases, Term, Var, Wildcard}
import mlscript.ucs.Desugarer
import mlscript.ucs.context.{Context, PatternInfo, Scrutinee}
import mlscript.pretyper.symbol._
import mlscript.utils._, shorthands._
import mlscript.Message, Message.MessageContext
import scala.annotation.tailrec

trait PostProcessing { self: Desugarer with mlscript.pretyper.Traceable =>
  import PostProcessing._

  def postProcess(term: Term)(implicit context: Context): Term = trace(s"postProcess <== ${term.showDbg}") {
    // Normalized terms are constructed using `Let` and `CaseOf`.
    term match {
      case top @ CaseOf(Scrutinee(_), Wildcard(body)) => body
      case top @ CaseOf(Scrutinee.WithVar(scrutinee, scrutineeVar), fst @ Case(className: Var, body, NoCases)) =>
        println(s"UNARY: ${scrutineeVar.name} is ${className.name}")
        top.copy(cases = fst.copy(body = postProcess(body))(refined = fst.refined))
      case top @ CaseOf(Scrutinee.WithVar(scrutinee, scrutineeVar), fst @ Case(pat, trueBranch, Wildcard(falseBranch))) =>
        println(s"BINARY: ${scrutineeVar.name} is ${pat.showDbg}")
        println(s"patterns of `${scrutineeVar.name}`: ${scrutinee.showPatternsDbg}")
        // Post-process the true branch.
        println("TRUE")
        val processedTrueBranch = postProcess(trueBranch)
        // Post-process the false branch.
        println("FALSE")
        // Get all patterns, except the current one `pat`.
        val patternInfoList = scrutinee.patternsIterator.filter(!_.matches(pat)).toList
        println(s"found ${patternInfoList.length} patterns to distentangle: ${patternInfoList.iterator.map(_.showDbg).mkString(", ")}")
        val (default, cases) = patternInfoList
          // For each case class name, distangle case branch body terms from the false branch.
          .foldLeft[Opt[Term] -> Ls[(PatternInfo, Opt[Loc], Term)]](S(falseBranch) -> Nil) {
            case ((S(remainingTerm), cases), pattern) =>
              println(s"searching for case: ${pattern.showDbg}")
              val (leftoverTerm, extracted) = disentangleTerm(remainingTerm)(
                context, scrutineeVar, scrutinee, pattern)
              trimEmptyTerm(leftoverTerm) -> (extracted match {
                case N =>
                  println(s"no extracted term about ${pattern.showDbg}")
                  cases
                case terms @ S(extractedTerm) => 
                  println(s"extracted a term about ${pattern.showDbg}")
                  (pattern, pattern.firstOccurrence, postProcess(extractedTerm)) :: cases
              })
            case ((N, cases), _) => (N, cases)
          }
        println(s"found ${cases.length} case branches")
        val postProcessedDefault = default.map(postProcess)
        // Assemble a `CaseBranches`.
        val actualFalseBranch = cases.foldRight[CaseBranches](
          postProcessedDefault.fold[CaseBranches](NoCases)(Wildcard(_))
        ) { case ((pattern, loc, body), rest) =>
          Case(pattern.toCasePattern, body, rest)(refined = false/*FIXME?*/)
        }
        // Assemble the final `CaseOf`.
        top.copy(cases = fst.copy(body = processedTrueBranch, rest = actualFalseBranch)
          (refined = fst.refined))
      // We recursively process the body of as`Let` bindings.
      case let @ Let(_, _, _, body) => let.copy(body = postProcess(body))
      // Otherwise, this is not a part of a normalized term.
      case other => println(s"CANNOT post-process ${other.showDbg}"); other
    }
  }(res => s"postProcess ==> ${res.showDbg}")

  private def trimEmptyTerm(term: Term): Opt[Term] = term match {
    case k @ CaseOf(_, cases) => trimEmptyCaseBranches(cases).map(c => k.copy(cases = c))
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

  private def mergeTerms(t1: Opt[Term], t2: Opt[Term]): Opt[Term] =
    (t1, t2) match {
      case (N, N) => N
      case (S(t1), N) => S(t1)
      case (N, S(t2)) => S(t2)
      case (S(t1), S(t2)) => S(mergeTerms(t1, t2))
    }

  private def mergeTerms(t1: Term, t2: Term): Term =
    trace(s"mergeTerms <== ${t1.showDbg} ${t2.showDbg}") {
      t1 match {
        case t1 @ Let(_, _, _, body) => t1.copy(body = mergeTerms(body, t2))
        case t1 @ CaseOf(scrutinee: Var, cases) =>
          t1.copy(cases = mergeTermIntoCaseBranches(t2, cases))
        case _ =>
          println(s"CANNOT merge. Discard ${t2.showDbg}.")
          t1
      }
    }(merged => s"mergedTerms ==> ${merged.showDbg}")

  private def mergeTermIntoCaseBranches(term: Term, cases: CaseBranches): CaseBranches =
    trace(s"mergeTermIntoCaseBranches <== ${term.describe} ${cases}") {
      cases match {
        case NoCases => Wildcard(term).withLocOf(term)
        case Wildcard(body) => Wildcard(mergeTerms(body, term))
        case cases @ Case(_, _, rest) =>
          cases.copy(rest = mergeTermIntoCaseBranches(term, rest))(refined = cases.refined)
      }
    }()

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
      pattern: PatternInfo
  ): (Term, Opt[Term]) = {
    def rec(term: Term): (Term, Opt[Term]) =
      term match {
        case top @ CaseOf(Scrutinee.WithVar(otherScrutinee, otherScrutineeVar), cases) =>
          if (scrutinee === otherScrutinee) {
            println(s"found a `CaseOf` that matches on `${scrutineeVar.name}`")
            val (n, y) = disentangleMatchedCaseBranches(cases)
            (top.copy(cases = n), y)
          } else {
            println(s"found a `CaseOf` that does NOT match on ${scrutineeVar.name}")
            val (n, y) = disentangleUnmatchedCaseBranches(cases)
            (top.copy(cases = n), (if (y === NoCases) N else S(top.copy(cases = y))))
          }
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

  /** Helper function for `disentangleTerm`. */
  private def disentangleMatchedCaseBranches(cases: CaseBranches)(implicit
      context: Context,
      scrutineeVar: Var,
      scrutinee: Scrutinee,
      pattern: PatternInfo
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
      // case kase @ Case(otherClassName, body, rest) =>
      //   println(s"found another case branch matching against $otherClassName")
      //   val (n, y) = disentangleMatchedCaseBranches(rest)
      //   kase.copy(rest = n) -> y
    }


  /** Helper function for `disentangleTerm`. */
  private def disentangleUnmatchedCaseBranches(cases: CaseBranches)(implicit
      context: Context,
      scrutineeVar: Var,
      scrutinee: Scrutinee,
      pattern: PatternInfo
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
  class PostProcessingException(val messages: Ls[Message -> Opt[Loc]]) extends Throwable {
    def this(message: Message, location: Opt[Loc]) = this(message -> location :: Nil)
  }

  private object typeSymbolOrdering extends Ordering[TypeSymbol] {
    override def compare(x: TypeSymbol, y: TypeSymbol): Int = {
      (x.defn.toLoc, y.defn.toLoc) match {
        case (S(xLoc), S(yLoc)) => xLoc.spanStart.compare(yLoc.spanStart)
        case (_, _) => x.defn.name.compare(y.defn.name)
      }
    }
  }
}
