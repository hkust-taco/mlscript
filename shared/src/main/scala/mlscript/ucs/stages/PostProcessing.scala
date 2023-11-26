package mlscript.ucs.stages

import mlscript.{Case, CaseBranches, CaseOf, Let, Loc, NoCases, Term, Var, Wildcard}
import mlscript.pretyper.{ScrutineeSymbol, Symbol}
import mlscript.utils._, shorthands._
import mlscript.Message, Message.MessageContext
import mlscript.pretyper.shortName
import scala.annotation.tailrec

trait PostProcessing { self: mlscript.pretyper.Traceable =>
  import PostProcessing._

  def postProcess(term: Term): Term = trace(s"postProcess <== ${shortName(term)}") {
    // Normalized terms are constructed using `Let` and `CaseOf`.
    term match {
      case top @ CaseOf(scrutinee: Var, fst @ Case(className: Var, body, NoCases)) =>
        println(s"found a UNARY case: $scrutinee is $className")
        println("post-processing the body")
        top.copy(cases = fst.copy(body = postProcess(body)))
      case top @ CaseOf(scrutinee: Var, fst @ Case(className: Var, trueBranch, Wildcard(falseBranch))) =>
        println(s"found a BINARY case: $scrutinee is $className")
        val scrutineeSymbol = scrutinee.symbol match {
          case symbol: ScrutineeSymbol => symbol
          case _ => throw new PostProcessingException(
            msg"variable ${scrutinee.name} is not a scrutinee" -> N :: Nil
          )
        }
        println(s"`${scrutinee}`'s matched classes: ${scrutineeSymbol.matchedClasses.iterator.map(_.name).mkString("[", ", ", "]")}")
        // Post-process the first branch body.
        println("post-processing the first branch")
        val processedTrueBranch = postProcess(trueBranch)
        // Post-process the false branch.
        val (default, cases) = scrutineeSymbol.matchedClasses.iterator.filter(_ =/= className)
          // For each case class name, distangle case branch body terms from the false branch.
          .foldLeft[Opt[Term] -> Ls[Var -> Term]](S(falseBranch) -> Nil) {
            case ((S(remainingTerm), cases), className) =>
              val (leftoverTerm, extracted) = disentangle(remainingTerm, scrutineeSymbol, className)
              avoidEmptyCaseOf(leftoverTerm) -> (extracted match {
                case N =>
                  println(s"no extracted term about $className")
                  cases
                case terms @ S(extractedTerm) => 
                  println(s"extracted a term about $className")
                  className -> postProcess(extractedTerm) :: cases
              })
            // TODO: Consider either make the first tuple element as non-optional.
            // TODO: Then, write a new helper function which checks if the term is an empty `CaseOf`.
            case ((N, cases), _) => (N, cases) 
          }
        println(s"found ${cases.length} cases")
        // Assemble a `CaseBranches`.
        val actualFalseBranch = cases.foldRight[CaseBranches](
          default.fold[CaseBranches](NoCases)(Wildcard(_))
        ) { case (className -> body, rest) => Case(className, body, rest) }
        // Assemble the final `CaseOf`.
        top.copy(cases = fst.copy(body = processedTrueBranch, rest = actualFalseBranch))
      // We recursively process the body of as`Let` bindings.
      case let @ Let(_, _, _, body) => let.copy(body = postProcess(body))
      // Otherwise, this is not a part of a normalized term.
      case other => println(s"CANNOT post-process"); other
    }
  }(_ => "postProcess ==> ")

  private def avoidEmptyCaseOf(term: Term): Opt[Term] = term match {
    case CaseOf(_, NoCases) => println(s"$term is empty"); N
    case CaseOf(_, cases: Case) =>
      @tailrec
      def containsNoWildcard(cases: CaseBranches): Bool = cases match {
        case NoCases => true
        case Wildcard(_) => false
        case Case(_, body, rest) =>
          avoidEmptyCaseOf(body) === N && containsNoWildcard(rest)
      }
      if (containsNoWildcard(cases)) S(term) else N
    case _ => S(term)
  }

  private def mergeTerms(t1: Term, t2: Term): Term =
    trace(s"mergeTerms <== ${t1.describe} ${t2.describe}") {
      t1 match {
        case t1 @ Let(_, _, _, body) => t1.copy(body = mergeTerms(body, t2))
        case t1 @ CaseOf(scrutinee: Var, cases) =>
          t1.copy(cases = mergeTermIntoCaseBranches(t2, cases))
        case _ => println("CANNOT merge. Discard t2."); t1
      }
    }()

  private def mergeTermIntoCaseBranches(term: Term, cases: CaseBranches): CaseBranches =
    trace(s"mergeTermIntoCaseBranches <== ${term.describe} ${cases}") {
      cases match {
        case NoCases => Wildcard(term).withLocOf(term)
        case Wildcard(body) => Wildcard(mergeTerms(body, term))
        case cases @ Case(_, _, rest) => cases.copy(rest = mergeTermIntoCaseBranches(term, rest))
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
  def disentangle(term: Term, scrutinee: ScrutineeSymbol, className: Var): (Term, Opt[Term]) =
    trace[(Term, Opt[Term])](s"disentangle <== ${scrutinee.name}: $className") {
      term match {
        case top @ CaseOf(scrutineeVar: Var, cases) =>
          if (scrutineeVar.symbol match {
            case s: ScrutineeSymbol => s === scrutinee; case _ => false
          }) {
            println(s"found a `CaseOf` that matches on ${scrutinee.name}")
            def rec(cases: CaseBranches): (CaseBranches, Opt[Term]) = cases match {
              case NoCases => println("found the end, stop"); NoCases -> N
              case wildcard @ Wildcard(body) =>
                println("found a wildcard, stop")
                val (y, n) = disentangle(body, scrutinee, className)
                wildcard.copy(body = y) -> n
              case kase @ Case(`className`, body, rest) =>
                println(s"found a case branch matching against $className")
                val (y, n) = rec(rest)
                y -> S(n.fold(body)(mergeTerms(_, body)))
              case kase @ Case(otherClassName, body, rest) =>
                val (y, n) = rec(rest)
                kase.copy(rest = y) -> n
            }
            val (y, n) = rec(cases)
            top.copy(cases = y) -> n
          } else {
            println(s"found a `CaseOf` that does NOT match on ${scrutinee.name}")
            def rec(cases: CaseBranches): (CaseBranches, CaseBranches) = cases match {
              case NoCases =>
                println("found the end, stop")
                NoCases -> NoCases
              case wildcard @ Wildcard(body) =>
                println("found a wildcard, stop")
                val (y, n) = disentangle(body, scrutinee, className)
                wildcard.copy(body = y) -> n.fold(NoCases: CaseBranches)(Wildcard(_))
              case kase @ Case(_, body, rest) =>
                println(s"found a case branch")
                val (y1, n1) = disentangle(body, scrutinee, className)
                val (y2, n2) = rec(rest)
                kase.copy(body = y1, rest = y2) -> (n1 match {
                  case S(term) => kase.copy(body = term, rest = n2)
                  case N => n2
                })
            }
            val (y, n) = rec(cases)
            top.copy(cases = y) -> (if (n === NoCases) N else S(top.copy(cases = n)))
          }
        case let @ Let(_, _, _, body) =>
          val (y, n) = disentangle(body, scrutinee, className)
          let.copy(body = y) -> n.map(t => let.copy(body = t))
        case other => println(s"CANNOT disentangle"); other -> N
      }
    }({ case (y, n) => s"disentangle ==> `${shortName(y)}` and `${n.fold("_")(shortName)}`" })

  def cascadeConsecutiveCaseOf(term: Term): Term = trace(s"cascade consecutive CaseOf <== ${term.describe}") {
    // Normalized terms are constructed using `Let` and `CaseOf`.
    term match {
      case top @ CaseOf(scrutinee: Var, fst @ Case(pattern, body, NoCases)) =>
        println(s"found a UNARY case: $scrutinee is $pattern")
        top.copy(cases = fst.copy(body = cascadeConsecutiveCaseOf(body)))
      case top @ CaseOf(scrutinee: Var, fst @ Case(pattern, trueBranch, snd @ Wildcard(falseBranch))) =>
        println(s"found a BINARY case: $scrutinee is $pattern")
        println("cascading the true branch")
        val processedTrueBranch = cascadeConsecutiveCaseOf(trueBranch)
        println("cascading the false branch")
        val processedFalseBranch = cascadeConsecutiveCaseOf(falseBranch)
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
      case let @ Let(_, _, _, body) => let.copy(body = cascadeConsecutiveCaseOf(body))
      // Otherwise, this is not a part of a normalized term.
      case other => println(s"CANNOT cascade"); other
    }
  }()
}

object PostProcessing {
  class PostProcessingException(val messages: Ls[Message -> Opt[Loc]]) extends Throwable {
    def this(message: Message, location: Opt[Loc]) = this(message -> location :: Nil)
  }
}
