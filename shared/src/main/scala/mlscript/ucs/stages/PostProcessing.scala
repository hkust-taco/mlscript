package mlscript.ucs.stages

import mlscript.{Case, CaseBranches, CaseOf, Let, Loc, NoCases, Term, Var, Wildcard}
import mlscript.ucs.Context
import mlscript.pretyper.symbol._
import mlscript.utils._, shorthands._
import mlscript.Message, Message.MessageContext
import scala.annotation.tailrec

trait PostProcessing { self: mlscript.pretyper.Traceable =>
  import PostProcessing._

  /**
    * If the given `Var` represents a class name, get its `ClassSymbol`.
    *
    * @param className the class name variable
    */
  def getClassSymbolFromVar(className: Var): TypeSymbol =
    trace(s"getClassSymbolFromVar <== ${inspect.shallow(className)}") {
      className.symbolOption match {
        case S(symbol: ClassSymbol) => symbol
        case S(symbol: TraitSymbol) => symbol
        case S(symbol: ModuleSymbol) => symbol
        case S(symbol: Symbol) => throw new PostProcessingException(
          msg"variable ${className.name} is not associated with a class symbol" -> N :: Nil)
        case N => throw new PostProcessingException(
          msg"variable ${className.name} is not associated with any symbols" -> N :: Nil)
      }
    }(symbol => s"getClassSymbolFromVar ==> ${symbol.name}")

  def postProcess(term: Term)(implicit context: Context): Term = trace(s"postProcess <== ${inspect.shallow(term)}") {
    // Normalized terms are constructed using `Let` and `CaseOf`.
    term match {
      case top @ CaseOf(scrutinee: Var, fst @ Case(className: Var, body, NoCases)) =>
        println(s"found a UNARY case: $scrutinee is $className")
        println("post-processing the body")
        top.copy(cases = fst.copy(body = postProcess(body)))
      case top @ CaseOf(test: Var, fst @ Case(Var("true"), trueBranch, Wildcard(falseBranch))) if context.isTestVar(test) =>
        println(s"found a if-then-else case: $test is true")
        val processedTrueBranch = postProcess(trueBranch)
        val processedFalseBranch = postProcess(falseBranch)
        top.copy(cases = fst.copy(body = processedTrueBranch, rest = Wildcard(processedFalseBranch)))
      case top @ CaseOf(scrutinee: Var, fst @ Case(className: Var, trueBranch, Wildcard(falseBranch))) =>
        println(s"found a BINARY case: $scrutinee is $className")
        val scrutineeSymbol = scrutinee.symbol match {
          case symbol: ScrutineeSymbol => symbol
          case _ => throw new PostProcessingException(
            msg"variable ${scrutinee.name} is not a scrutinee" -> N :: Nil
          )
        }
        val classSymbol = getClassSymbolFromVar(className)
        println(s"`${scrutinee}`'s matched classes: ${scrutineeSymbol.matchedClasses.keysIterator.map(_.name).mkString("[", ", ", "]")}")
        // Post-process the true branch.
        println("post-processing the first branch")
        val processedTrueBranch = postProcess(trueBranch)
        // Post-process the false branch.
        println("post-processing the false branch")
        println(s"searching for cases: " + scrutineeSymbol.matchedClasses.keysIterator.filter(_ =/= classSymbol).map(_.name).mkString("[", ", ", "]"))
        val (default, cases) = scrutineeSymbol.matchedClasses.iterator.filter(_._1 =/= classSymbol)
          // For each case class name, distangle case branch body terms from the false branch.
          .foldLeft[Opt[Term] -> Ls[(TypeSymbol, Opt[Loc], Term)]](S(falseBranch) -> Nil) {
            case ((S(remainingTerm), cases), (classSymbol -> locations)) =>
              println(s"searching for case: ${classSymbol.name}")
              val (leftoverTerm, extracted) = disentangle(remainingTerm, scrutineeSymbol, classSymbol)
              trimEmptyTerm(leftoverTerm) -> (extracted match {
                case N =>
                  println(s"no extracted term about ${classSymbol.name}")
                  cases
                case terms @ S(extractedTerm) => 
                  println(s"extracted a term about ${classSymbol.name}")
                  (classSymbol, locations.headOption, postProcess(extractedTerm)) :: cases
              })
            case ((N, cases), _) => (N, cases) 
          }
        println(s"found ${cases.length} case branches")
        val postProcessedDefault = default.map(postProcess)
        // Assemble a `CaseBranches`.
        val actualFalseBranch = cases.foldRight[CaseBranches](
          postProcessedDefault.fold[CaseBranches](NoCases)(Wildcard(_))
        ) { case ((classSymbol, loc, body), rest) =>
          // TODO: Why not just keep the class name?
          val className = Var(classSymbol.name).withLoc(loc).withSymbol(classSymbol)
          Case(className, body, rest)
        }
        // Assemble the final `CaseOf`.
        top.copy(cases = fst.copy(body = processedTrueBranch, rest = actualFalseBranch))
      // We recursively process the body of as`Let` bindings.
      case let @ Let(_, _, _, body) => let.copy(body = postProcess(body))
      // Otherwise, this is not a part of a normalized term.
      case other => println(s"CANNOT post-process"); other
    }
  }(_ => "postProcess ==> ")

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
        case (S(body), N) => S(k.copy(body = body, rest = NoCases))
        case (N, S(rest)) => S(rest)
        case (S(body), S(rest)) => S(k.copy(body = body, rest = rest))
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
    trace(s"mergeTerms <== ${inspect.shallow(t1)} ${inspect.shallow(t2)}") {
      t1 match {
        case t1 @ Let(_, _, _, body) => t1.copy(body = mergeTerms(body, t2))
        case t1 @ CaseOf(scrutinee: Var, cases) =>
          t1.copy(cases = mergeTermIntoCaseBranches(t2, cases))
        case _ =>
          println(s"CANNOT merge. Discard ${inspect.shallow(t2)}.")
          t1
      }
    }(merged => s"mergedTerms ==> ${inspect.shallow(merged)}")

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
  def disentangle(term: Term, scrutinee: ScrutineeSymbol, classSymbol: TypeSymbol): (Term, Opt[Term]) =
    trace[(Term, Opt[Term])](s"disentangle <== ${scrutinee.name}: ${classSymbol.name}") {
      term match {
        case top @ CaseOf(scrutineeVar: Var, cases) =>
          if (scrutineeVar.symbol match {
            case s: ScrutineeSymbol => s === scrutinee; case _ => false
          }) {
            println(s"found a `CaseOf` that matches on `${scrutinee.name}`")
            def rec(cases: CaseBranches): (CaseBranches, Opt[Term]) = cases match {
              case NoCases =>
                println("no cases, STOP")
                NoCases -> N
              case wildcard @ Wildcard(body) =>
                println("found a wildcard, go deeper")
                val (n, y) = disentangle(body, scrutinee, classSymbol)
                wildcard.copy(body = n) -> y
              case kase @ Case(className: Var, body, rest) =>
                println(s"found a case branch matching against $className")
                val otherClassSymbol = getClassSymbolFromVar(className)
                if (otherClassSymbol === classSymbol) {
                  rest -> S(body)
                } else {
                  val (n1, y1) = disentangle(body, scrutinee, classSymbol)
                  val (n2, y2) = rec(rest)
                  (kase.copy(body = n1, rest = n2), mergeTerms(y1, y2))
                }
              case kase @ Case(otherClassName, body, rest) =>
                println(s"found another case branch matching against $otherClassName")
                val (n, y) = rec(rest)
                kase.copy(rest = n) -> y
            }
            val (n, y) = rec(cases)
            (top.copy(cases = n), y)
          } else {
            println(s"found a `CaseOf` that does NOT match on ${scrutinee.name}")
            def rec(cases: CaseBranches): (CaseBranches, CaseBranches) = cases match {
              case NoCases =>
                println("no cases, STOP")
                NoCases -> NoCases
              case wildcard @ Wildcard(body) =>
                println("found a wildcard, go deeper")
                val (n, y) = disentangle(body, scrutinee, classSymbol)
                (wildcard.copy(body = n), y.fold(NoCases: CaseBranches)(Wildcard(_)))
              case kase @ Case(_, body, rest) =>
                println(s"found a case branch")
                val (n1, y1) = disentangle(body, scrutinee, classSymbol)
                val (n2, y2) = rec(rest)
                (kase.copy(body = n1, rest = n2), (y1 match {
                  case S(term) => kase.copy(body = term, rest = y2)
                  case N => y2
                }))
            }
            val (n, y) = rec(cases)
            (top.copy(cases = n), (if (y === NoCases) N else S(top.copy(cases = y))))
          }
        case let @ Let(_, _, _, body) =>
          val (n, y) = disentangle(body, scrutinee, classSymbol)
          (let.copy(body = n), y.map(t => let.copy(body = t)))
        case other =>
          println(s"cannot disentangle ${inspect.shallow(other)}. STOP")
          other -> N
      }
    }({ case (n, y) => s"disentangle ==> `${inspect.deep(n)}` and `${y.fold("<empty>")(inspect.deep(_))}`" })

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
