package mlscript
package ucs
package stages

import mlscript.utils._, shorthands._, Message.MessageContext
import context.{Context, Scrutinee}
import display.{showNormalizedTerm, showSplit}
import syntax.core.{Pattern, Branch, Split}
import pretyper.symbol._
import pretyper.{Diagnosable, Scope, Traceable}

trait Normalization { self: Desugarer with Traceable =>
  import Normalization._

  private def fillImpl(these: Split, those: Split)(implicit
      scope: Scope,
      context: Context,
      declaredVars: Set[Var],
      shouldReportDiscarded: Bool
  ): Split =
    if (these.isFull) {
      reportUnreachableCase(those, these, onlyIf = those =/= Split.Nil && shouldReportDiscarded)
    } else (these match {
      case these @ Split.Cons(head, tail) =>
        these.copy(tail = fillImpl(tail, those))
      case these @ Split.Let(_, nme, _, tail) =>
        println(s"fill let binding ${nme.name}")
        if (scope.getTermSymbol(nme.name).isDefined && (those.freeVars contains nme)) {
          val fresh = context.freshShadowed()
          val thoseWithShadowed = Split.Let(false, nme, fresh, those)
          val concatenated = these.copy(tail = fillImpl(tail, thoseWithShadowed))
          Split.Let(false, fresh, nme, concatenated)
        } else {
          these.copy(tail = fillImpl(tail, those)(scope, context, declaredVars + nme, false))
        }
      case _: Split.Else => these
      case Split.Nil => those.withoutBindings(declaredVars).markAsFallback()
    })

  private implicit class SplitOps(these: Split) {
    /**
      * Fill the split into the previous split. 
      *
      * @param those the split to append
      * @param shouldReportDiscarded whether we should raise an error if the given
      *                        split is discarded because of the else branch
      * @param declaredVars the generated variables which have been declared
      * @return the concatenated split
      */
    def fill(
        those: Split,
        declaredVars: Set[Var],
        shouldReportDiscarded: Bool,
    )(implicit
        scope: Scope,
        context: Context,
    ): Split =
      trace(s"fill <== vars = ${declaredVars.iterator.map(_.name).mkString("{", ", ", "}")}") {
        println(s"LHS: ${showSplit(these)}")
        println(s"RHS: ${showSplit(those)}")
        fillImpl(these, those)(scope, context, declaredVars, shouldReportDiscarded)
      }(sp => s"fill ==> ${showSplit(sp)}")

    def :++(tail: => Split): Split = {
      if (these.isFull) {
        println("tail is discarded")
        // raiseDesugaringWarning(msg"Discarded split because of else branch" -> these.toLoc)
        these
      } else {
        these ++ tail
      }
    }
  }

  /** We don't care about `Pattern.Name` because they won't appear in `specialize`. */
  private implicit class PatternOps(val self: Pattern) extends AnyRef {
    /** Checks if two patterns are the same. */
    def =:=(other: Pattern): Bool = (self, other) match {
      case (Pattern.Class(_, s1, _), Pattern.Class(_, s2, _)) => s1 === s2
      case (Pattern.Literal(l1), Pattern.Literal(l2)) => l1 === l2
      case (_, _) => false
    }
    /** Checks if `self` can be subsumed under `other`. */
    def <:<(other: Pattern): Bool = {
      def mk(pattern: Pattern): Opt[Lit \/ TypeSymbol] = pattern match {
        case Pattern.Class(_, s, _) => S(R(s))
        case Pattern.Literal(l) => S(L(l))
        case _ => N
      }
      compareCasePattern(mk(self), mk(other))
    }
    /**
      * If two class-like patterns has different `refined` flag. Report the
      * inconsistency as a warning.
      */
    def reportInconsistentRefinedWith(other: Pattern): Unit = (self, other) match {
      case (Pattern.Class(n1, _, r1), Pattern.Class(n2, _, r2)) if r1 =/= r2 =>
        def be(value: Bool): Str = if (value) "is" else "is not"
        raiseDesugaringWarning(
          msg"inconsistent refined pattern" -> other.toLoc,
          msg"pattern `${n1.name}` ${be(r1)} refined" -> n1.toLoc,
          msg"but pattern `${n2.name}` ${be(r2)} refined" -> n2.toLoc
        )
      case (_, _) => ()
    }
    /** If the pattern is a class-like pattern, override its `refined` flag. */
    def markAsRefined: Unit = self match {
      case self: Pattern.Class => self.refined = true
      case _ => ()
    }
  }
  

  /**
    * Normalize core abstract syntax to MLscript syntax.
    *
    * @param split the split to normalize
    * @return the normalized term
    */ 
  @inline protected def normalize(split: Split)(implicit
      scope: Scope,
      context: Context
  ): Term = normalizeToTerm(split, Set.empty)(scope, context)

  private def errorTerm: Term = Var("error")

  private def normalizeToTerm(split: Split, declaredVars: Set[Var])(implicit
      scope: Scope,
      context: Context,
  ): Term = trace(s"normalizeToTerm <== ${showSplit(split)}") {
    normalizeToTermImpl(split, declaredVars)
  }(split => "normalizeToTerm ==> " + showNormalizedTerm(split))

  private def normalizeToTermImpl(split: Split, declaredVars: Set[Var])(implicit
      scope: Scope,
      context: Context,
  ): Term =
    split match {
      case Split.Cons(head, tail) =>
        head match {
          case Branch(scrutinee, Pattern.Name(nme), _) =>
            println(s"ALIAS: ${scrutinee.name} is ${nme.name}")
            val (wrap, realTail) = preventShadowing(nme, tail)
            val continuation = head.continuation.fill(realTail, declaredVars, true)
            wrap(Let(false, nme, scrutinee, normalizeToTermImpl(continuation, declaredVars)))
          // Skip Boolean conditions as scrutinees, because they only appear once.
          case Branch(test, pattern @ Pattern.Class(nme @ Var("true"), _, _), _) if context.isTestVar(test) =>
            println(s"TRUE: ${test.name} is true")
            val continuation = head.continuation.fill(tail, declaredVars, false)
            val whenTrue = normalizeToTerm(continuation, declaredVars)
            val whenFalse = normalizeToCaseBranches(tail, declaredVars)
            CaseOf(test, Case(nme, whenTrue, whenFalse)(refined = false))
          case Branch(Scrutinee.WithVar(scrutineeVar, scrutinee), pattern @ (Pattern.Literal(_) | Pattern.Class(_, _, _)), _) =>
            println(s"CONS: ${scrutineeVar.name} is $pattern")
            val continuation = head.continuation.fill(tail, declaredVars, false)
            val whenTrue = normalizeToTerm(specialize(continuation, +, scrutineeVar, scrutinee, pattern), declaredVars)
            val whenFalse = normalizeToCaseBranches(specialize(tail, `-`(head.continuation.isFull), scrutineeVar, scrutinee, pattern).clearFallback(), declaredVars)
            CaseOf(scrutineeVar, Case(pattern.toSimpleTerm, whenTrue, whenFalse)(refined = pattern.refined))
          case Branch(scrutinee, pattern, _) =>
            raiseDesugaringError(msg"unsupported pattern matching: ${scrutinee.name} is ${pattern.toString}" -> pattern.toLoc)
            errorTerm
        }
      case Split.Let(_, nme, _, tail) if context.isScrutineeVar(nme) && declaredVars.contains(nme) =>
        println(s"LET: SKIP already declared scrutinee ${nme.name}")
        normalizeToTermImpl(tail, declaredVars)
      case Split.Let(rec, nme, rhs, tail) if context.isGeneratedVar(nme) =>
        println(s"LET: generated ${nme.name}")
        Let(rec, nme, rhs, normalizeToTermImpl(tail, declaredVars + nme)(scope, context))
      case Split.Let(rec, nme, rhs, tail) =>
        println(s"LET: ${nme.name}")
        Let(rec, nme, rhs, normalizeToTermImpl(tail, declaredVars))
      case Split.Else(default) =>
        println(s"DFLT: ${default.showDbg}")
        default
      case Split.Nil =>
        // raiseDesugaringError(msg"unexpected empty split found" -> N)
        errorTerm
    }

  private def normalizeToCaseBranches(split: Split, declaredVars: Set[Var])(implicit
      scope: Scope,
      context: Context,
  ): CaseBranches =
    trace(s"normalizeToCaseBranches <==") {
      split match {
        // case Split.Cons(head, Split.Nil) => Case(head.pattern, normalizeToTerm(head.continuation), NoCases)
        case other: Split.Cons => Wildcard(normalizeToTerm(other, declaredVars))
        case Split.Let(_, nme, _, tail) if context.isScrutineeVar(nme) && declaredVars.contains(nme) =>
          normalizeToCaseBranches(tail, declaredVars)
        case Split.Let(rec, nme, rhs, tail) =>
          val newDeclaredVars = if (context.isGeneratedVar(nme)) declaredVars + nme else declaredVars
          normalizeToCaseBranches(tail, newDeclaredVars)(scope, context) match {
            case NoCases => Wildcard(rhs)
            case Wildcard(term) => Wildcard(Let(rec, nme, rhs, term))
            case _: Case => die
          }
        case Split.Else(default) => Wildcard(default)
        case Split.Nil => NoCases
      }
    }(r => "normalizeToCaseBranches ==>")

  /**
    * Specialize `split` with the assumption that `scrutinee` matches `pattern`.
    * If `matchOrNot` is `true`, the function _keeps_ branches that agree on
    * `scrutinee` matches `pattern`. Otherwise, the function _removes_ branches
    * that agree on `scrutinee` matches `pattern`.
    */
  private def specialize(
      split: Split,
      mode: Mode,
      scrutineeVar: Var,
      scrutinee: Scrutinee,
      pattern: Pattern
  )(implicit context: Context): Split = 
    trace(s"S$mode <== ${scrutineeVar.name} is ${pattern} : ${showSplit(split, true)}"){
      val specialized = specializeImpl(split)(mode, scrutineeVar, scrutinee, pattern, context)
      // if (split =/= Split.Nil && specialized === Split.Nil && !split.isFallback) {
      //   raiseDesugaringWarning(msg"the case is unreachable" -> split.toLoc)
      // }
      specialized
    }(r => s"S$mode ==> ${showSplit(r, true)}")

  /**
   * This function does not trace. Call it when handling `tail`s, so we can get
   * flattened debug logs.
   * @param keepOrRemove `N` if S+ or `S(...)` if S-. If we don't need to track
   *                     duplication information, this parameter can be denoted
   *                     by just a Boolean variable.
   */
  private def specializeImpl(split: Split)(implicit
      mode: Mode,
      scrutineeVar: Var,
      scrutinee: Scrutinee,
      pattern: Pattern,
      context: Context): Split = split match {
    case split @ Split.Cons(head, tail) =>
      println(s"CASE Cons ${head.showDbg}")
      lazy val continuation = specialize(head.continuation, mode, scrutineeVar, scrutinee, pattern)
      head match {
        case Branch(thatScrutineeVar, Pattern.Name(alias), _) =>
          Split.Let(false, alias, thatScrutineeVar, continuation)
        case Branch(test, Pattern.Class(Var("true"), _, _), _) if context.isTestVar(test) =>
          head.copy(continuation = continuation) :: specializeImpl(tail)
        case Branch(Scrutinee.WithVar(thatScrutineeVar, thatScrutinee), thatPattern, _) =>
          if (scrutinee === thatScrutinee) mode match {
            case + =>
              println(s"Case 1.1: ${scrutineeVar.name} === ${thatScrutineeVar.name}")
              if (thatPattern =:= pattern) {
                println(s"Case 1.1.1: $pattern =:= $thatPattern")
                thatPattern reportInconsistentRefinedWith pattern
                continuation :++ specializeImpl(tail)
              } else if (thatPattern <:< pattern) {
                println(s"Case 1.1.2: $pattern <:< $thatPattern")
                pattern.markAsRefined; split
              } else {
                println(s"Case 1.1.3: $pattern is unrelated with $thatPattern")
                // The `continuation` is discarded because `thatPattern` is unrelated
                // to the specialization topic.
                if (!split.isFallback) {
                  println(s"report warning")
                  if (pattern <:< thatPattern) {
                    raiseDesugaringWarning(
                      msg"the pattern always matches" -> thatPattern.toLoc,
                      msg"the scrutinee was matched against ${pattern.toString}" -> pattern.toLoc,
                      msg"which is a subtype of ${thatPattern.toString}" -> (pattern match {
                        case Pattern.Class(_, symbol, _) => symbol.defn.toLoc
                        case _ => thatPattern.getLoc
                      }))
                    continuation :++ specializeImpl(tail)
                  } else {
                    raiseDesugaringWarning(
                      msg"possibly conflicting patterns for this scrutinee" -> scrutineeVar.toLoc,
                      msg"the scrutinee was matched against ${pattern.toString}" -> pattern.toLoc,
                      msg"which is unrelated with ${thatPattern.toString}" -> thatPattern.toLoc)
                    specializeImpl(tail)
                  }
                } else {
                  specializeImpl(tail)
                }
              }
            case -(full) =>
              println(s"Case 1.2: ${scrutineeVar.name} === ${thatScrutineeVar.name}")
              thatPattern reportInconsistentRefinedWith pattern
              val samePattern = thatPattern =:= pattern
              if (samePattern || thatPattern <:< pattern) {
                println(s"Case 1.2.1: $pattern =:= (or <:<) $thatPattern")
                // The `continuation` is discarded because `thatPattern` is related
                // to the specialization topic.
                println(s"`${thatScrutineeVar.name} is ${thatPattern}` is${if (split.isFallback) " " else " not "}fallback")
                println(s"already removed = $full")
                if (!split.isFallback && full && !head.continuation.isEmpty) {
                  println(s"report warning")
                  if (pattern === thatPattern) {
                    raiseDesugaringWarning(
                      msg"found a duplicated case" -> thatPattern.toLoc,
                      msg"there is an identical pattern ${pattern.toString}" -> pattern.toLoc,
                    )
                  } else {
                    raiseDesugaringWarning(
                      msg"found a duplicated case" -> thatPattern.toLoc,
                      msg"the case is covered by pattern ${pattern.toString}" -> pattern.toLoc,
                      msg"due to the subtyping relation" -> (thatPattern match {
                        case Pattern.Class(_, symbol, _) => symbol.defn.getLoc
                        case _ => thatPattern.toLoc
                      })
                    )
                  }
                }
                specializeImpl(tail)(
                  `-`(if (samePattern) continuation.isFull else full),
                  scrutineeVar, scrutinee, pattern, context)
              } else {
                println(s"Case 1.2.2: $pattern are unrelated to $thatPattern")
                split.copy(tail = specializeImpl(tail))
              }
          } else {
            println(s"Case 2: ${scrutineeVar.name} =/= ${thatScrutineeVar.name}")
            head.copy(continuation = continuation) :: specializeImpl(tail)
          }
        case _ =>
          raiseDesugaringError(msg"unsupported pattern" -> pattern.toLoc)
          split
      }
    case split @ Split.Let(_, nme, _, tail) =>
      println(s"CASE Let ${nme.name}")
      split.copy(tail = specializeImpl(tail))
    case Split.Else(_) => println("CASE Else"); split
    case Split.Nil => println("CASE Nil"); split
  }

  /**
    * If you want to prepend `tail` to another `Split` where the `nme` takes
    * effects, you should use this function to prevent shadowing.
    */
  private def preventShadowing(nme: Var, tail: Split)(implicit
      scope: Scope,
      context: Context
  ): (Term => Term, Split) = scope.getTermSymbol(nme.name) match {
    case S(symbol) if tail.freeVars contains nme =>
      val stashVar = context.freshShadowed()
      ((body: Term) => Let(false, stashVar, nme, body)) ->
        Split.Let(false, nme, stashVar, tail)
    case S(_) | N => identity[Term] _ -> tail
  }
}

object Normalization {
  /** Specialization mode */
  sealed abstract class Mode
  final case object + extends Mode {
    override def toString(): String = "+"
  }
  final case class -(full: Bool) extends Mode {
    override def toString(): String = s"-($full)"
  }
}
