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
    def fill(those: Split, declaredVars: Set[Var], shouldReportDiscarded: Bool)(implicit
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
    split match {
      case Split.Cons(Branch(scrutinee, Pattern.Name(nme), continuation), tail) =>
        println(s"ALIAS: ${scrutinee.name} is ${nme.name}")
        val (wrap, realTail) = preventShadowing(nme, tail)
        wrap(Let(false, nme, scrutinee, normalizeToTerm(continuation.fill(realTail, declaredVars, true), declaredVars)))
      // Skip Boolean conditions as scrutinees, because they only appear once.
      case Split.Cons(Branch(test, pattern @ Pattern.Class(nme @ Var("true"), _, _), continuation), tail) if context.isTestVar(test) =>
        println(s"TRUE: ${test.name} is true")
        val trueBranch = normalizeToTerm(continuation.fill(tail, declaredVars, false), declaredVars)
        val falseBranch = normalizeToCaseBranches(tail, declaredVars)
        CaseOf(test, Case(nme, trueBranch, falseBranch)(refined = false))
      case Split.Cons(Branch(Scrutinee.WithVar(scrutineeVar, scrutinee), pattern @ Pattern.Literal(literal), continuation), tail) =>
        println(s"LITERAL: ${scrutineeVar.name} is ${literal.idStr}")
        println(s"entire split: ${showSplit(split)}")
        val concatenatedTrueBranch = continuation.fill(tail, declaredVars, false)
        // println(s"true branch: ${showSplit(concatenatedTrueBranch)}")
        val trueBranch = normalizeToTerm(specialize(concatenatedTrueBranch, true, scrutineeVar, scrutinee, pattern), declaredVars)
        // println(s"false branch: ${showSplit(tail)}")
        val falseBranch = normalizeToCaseBranches(specialize(tail, false, scrutineeVar, scrutinee, pattern), declaredVars)
        CaseOf(scrutineeVar, Case(literal, trueBranch, falseBranch)(refined = false))
      case Split.Cons(Branch(Scrutinee.WithVar(scrutineeVar, scrutinee), pattern @ Pattern.Class(nme, _, rfd), continuation), tail) =>
        println(s"CLASS: ${scrutineeVar.name} is ${nme.name}")
        // println(s"match ${scrutineeVar.name} with $nme (has location: ${nme.toLoc.isDefined})")
        val trueBranch = normalizeToTerm(specialize(continuation.fill(tail, declaredVars, false), true, scrutineeVar, scrutinee, pattern), declaredVars)
        val falseBranch = normalizeToCaseBranches(specialize(tail, false, scrutineeVar, scrutinee, pattern), declaredVars)
        CaseOf(scrutineeVar, Case(nme, trueBranch, falseBranch)(refined = pattern.refined))
      case Split.Cons(Branch(scrutinee, pattern, continuation), tail) =>
        raiseDesugaringError(msg"unsupported pattern: ${pattern.toString}" -> pattern.toLoc)
        errorTerm
      case Split.Let(_, nme, _, tail) if context.isScrutineeVar(nme) && declaredVars.contains(nme) =>
        println(s"LET: SKIP already declared scrutinee ${nme.name}")
        normalizeToTerm(tail, declaredVars)
      case Split.Let(rec, nme, rhs, tail) if context.isGeneratedVar(nme) =>
        println(s"LET: generated ${nme.name}")
        Let(rec, nme, rhs, normalizeToTerm(tail, declaredVars + nme)(scope, context))
      case Split.Let(rec, nme, rhs, tail) =>
        println(s"LET: ${nme.name}")
        Let(rec, nme, rhs, normalizeToTerm(tail, declaredVars))
      case Split.Else(default) =>
        println(s"DFLT: ${default.showDbg}")
        default
      case Split.Nil =>
        // raiseDesugaringError(msg"unexpected empty split found" -> N)
        errorTerm
    }
  }(split => "normalizeToTerm ==> " + showNormalizedTerm(split))

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
      matchOrNot: Bool,
      scrutineeVar: Var,
      scrutinee: Scrutinee,
      pattern: Pattern
  )(implicit context: Context): Split = 
    trace(s"S${if (matchOrNot) "+" else "-"} <== ${scrutineeVar.name} is ${pattern} : ${showSplit(split, true)}"){
      val specialized = specializeImpl(split)(matchOrNot, scrutineeVar, scrutinee, pattern, context)
      // if (split =/= Split.Nil && specialized === Split.Nil && !split.isFallback) {
      //   raiseDesugaringWarning(msg"the case is unreachable" -> split.toLoc)
      // }
      specialized
    }(r => s"S${if (matchOrNot) "+" else "-"} ==> ${showSplit(r, true)}")

  /** This function does not trace. Call it when handling `tail`s. */
  private def specializeImpl(split: Split)(implicit
      keepOrRemove: Bool,
      scrutineeVar: Var,
      scrutinee: Scrutinee,
      pattern: Pattern,
      context: Context): Split =split match {
    case split @ Split.Cons(head, tail) =>
      println(s"CASE Cons ${head.showDbg}")
      lazy val continuation = specialize(head.continuation, keepOrRemove, scrutineeVar, scrutinee, pattern)
      head match {
        case Branch(otherScrutineeVar, Pattern.Name(alias), _) =>
          Split.Let(false, alias, otherScrutineeVar, continuation)
        case Branch(test, Pattern.Class(Var("true"), _, _), _) if context.isTestVar(test) =>
          head.copy(continuation = continuation) :: specializeImpl(tail)
        case Branch(Scrutinee.WithVar(otherScrutineeVar, otherScrutinee), otherPattern, _) =>
          if (scrutinee === otherScrutinee) {
            if (keepOrRemove) {
              println(s"Case 1.1: ${scrutineeVar.name} === ${otherScrutineeVar.name}")
              if (otherPattern =:= pattern) {
                println(s"Case 1.1.1: $pattern =:= $otherPattern")
                otherPattern reportInconsistentRefinedWith pattern
                continuation :++ specializeImpl(tail)
              } else if (otherPattern <:< pattern) {
                println(s"Case 1.1.2: $pattern <:< $otherPattern")
                pattern.markAsRefined; split
              } else {
                println(s"Case 1.1.3: $pattern is unrelated with $otherPattern")
                // The `continuation` is discarded because `otherPattern` is unrelated
                // to the specialization topic.
                if (!split.isFallback) {
                  println(s"report warning")
                  if (pattern <:< otherPattern) {
                    raiseDesugaringWarning(
                      msg"the pattern always matches" -> otherPattern.toLoc,
                      msg"the scrutinee was matched against ${pattern.toString}" -> pattern.toLoc,
                      msg"which is a subtype of ${otherPattern.toString}" -> (pattern match {
                        case Pattern.Class(_, symbol, _) => symbol.defn.toLoc
                        case _ => otherPattern.getLoc
                      }))
                    continuation :++ specializeImpl(tail)
                  } else {
                    raiseDesugaringWarning(
                      msg"possibly conflicted patterns" -> otherPattern.toLoc,
                      msg"the scrutinee was matched against ${pattern.toString}" -> pattern.toLoc,
                      msg"which is unrelated with ${otherPattern.toString}" -> otherPattern.toLoc)
                    specializeImpl(tail)
                  }
                } else {
                  specializeImpl(tail)
                }
              }
            } else {
              println(s"Case 1.2: ${scrutineeVar.name} === ${otherScrutineeVar.name}")
              otherPattern reportInconsistentRefinedWith pattern
              if (otherPattern =:= pattern || otherPattern <:< pattern) {
                println(s"Case 1.2.1: $pattern =:= (or <:<) $otherPattern")
                // The `continuation` is discarded because `otherPattern` is related
                // to the specialization topic.
                // println(s"is fallback = ${split.isFallback}")
                // if (!split.isFallback) {
                //   println(s"report warning")
                //   raiseDesugaringWarning(
                //     msg"possibly duplicated cases" -> otherPattern.toLoc,
                //     msg"the case can be covered by ${pattern.toString}" -> pattern.toLoc,
                //   )
                // }
                specializeImpl(tail)
              } else {
                println(s"Case 1.2.2: $pattern are unrelated with $otherPattern")
                split.copy(tail = specializeImpl(tail))
              }
            }
          } else {
            println(s"Case 2: ${scrutineeVar.name} =/= ${otherScrutineeVar.name}")
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
