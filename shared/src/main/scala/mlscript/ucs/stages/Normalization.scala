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
    if (these.hasElse) {
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
      case Split.Nil => those.withoutBindings(declaredVars)
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
      trace(s"fill <== ${declaredVars.iterator.map(_.name).mkString("{", ", ", "}")}") {
        println(s"LHS: ${showSplit(these)}")
        println(s"RHS: ${showSplit(those)}")
        fillImpl(these, those)(scope, context, declaredVars, shouldReportDiscarded)
      }(sp => s"fill ==> ${showSplit(sp)}")

    def :++(tail: => Split): Split = {
      if (these.hasElse) {
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
  ): Term = trace("normalizeToTerm <==") {
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
        val trueBranch = normalizeToTerm(specialize(concatenatedTrueBranch, true)(scrutineeVar, scrutinee, pattern, context), declaredVars)
        // println(s"false branch: ${showSplit(tail)}")
        val falseBranch = normalizeToCaseBranches(specialize(tail, false)(scrutineeVar, scrutinee, pattern, context), declaredVars)
        CaseOf(scrutineeVar, Case(literal, trueBranch, falseBranch)(refined = false))
      case Split.Cons(Branch(Scrutinee.WithVar(scrutineeVar, scrutinee), pattern @ Pattern.Class(nme, _, rfd), continuation), tail) =>
        println(s"CLASS: ${scrutineeVar.name} is ${nme.name}")
        // println(s"match ${scrutineeVar.name} with $nme (has location: ${nme.toLoc.isDefined})")
        val trueBranch = normalizeToTerm(specialize(continuation.fill(tail, declaredVars, false), true)(scrutineeVar, scrutinee, pattern, context), declaredVars)
        val falseBranch = normalizeToCaseBranches(specialize(tail, false)(scrutineeVar, scrutinee, pattern, context), declaredVars)
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
        raiseDesugaringError(msg"unexpected empty split found" -> N)
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
  private def specialize
      (split: Split, matchOrNot: Bool)
      (implicit scrutineeVar: Var, scrutinee: Scrutinee, pattern: Pattern, context: Context): Split =
  trace[Split](s"S${if (matchOrNot) "+" else "-"} <== ${scrutineeVar.name} is ${pattern}") {
    (matchOrNot, split) match {
      // Name patterns are translated to let bindings.
      case (m, Split.Cons(Branch(otherScrutineeVar, Pattern.Name(alias), continuation), tail)) =>
        Split.Let(false, alias, otherScrutineeVar, specialize(continuation, m))
      case (m, Split.Cons(head @ Branch(test, Pattern.Class(Var("true"), _, _), continuation), tail)) if context.isTestVar(test) =>
        println(s"TEST: ${test.name} is true")
        head.copy(continuation = specialize(continuation, m)) :: specialize(tail, m)
      case (true, split @ Split.Cons(head @ Branch(Scrutinee.WithVar(otherScrutineeVar, otherScrutinee), otherPattern, continuation), tail)) =>
        if (scrutinee === otherScrutinee) {
          println(s"Case 1: ${scrutineeVar.name} === ${otherScrutineeVar.name}")
          if (otherPattern =:= pattern) {
            println(s"Case 1.1: $pattern =:= $otherPattern")
            otherPattern reportInconsistentRefinedWith pattern
            specialize(continuation, true) :++ specialize(tail, true)
          } else if (otherPattern <:< pattern) {
            println(s"Case 1.2: $pattern <:< $otherPattern")
            pattern.markAsRefined; split
          } else {
            println(s"Case 1.3: $pattern are unrelated with $otherPattern")
            specialize(tail, true)
          }
        } else {
          println(s"Case 2: ${scrutineeVar.name} =/= ${otherScrutineeVar.name}")
          head.copy(continuation = specialize(continuation, true)) :: specialize(tail, true)
        }
      case (false, split @ Split.Cons(head @ Branch(Scrutinee.WithVar(otherScrutineeVar, otherScrutinee), otherPattern, continuation), tail)) =>
        if (scrutinee === otherScrutinee) {
          println(s"Case 1: ${scrutineeVar.name} === ${otherScrutineeVar.name}")
          otherPattern reportInconsistentRefinedWith pattern
          if (otherPattern =:= pattern || otherPattern <:< pattern) {
            println(s"Case 1.1: $pattern =:= (or <:<) $otherPattern")
            specialize(tail, false)
          } else {
            println(s"Case 1.2: $pattern are unrelated with $otherPattern")
            split.copy(tail = specialize(tail, false))
          }
        } else {
          println(s"Case 2: ${scrutineeVar.name} =/= ${otherScrutineeVar.name}")
          head.copy(continuation = specialize(continuation, false)) :: specialize(tail, false)
        }
      case (_, split @ Split.Cons(Branch(_, pattern, _), _)) =>
        raiseDesugaringError(msg"unsupported pattern" -> pattern.toLoc)
        split
      case (m, let @ Split.Let(_, nme, _, tail)) => let.copy(tail = specialize(tail, m))
      case (_, end @ (Split.Else(_) | Split.Nil)) => println("the end"); end
    }
  }()

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
