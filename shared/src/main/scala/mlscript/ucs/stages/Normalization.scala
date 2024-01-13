
package mlscript.ucs.stages

import mlscript.ucs.{DesugarUCS, Lines, LinesOps, VariableGenerator}
import mlscript.ucs.context.{Context, ScrutineeData}
import mlscript.ucs.core._
import mlscript.ucs.display.{showNormalizedTerm, showSplit}
import mlscript.ucs.helpers._
import mlscript.pretyper.Scope
import mlscript.pretyper.symbol._
import mlscript.{App, CaseOf, Fld, FldFlags, Let, Loc, Sel, Term, Tup, Var, StrLit}
import mlscript.{CaseBranches, Case, Wildcard, NoCases}
import mlscript.Message, Message.MessageContext
import mlscript.utils._, shorthands._
import mlscript.pretyper.Traceable

trait Normalization { self: DesugarUCS with Traceable =>
  import Normalization._

  // TODO: We might not need the case where `deep` is `false`.
  private def fillImpl(these: Split, those: Split, deep: Bool)(implicit context: Context, generatedVars: Set[Var]): Split =
    if (these.hasElse) these else (these match {
      case these @ Split.Cons(head, tail) =>
        if (head.continuation.hasElse || !deep) {
          these.copy(tail = fillImpl(tail, those, deep))
        } else {
          // println(s"found a branch without default ${showSplit(head.continuation)}")
          val newHead = head.copy(continuation = fillImpl(head.continuation, those, deep))
          these.copy(head = newHead, tail = fillImpl(tail, those, deep))
        }
      case these @ Split.Let(_, nme, _, tail) =>
        if (those.freeVars contains nme) {
          val fresh = context.freshShadowed()
          val thoseWithShadowed = Split.Let(false, nme, fresh, those)
          val concatenated = these.copy(tail = fillImpl(tail, thoseWithShadowed, deep))
          Split.Let(false, fresh, nme, concatenated)
        } else {
          these.copy(tail = fillImpl(tail, those, deep)(context, generatedVars + nme))
        }
      case _: Split.Else => these
      case Split.Nil =>
        // println(s"END, generated vars: ${generatedVars.iterator.map(_.name).mkString(", ")}")
        those.withoutBindings(generatedVars)
    })

  private implicit class SplitOps(these: Split) {
    def fill(those: Split, deep: Bool)(implicit context: Context, generatedVars: Set[Var]): Split =
      trace(s"fill <== ${generatedVars.iterator.map(_.name).mkString("{", ", ", "}")}") {
        println(s"LHS: ${showSplit(these)}")
        println(s"RHS: ${showSplit(those)}")
        fillImpl(these, those, deep)
      }(sp => s"fill ==> ${showSplit(sp)}")

    def :++(tail: => Split): Split = {
      if (these.hasElse) {
        println("tail is discarded")
        // raiseWarning(msg"Discarded split because of else branch" -> these.toLoc)
        these
      } else {
        these ++ tail
      }
    }
  }
  

  /**
    * Normalize core abstract syntax to MLscript syntax.
    *
    * @param split the split to normalize
    * @return the normalized term
    */ 
  @inline protected def normalize(split: Split)(implicit context: Context): Term = normalizeToTerm(split)(context, Set.empty)

  private def errorTerm: Term = Var("error")

  private def normalizeToTerm(split: Split)(implicit context: Context, generatedVars: Set[Var]): Term = trace("normalizeToTerm <==") {
    split match {
      case Split.Cons(Branch(scrutinee, Pattern.Name(nme), continuation), tail) =>
        println(s"normalizing name pattern ${scrutinee.name} is ${nme.name}")
        Let(false, nme, scrutinee, normalizeToTerm(continuation.fill(tail, deep = false)))
      // Skip Boolean conditions as scrutinees, because they only appear once.
      case Split.Cons(Branch(test, pattern @ Pattern.Class(nme @ Var("true"), _), continuation), tail) =>
        println(s"normalizing true pattern: ${test.name} is true")
        val trueBranch = normalizeToTerm(continuation.fill(tail, deep = false))
        val falseBranch = normalizeToCaseBranches(tail)
        CaseOf(test, Case(nme, trueBranch, falseBranch)(refined = false))
      case Split.Cons(Branch(ScrutineeData.WithVar(scrutinee, scrutineeVar), pattern @ Pattern.Literal(literal), continuation), tail) =>
        println(s"normalizing literal pattern: ${scrutineeVar.name} is ${literal.idStr}")
        println(s"entire split: ${showSplit(split)}")
        val concatenatedTrueBranch = continuation.fill(tail, deep = false)
        // println(s"true branch: ${showSplit(concatenatedTrueBranch)}")
        val trueBranch = normalizeToTerm(specialize(concatenatedTrueBranch, true)(scrutineeVar, scrutinee, pattern, context))
        // println(s"false branch: ${showSplit(tail)}")
        val falseBranch = normalizeToCaseBranches(specialize(tail, false)(scrutineeVar, scrutinee, pattern, context))
        CaseOf(scrutineeVar, Case(literal, trueBranch, falseBranch)(refined = false))
      case Split.Cons(Branch(ScrutineeData.WithVar(scrutinee, scrutineeVar), pattern @ Pattern.Class(nme, rfd), continuation), tail) =>
        println(s"normalizing class pattern: ${scrutineeVar.name} is ${nme.name}")
        // println(s"match ${scrutineeVar.name} with $nme (has location: ${nme.toLoc.isDefined})")
        val trueBranch = normalizeToTerm(specialize(continuation.fill(tail, deep = false), true)(scrutineeVar, scrutinee, pattern, context))
        val falseBranch = normalizeToCaseBranches(specialize(tail, false)(scrutineeVar, scrutinee, pattern, context))
        CaseOf(scrutineeVar, Case(nme, trueBranch, falseBranch)(refined = pattern.refined))
      case Split.Cons(Branch(scrutinee, pattern, continuation), tail) =>
        raiseError(msg"Unsupported pattern: ${pattern.toString}" -> pattern.toLoc)
        errorTerm
      case Split.Let(rec, Var("_"), rhs, tail) => normalizeToTerm(tail)
      case Split.Let(_, nme, _, tail) if context.isScrutineeVar(nme) && generatedVars.contains(nme) =>
        println(s"normalizing let binding of generated variable: ${nme.name}")
        normalizeToTerm(tail)
      case Split.Let(rec, nme, rhs, tail) =>
        println(s"normalizing let binding ${nme.name}")
        val newDeclaredBindings = if (context.isGeneratedVar(nme)) generatedVars + nme else generatedVars
        Let(rec, nme, rhs, normalizeToTerm(tail)(context, newDeclaredBindings))
      case Split.Else(default) =>
        println(s"normalizing default: ${default.showDbg}")
        default
      case Split.Nil =>
        raiseError(msg"Found unexpected empty split" -> N)
        errorTerm
    }
  }(split => "normalizeToTerm ==> " + showNormalizedTerm(split))

  private def normalizeToCaseBranches(split: Split)(implicit context: Context, generatedVars: Set[Var]): CaseBranches =
    trace(s"normalizeToCaseBranches <==") {
      split match {
        // case Split.Cons(head, Split.Nil) => Case(head.pattern, normalizeToTerm(head.continuation), NoCases)
        case other: Split.Cons => Wildcard(normalizeToTerm(other))
        case Split.Let(rec, Var("_"), rhs, tail) => normalizeToCaseBranches(tail)
        case Split.Let(_, nme, _, tail) if context.isScrutineeVar(nme) && generatedVars.contains(nme) =>
          normalizeToCaseBranches(tail)
        case Split.Let(rec, nme, rhs, tail) =>
          val newDeclaredBindings = if (context.isGeneratedVar(nme)) generatedVars + nme else generatedVars
          normalizeToCaseBranches(tail)(context, newDeclaredBindings) match {
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
    * If `matchOrNot` is `true`, the function keeps branches that agree on
    * `scrutinee` matches `pattern`. Otherwise, the function removes branches
    * that agree on `scrutinee` matches `pattern`.
    */
  private def specialize
      (split: Split, matchOrNot: Bool)
      (implicit scrutineeVar: Var, scrutinee: ScrutineeData, pattern: Pattern, context: Context): Split =
  trace[Split](s"S${if (matchOrNot) "+" else "-"} <== ${scrutineeVar.name} is ${pattern}") {
    (matchOrNot, split) match {
      // Name patterns are translated to let bindings.
      case (_, Split.Cons(Branch(otherScrutineeVar, Pattern.Name(alias), continuation), tail)) =>
        Split.Let(false, alias, otherScrutineeVar, specialize(continuation, matchOrNot))
      case (_, split @ Split.Cons(head @ Branch(test, Pattern.Class(Var("true"), _), continuation), tail)) if context.isTestVar(test) =>
        println(s"found a Boolean test: ${test.showDbg} is true")
        val trueBranch = specialize(continuation, matchOrNot)
        val falseBranch = specialize(tail, matchOrNot)
        split.copy(head = head.copy(continuation = trueBranch), tail = falseBranch)
      // Class pattern. Positive.
      case (true, split @ Split.Cons(head @ Branch(ScrutineeData.WithVar(otherScrutinee, otherScrutineeVar), Pattern.Class(otherClassName, otherRefined), continuation), tail)) =>
        val otherClassSymbol = otherClassName.getClassLikeSymbol
        if (scrutinee === otherScrutinee) {
          println(s"scrutinee: ${scrutineeVar.name} === ${otherScrutineeVar.name}")
          pattern match {
            case classPattern @ Pattern.Class(className, refined) =>
              val classSymbol = className.getClassLikeSymbol
              if (classSymbol === otherClassSymbol) {
                println(s"Case 1: class name: ${className.name} === ${otherClassName.name}")
                if (otherRefined =/= refined) {
                  def be(value: Bool): Str = if (value) "is" else "is not"
                  raiseWarning(
                    msg"inconsistent refined case branches" -> pattern.toLoc,
                    msg"class pattern ${className.name} ${be(refined)} refined" -> className.toLoc,
                    msg"but class pattern ${otherClassName.name} ${be(otherRefined)} refined" -> otherClassName.toLoc
                  )
                }
                specialize(continuation, true) :++ specialize(tail, true)
              } else if (otherClassSymbol hasSuperType classSymbol) {
                println(s"Case 2: ${otherClassName.name} <: ${className.name}")
                println(s"${otherClassSymbol.name} is refining ${className.name}")
                // We should mark `pattern` as refined.
                classPattern.refined = true
                split
              } else {
                println(s"Case 3: ${className.name} and ${otherClassName.name} are unrelated")
                specialize(tail, true)
              }
            case _ =>
              // TODO: Make a case for this. Check if this is a valid case.
              raiseError(
                msg"pattern ${pattern.toString}" -> pattern.toLoc,
                msg"is incompatible with class pattern ${otherClassName.name}" -> otherClassName.toLoc,
              )
              split
          }
        } else {
          // println(s"scrutinee: ${scrutineeVar.name} =/= ${otherScrutineeVar.name}")
          split.copy(
            head = head.copy(continuation = specialize(continuation, true)),
            tail = specialize(tail, true)
          )
        }
      // Class pattern. Negative
      case (false, split @ Split.Cons(head @ Branch(ScrutineeData.WithVar(otherScrutinee, otherScrutineeVar), Pattern.Class(otherClassName, otherRefined), continuation), tail)) =>
        val otherClassSymbol = otherClassName.getClassLikeSymbol
        if (scrutinee === otherScrutinee) {
          println(s"scrutinee: ${scrutineeVar.name} === ${otherScrutineeVar.name}")
          pattern match {
            case Pattern.Class(className, refined) =>
              println("both of them are class patterns")
              if (otherRefined =/= refined) {
                def be(value: Bool): Str = if (value) "is" else "is not"
                raiseWarning(
                  msg"inconsistent refined case branches" -> pattern.toLoc,
                  msg"class pattern ${className.name} ${be(refined)} refined" -> className.toLoc,
                  msg"but class pattern ${otherClassName.name} ${be(otherRefined)} refined" -> otherClassName.toLoc
                )
              }
              val classSymbol = className.getClassLikeSymbol
              if (className === otherClassName) {
                println(s"Case 1: class name: ${otherClassName.name} === ${className.name}")
                specialize(tail, false)
              } else if (otherClassSymbol.baseTypes contains classSymbol) {
                println(s"Case 2: class name: ${otherClassName.name} <: ${className.name}")
                Split.Nil
              } else {
                println(s"Case 3: class name: ${otherClassName.name} and ${className.name} are unrelated")
                split.copy(tail = specialize(tail, false))
              }
            case _ =>
              println(s"different patterns: ${otherClassName.name} and $pattern.toString")
              split.copy(tail = specialize(tail, false))
          }
        } else {
          println(s"scrutinee: ${scrutineeVar.name} =/= ${otherScrutineeVar.name}")
          split.copy(
            head = head.copy(continuation = specialize(continuation, matchOrNot)),
            tail = specialize(tail, matchOrNot)
          )
        }
      // Literal pattern. Positive.
      case (true, split @ Split.Cons(head @ Branch(ScrutineeData.WithVar(otherScrutinee, otherScrutineeVar), Pattern.Literal(otherLiteral), continuation), tail)) =>
        if (scrutinee === otherScrutinee) {
          println(s"scrutinee: ${scrutineeVar.name} is ${otherScrutineeVar.name}")
          pattern match {
            case Pattern.Literal(literal) if literal === otherLiteral =>
              specialize(continuation, true) :++ specialize(tail, true)
            case _ => specialize(tail, true)
          }
        } else {
          println(s"scrutinee: ${scrutineeVar.name} is NOT ${otherScrutineeVar.name}")
          split.copy(
            head = head.copy(continuation = specialize(continuation, true)),
            tail = specialize(tail, true)
          )
        }
      // Literal pattern. Negative.
      case (false, split @ Split.Cons(head @ Branch(ScrutineeData.WithVar(otherScrutinee, otherScrutineeVar), Pattern.Literal(otherLiteral), continuation), tail)) =>
        if (scrutinee === otherScrutinee) {
          println(s"scrutinee: ${scrutineeVar.name} is ${otherScrutineeVar.name}")
          pattern match {
            case Pattern.Literal(literal) if literal === otherLiteral =>
              specialize(tail, false)
            case _ =>
              // No need to check `continuation` because literals don't overlap.
              split.copy(tail = specialize(tail, false))
          }
        } else {
          println(s"scrutinee: ${scrutineeVar.name} is NOT ${otherScrutineeVar.name}")
          split.copy(
            head = head.copy(continuation = specialize(continuation, false)),
            tail = specialize(tail, false)
          )
        }
      // Other patterns. Not implemented.
      case (_, split @ Split.Cons(Branch(otherScrutineeVar, pattern, continuation), tail)) =>
        raiseError(msg"found unsupported pattern: ${pattern.toString}" -> pattern.toLoc)
        split
      case (_, let @ Split.Let(_, nme, _, tail)) =>
        println(s"let binding ${nme.name}, go next")
        let.copy(tail = specialize(tail, matchOrNot))
      // Ending cases remain the same.
      case (_, end @ (Split.Else(_) | Split.Nil)) => println("the end"); end
    }
  }()
  // }(showSplit(s"S${if (matchOrNot) "+" else "-"} ==>", _))
}

object Normalization
