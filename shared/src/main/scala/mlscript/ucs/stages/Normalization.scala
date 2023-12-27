
package mlscript.ucs.stages

import mlscript.ucs.{showVar, Context, Lines, LinesOps, VariableGenerator}
import mlscript.ucs.core._
import mlscript.ucs.helpers._
import mlscript.pretyper.Scope
import mlscript.pretyper.symbol._
import mlscript.{App, CaseOf, Fld, FldFlags, Let, Loc, Sel, Term, Tup, Var, StrLit}
import mlscript.{CaseBranches, Case, Wildcard, NoCases}
import mlscript.Message, Message.MessageContext
import mlscript.utils._, shorthands._

trait Normalization { self: mlscript.pretyper.Traceable =>
  import Normalization._

  private def concatImpl(these: Split, those: Split)(implicit context: Context, generatedVars: Set[Var]): Split =
    if (these.hasElse) these else (these match {
      case these @ Split.Cons(_, tail) => these.copy(tail = concatImpl(tail, those))
      case these @ Split.Let(_, nme, _, tail) =>
        if (those.freeVars contains nme) {
          val fresh = context.freshShadowed()
          val thoseWithShadowed = Split.Let(false, nme, fresh, those)
          val concatenated = these.copy(tail = concatImpl(tail, thoseWithShadowed))
          Split.Let(false, fresh, nme, concatenated)
        } else {
          these.copy(tail = concatImpl(tail, those)(context, generatedVars + nme))
        }
      case _: Split.Else => these
      case Split.Nil => those.withoutBindings(generatedVars)
    })
  
  private def concat(these: Split, those: Split)(implicit context: Context, generatedVars: Set[Var]): Split =
    trace(s"concat <== ${generatedVars.mkString("{", ", ", "}")}") {
      println(s"these: ${printSplit(these)}")
      println(s"those: ${printSplit(those)}")
      concatImpl(these, those)
    }(sp => s"concat => ${printSplit(sp)}")

  /**
    * Normalize core abstract syntax to MLscript syntax.
    *
    * @param split the split to normalize
    * @return the normalized term
    */ 
  @inline protected def normalize(split: Split)(implicit context: Context): Term = normalizeToTerm(split)(context, Set.empty)

  private def normalizeToTerm(split: Split)(implicit context: Context, generatedVars: Set[Var]): Term = trace("normalizeToTerm <==") {
    split match {
      case Split.Cons(Branch(scrutinee, Pattern.Name(nme), continuation), tail) =>
        println(s"alias $scrutinee => $nme")
        Let(false, nme, scrutinee, normalizeToTerm(concat(continuation, tail)))
      // Skip Boolean conditions as scrutinees, because they only appear once.
      case Split.Cons(Branch(test, pattern @ Pattern.Class(nme @ Var("true")), continuation), tail) if context.isTestVar(test) =>
        val trueBranch = normalizeToTerm(concat(continuation, tail))
        val falseBranch = normalizeToCaseBranches(tail)
        CaseOf(test, Case(nme, trueBranch, falseBranch))
      case Split.Cons(Branch(scrutinee, pattern @ Pattern.Literal(literal), continuation), tail) =>
        val trueBranch = normalizeToTerm(specialize(concat(continuation, tail), true)(scrutinee.symbol, pattern))
        val falseBranch = normalizeToCaseBranches(specialize(tail, false)(scrutinee.symbol, pattern))
        CaseOf(scrutinee, Case(literal, trueBranch, falseBranch))
      // false class parameters. Easy
      case Split.Cons(Branch(scrutinee, pattern @ Pattern.Class(nme), continuation), tail) =>
        println(s"match $scrutinee with $nme (has location: ${nme.toLoc.isDefined})")
        val trueBranch = normalizeToTerm(specialize(concat(continuation, tail), true)(scrutinee.symbol, pattern))
        val falseBranch = normalizeToCaseBranches(specialize(tail, false)(scrutinee.symbol, pattern))
        CaseOf(scrutinee, Case(nme, trueBranch, falseBranch))
      case Split.Cons(Branch(scrutinee, pattern, continuation), tail) =>
        throw new NormalizationException((msg"Unsupported pattern: ${pattern.toString}" -> pattern.toLoc) :: Nil)
      case Split.Let(rec, Var("_"), rhs, tail) => normalizeToTerm(tail)
      case Split.Let(_, nme, _, tail) if context.isScrutineeVar(nme) && generatedVars.contains(nme) =>
        normalizeToTerm(tail)
      case Split.Let(rec, nme, rhs, tail) =>
        val newDeclaredBindings = if (context.isGeneratedVar(nme)) generatedVars + nme else generatedVars
        Let(rec, nme, rhs, normalizeToTerm(tail)(context, newDeclaredBindings))
      case Split.Else(default) => default
      case Split.Nil => println("unexpected empty split"); ???
    }
  }(_ => "normalizeToTerm ==> ")

  private def normalizeToCaseBranches(split: Split)(implicit context: Context, generatedVars: Set[Var]): CaseBranches =
    trace("normalizeToCaseBranches") {
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
    }()

  // Specialize `split` with the assumption that `scrutinee` matches `pattern`.
  private def specialize
      (split: Split, matchOrNot: Bool)
      (implicit scrutinee: Symbol, pattern: Pattern): Split =
  trace[Split](s"S${if (matchOrNot) "+" else "-"} <== ${scrutinee.name} is ${pattern}") {
    (matchOrNot, split) match {
      // Name patterns are translated to let bindings.
      case (true | false, Split.Cons(Branch(otherScrutineeVar, Pattern.Name(alias), continuation), tail)) =>
        Split.Let(false, alias, otherScrutineeVar, specialize(continuation, matchOrNot))
      // Class pattern. Positive.
      case (true, split @ Split.Cons(head @ Branch(ScrutineeOnly(otherScrutinee), Pattern.Class(otherClassName), continuation), tail)) =>
        val otherClassSymbol = getClassLikeSymbol(otherClassName)
        lazy val specializedTail = {
          println(s"specialized next")
          specialize(tail, true)
        }
        if (scrutinee === otherScrutinee) {
          println(s"scrutinee: ${scrutinee.name} === ${otherScrutinee.name}")
          pattern match {
            case Pattern.Class(className) =>
              val classSymbol = getClassLikeSymbol(className)
              if (classSymbol === otherClassSymbol) {
                println(s"Case 1: class name: $className === $otherClassName")
                val specialized = specialize(continuation, true)
                if (specialized.hasElse) {
                  println("tail is discarded")
                  specialized.withDiagnostic(
                    msg"Discarded split because of else branch" -> None // TODO: Synthesize locations
                  )
                } else {
                  specialized ++ specialize(tail, true)
                }
              } else if (otherClassSymbol.baseTypes contains classSymbol) {
                println(s"Case 2: $otherClassName <: $className")
                split
              } else {
                println(s"Case 3: $className and $otherClassName are unrelated")
                specializedTail
              }
            case _ => throw new NormalizationException((msg"Incompatible: ${pattern.toString}" -> pattern.toLoc) :: Nil)
          }
        } else {
          println(s"scrutinee: ${scrutinee.name} =/= ${otherScrutinee.name}")
          split.copy(
            head = head.copy(continuation = specialize(continuation, true)),
            tail = specializedTail
          )
        }
      // Class pattern. Negative
      case (false, split @ Split.Cons(head @ Branch(ScrutineeOnly(otherScrutinee), Pattern.Class(otherClassName), continuation), tail)) =>
        val otherClassSymbol = getClassLikeSymbol(otherClassName)
        if (scrutinee === otherScrutinee) {
          println(s"scrutinee: ${scrutinee.name} === ${otherScrutinee.name}")
          pattern match {
            case Pattern.Class(className) =>
              val classSymbol = getClassLikeSymbol(className)
              if (className === otherClassName) {
                println(s"Case 1: class name: $otherClassName === $className")
                specialize(tail, false) // TODO: Subsitute parameters to otherParameters
              } else if (otherClassSymbol.baseTypes contains classSymbol) {
                println(s"Case 2: class name: $otherClassName <: $className")
                Split.Nil
              } else {
                println(s"Case 3: class name: $otherClassName and $className are unrelated")
                split.copy(tail = specialize(tail, false))
              }
            case _ => throw new NormalizationException((msg"Incompatible: ${pattern.toString}" -> pattern.toLoc) :: Nil)
          }
        } else {
          println(s"scrutinee: ${scrutinee.name} =/= ${otherScrutinee.name}")
          split.copy(
            head = head.copy(continuation = specialize(continuation, matchOrNot)),
            tail = specialize(tail, matchOrNot)
          )
        }
      // Other patterns. Not implemented.
      case (_, Split.Cons(Branch(otherScrutineeVar, pattern, continuation), tail)) =>
        throw new NormalizationException((msg"Unsupported pattern: ${pattern.toString}" -> pattern.toLoc) :: Nil)
      case (_, let @ Split.Let(_, nme, _, tail)) =>
        println(s"let binding $nme, go next")
        let.copy(tail = specialize(tail, matchOrNot))
      // Ending cases remain the same.
      case (_, end @ (Split.Else(_) | Split.Nil)) => println("the end"); end
    }
  }(showSplit(s"S${if (matchOrNot) "+" else "-"} ==>", _))

  /**
    * Print a normalized term with indentation.
    */
  @inline protected def printNormalizedTerm(term: Term): Unit =
    println(showNormalizedTerm(term))
}

object Normalization {
  private def getClassLikeSymbol(className: Var): TypeSymbol =
    className.symbolOption.flatMap(_.typeSymbolOption) match {
      case N => throw new NormalizationException(msg"class name is not resolved" -> className.toLoc :: Nil)
      case S(typeSymbol) => typeSymbol
    }

  class NormalizationException(val messages: Ls[Message -> Opt[Loc]]) extends Throwable {
    def this(message: Message, location: Opt[Loc]) = this(message -> location :: Nil)
  }

  /**
    * Convert a normalized term to a string with indentation. It makes use of
    * some special markers.
    *
    * - `*` if the variable is associated with a symbol,
    * - `†` if the variable has a location.
    */
  def showNormalizedTerm(term: Term): String = {
    def showTerm(term: Term): Lines = term match {
      case let: Let => showLet(let)
      case caseOf: CaseOf => showCaseOf(caseOf)
      case other => (0, other.toString) :: Nil
    }
    def showCaseOf(caseOf: CaseOf): Lines = {
      val CaseOf(trm, cases) = caseOf
      s"$trm match" ##: showCaseBranches(cases)
    }
    def showCaseBranches(caseBranches: CaseBranches): Lines =
      caseBranches match {
        case Case(pat, rhs, tail) =>
          // If the class name has a location, mark it with a dagger †.
          // This is to track the location information.
          val marker = if (pat.toLoc.isDefined) "†" else ""
          (s"case $pat$marker =>" @: showTerm(rhs)) ++ showCaseBranches(tail)
        case Wildcard(term) => s"case _ =>" @: showTerm(term)
        case NoCases => Nil
      }
    def showLet(let: Let): Lines = {
      val Let(rec, nme, rhs, body) = let
      (0, s"let ${showVar(nme)} = $rhs") :: showTerm(body)
    }
    showTerm(term).map { case (n, line) => "  " * n + line }.mkString("\n")
  }
}