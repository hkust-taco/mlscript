package mlscript.ucs

import mlscript.ucs.{Lines, LinesOps}
import mlscript.ucs.{core, syntax}
import mlscript.ucs.context.{Context}
import mlscript.pretyper.symbol.{TermSymbol, TypeSymbol}
import mlscript.{App, CaseOf, Fld, FldFlags, Let, Loc, Sel, SimpleTerm, Term, Tup, Var}
import mlscript.{CaseBranches, Case, Wildcard, NoCases}
import mlscript.utils._, shorthands._

/** All the pretty-printing stuff go here. */
package object display {

  /** If the variable has a location, mark it with an asterisk.
    * If the variable is associated with a term symbol, mark it with an asterisk.
    * If the variable is associated with a term symbol and has a scrutinee, mark it with a double dagger. */
  private def showVar(`var`: Var)(implicit context: Context): String = {
    val postfix = `var`.symbolOption match {
      case S(symbol: TermSymbol) if symbol.isScrutinee => "‡"
      case S(_: TermSymbol) => "†"
      case S(_: TypeSymbol) => "◊"
      case N => ""
    }
    `var`.name + (`var`.symbolOption.fold("")(_ => "*")) + postfix
  }

  def showSplit(split: syntax.TermSplit)(implicit context: Context): Str = {
    // TODO: tailrec
    def termSplit(split: syntax.TermSplit, isFirst: Bool, isAfterAnd: Bool): Lines = split match {
      case syntax.Split.Cons(head, tail) => (termBranch(head) match {
        case (n, line) :: tail => (n, (if (isAfterAnd) "" else "and ") + s"$line") :: tail
        case Nil => Nil
      }) ::: termSplit(tail, false, isAfterAnd)
      case syntax.Split.Let(_, nme, rhs, tail) =>
        (0, s"let ${nme.name} = ${rhs.showDbg}") :: termSplit(tail, false, isAfterAnd)
      case syntax.Split.Else(term) =>
        (if (isFirst) (0, s"then ${term.showDbg}") else (0, s"else ${term.showDbg}")) :: Nil
      case syntax.Split.Nil => Nil
    }
    def termBranch(branch: syntax.TermBranch): Lines = branch match {
      case syntax.TermBranch.Boolean(test, continuation) => 
        s"$test" #: termSplit(continuation, true, false)
      case syntax.TermBranch.Match(scrutinee, continuation) =>
        s"$scrutinee is" #: patternSplit(continuation)
      case syntax.TermBranch.Left(left, continuation) =>
        s"$left" #: operatorSplit(continuation)
    }
    def patternSplit(split: syntax.PatternSplit): Lines = split match {
      case syntax.Split.Cons(head, tail) => patternBranch(head) ::: patternSplit(tail)
      case syntax.Split.Let(rec, nme, rhs, tail) =>
        (0, s"let ${nme.name} = ${rhs.showDbg}") :: patternSplit(tail)
      case syntax.Split.Else(term) => (0, s"else ${term.showDbg}") :: Nil
      case syntax.Split.Nil => Nil
    }
    def operatorSplit(split: syntax.OperatorSplit): Lines = split match {
      case syntax.Split.Cons(head, tail) => operatorBranch(head) ::: operatorSplit(tail)
      case syntax.Split.Let(rec, nme, rhs, tail) =>
        (0, s"let ${nme.name} = ${rhs.showDbg}") :: operatorSplit(tail)
      case syntax.Split.Else(term) => (0, s"else ${term.showDbg}") :: Nil
      case syntax.Split.Nil => Nil
    }
    def operatorBranch(branch: syntax.OperatorBranch): Lines =
      s"${branch.operator}" #: (branch match {
        case syntax.OperatorBranch.Match(_, continuation) => patternSplit(continuation)
        case syntax.OperatorBranch.Binary(_, continuation) => termSplit(continuation, true, true)
      })
    def patternBranch(branch: syntax.PatternBranch): Lines = {
      val syntax.PatternBranch(pattern, continuation) = branch
      termSplit(continuation, true, false) match {
        case (0, line) :: lines => (0, s"$pattern $line") :: lines
        case lines => (0, pattern.toString) :: lines
      }
    }
    ("if" #: termSplit(split, true, true)).iterator.map { case (n, line) => "  " * n + line }.mkString("\n")
  }

  @inline def showSplit(s: core.Split)(implicit context: Context): Str = showSplit("if", s)

  def showSplit(prefix: Str, s: core.Split)(implicit context: Context): Str = {
    // TODO: tailrec
    def split(s: core.Split, isFirst: Bool, isTopLevel: Bool): Lines = s match {
      case core.Split.Cons(head, tail) => (branch(head) match {
        case (n, line) :: tail => (n, (if (isTopLevel) "" else "") + s"$line") :: tail
        case Nil => Nil
      }) ::: split(tail, false, isTopLevel)
      case core.Split.Let(_, nme, rhs, tail) =>
        (0, s"let ${showVar(nme)} = ${rhs.showDbg}") :: split(tail, false, isTopLevel)
      case core.Split.Else(term) =>
        (if (isFirst) (0, s"then ${term.showDbg}") else (0, s"else ${term.showDbg}")) :: Nil
      case core.Split.Nil => Nil
    }
    def branch(b: core.Branch): Lines = {
      val core.Branch(scrutinee, pattern, continuation) = b
      s"${showVar(scrutinee)} is $pattern" #: split(continuation, true, false)
    }
    val lines = split(s, true, true)
    (if (prefix.isEmpty) lines else prefix #: lines)
      .iterator.map { case (n, line) => "  " * n + line }.mkString("\n")
  }

  /**
    * Convert a normalized term to a string with indentation. It makes use of
    * some special markers.
    *
    * - `*` if the variable has a location.
    * - `†` if the variable is associated with a term symbol.
    * - `‡` if the variable is associated with a term symbol and has a scrutinee.
    */
  def showNormalizedTerm(term: Term)(implicit context: Context): String = {
    def showTerm(term: Term): Lines = term match {
      case let: Let => showLet(let)
      case caseOf: CaseOf => showCaseOf(caseOf)
      case other => (0, other.showDbg) :: Nil
    }
    def showScrutinee(term: Term): Str = term match {
      case vari: Var => showVar(vari)
      case _ => term.showDbg
    }
    def showPattern(pat: SimpleTerm): Str = pat match {
      case vari: Var => showVar(vari)
      case _ => pat.showDbg
    }
    def showCaseOf(caseOf: CaseOf): Lines = {
      val CaseOf(trm, cases) = caseOf
      s"case ${showScrutinee(trm)} of" ##: showCaseBranches(cases)
    }
    def showCaseBranches(caseBranches: CaseBranches): Lines =
      caseBranches match {
        case Case(pat, rhs, tail) =>
          (s"${showPattern(pat)} ->" @: showTerm(rhs)) ++ showCaseBranches(tail)
        case Wildcard(term) => s"_ ->" @: showTerm(term)
        case NoCases => Nil
      }
    def showLet(let: Let): Lines = {
      val Let(rec, nme, rhs, body) = let
      (0, s"let ${showVar(nme)} = ${rhs.showDbg}") :: showTerm(body)
    }
    showTerm(term).map { case (n, line) => "  " * n + line }.mkString("\n")
  }
}
