package mlscript
package ucs

import syntax.{core => c, source => s}
import context.{Context}
import pretyper.symbol.{TermSymbol, TypeSymbol}
import utils._, shorthands._

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

  def showSplit(split: s.TermSplit)(implicit context: Context): Str = {
    def termSplit(split: s.TermSplit, isFirst: Bool, isAfterAnd: Bool): Lines = split match {
      case s.Split.Cons(head, tail) => (termBranch(head) match {
        case (n, line) :: tail => (n, (if (isAfterAnd) "" else "and ") + s"$line") :: tail
        case Nil => Nil
      }) ::: termSplit(tail, false, isAfterAnd)
      case s.Split.Let(_, nme, rhs, tail) =>
        (0, s"let ${nme.name} = ${rhs.showDbg}") :: termSplit(tail, false, isAfterAnd)
      case s.Split.Else(term) =>
        (if (isFirst) (0, s"then ${term.showDbg}") else (0, s"else ${term.showDbg}")) :: Nil
      case s.Split.Nil => Nil
    }
    def termBranch(branch: s.TermBranch): Lines = branch match {
      case s.TermBranch.Boolean(test, continuation) => 
        s"${test.showDbg}" #: termSplit(continuation, true, false)
      case s.TermBranch.Match(scrutinee, continuation) =>
        s"${scrutinee.showDbg} is" #: patternSplit(continuation)
      case s.TermBranch.Left(left, continuation) =>
        s"${left.showDbg}" #: operatorSplit(continuation)
    }
    def patternSplit(split: s.PatternSplit): Lines = split match {
      case s.Split.Cons(head, tail) => patternBranch(head) ::: patternSplit(tail)
      case s.Split.Let(rec, nme, rhs, tail) =>
        (0, s"let ${nme.name} = ${rhs.showDbg}") :: patternSplit(tail)
      case s.Split.Else(term) => (0, s"else ${term.showDbg}") :: Nil
      case s.Split.Nil => Nil
    }
    def operatorSplit(split: s.OperatorSplit): Lines = split match {
      case s.Split.Cons(head, tail) => operatorBranch(head) ::: operatorSplit(tail)
      case s.Split.Let(rec, nme, rhs, tail) =>
        (0, s"let ${nme.name} = ${rhs.showDbg}") :: operatorSplit(tail)
      case s.Split.Else(term) => (0, s"else ${term.showDbg}") :: Nil
      case s.Split.Nil => Nil
    }
    def operatorBranch(branch: s.OperatorBranch): Lines =
      s"${branch.operator.name}" #: (branch match {
        case s.OperatorBranch.Match(_, continuation) => patternSplit(continuation)
        case s.OperatorBranch.Binary(_, continuation) => termSplit(continuation, true, true)
      })
    def patternBranch(branch: s.PatternBranch): Lines = {
      val s.PatternBranch(pattern, continuation) = branch
      termSplit(continuation, true, false) match {
        case (0, line) :: lines => (0, s"$pattern $line") :: lines
        case lines => (0, pattern.toString) :: lines
      }
    }
    ("if" #: termSplit(split, true, true)).toIndentedString
  }

  @inline def showSplit(s: c.Split, showFirstLevel: Bool = false)(implicit context: Context): Str =
    showSplit("if", s, showFirstLevel)

  def showSplit(prefix: Str, s: c.Split, showFirstLevel: Bool)(implicit context: Context): Str = {
    def split(s: c.Split, isFirst: Bool, isTopLevel: Bool): Lines = s match {
      case c.Split.Cons(head, tail) => (branch(head, isTopLevel) match {
        case (n, line) :: tail => (n, (if (isTopLevel) "" else "and ") + (if (s.isFallback) "?" else "") + line) :: tail
        case Nil => Nil
      }) ::: split(tail, false, isTopLevel)
      case c.Split.Let(_, nme, rhs, tail) =>
        (0, s"let ${showVar(nme)} = ${rhs.showDbg}") :: split(tail, false, isTopLevel)
      case c.Split.Else(term) =>
        (if (isFirst) (0, s"then ${term.showDbg}") else (0, s"else ${term.showDbg}")) :: Nil
      case c.Split.Nil => Nil
    }
    def branch(b: c.Branch, isTopLevel: Bool): Lines = {
      val c.Branch(scrutinee, pattern, continuation) = b
      if (showFirstLevel) {
        val continuation = b.continuation match {
          case c.Split.Nil => "empty"
          case c.Split.Else(_) => "then ..."
          case _ => "and ..."
        }
        (0, s"${showVar(scrutinee)} is $pattern " + continuation) :: Nil
      }
      else s"${showVar(scrutinee)} is $pattern" #: split(continuation, true, isTopLevel)
    }
    val lines = split(s, true, true)
    (if (prefix.isEmpty) lines else prefix #: lines).toIndentedString
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
    def showTerm(term: Term): Lines = term.desugaredTerm match {
      case N => term match {
        case let: Let => showLet(let)
        case caseOf: CaseOf => showCaseOf(caseOf)
        case other => (0, other.showDbg) :: Nil
      }
      case S(desugaredTerm) => "[desugared]" @: showTerm(desugaredTerm)
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
        case k @ Case(pat, rhs, tail) =>
          (s"${if (k.refined) "refined " else ""}${showPattern(pat)} ->" @: showTerm(rhs)) ++ showCaseBranches(tail)
        case Wildcard(term) => s"_ ->" @: showTerm(term)
        case NoCases => Nil
      }
    def showLet(let: Let): Lines = {
      val Let(rec, nme, rhs, body) = let
      (0, s"let ${showVar(nme)} = ${rhs.showDbg}") :: showTerm(body)
    }
    showTerm(term).toIndentedString
  }
}
