package mlscript
package ucs

import utils._, shorthands._
import pretyper.symbol.{ClassLikeSymbol, TypeSymbol}

package object stages {
  /**
    * Split a term into two parts: the pattern and the extra test.
    * This is used to extract patterns from UCS conjunctions. For example,
    * the second line results in `IfThen(Some(xv) and xv == 0, ...)`
    * in the following case.
    * 
    * ```
    * if x is
    *   Some(xv) and xv == 0 then ...
    * ```
    * 
    * We must separate `Some(xv)` from the term to complete the pattern
    * `x is Some(xv)`.
    *
    * @param term a term which might contains a pattern and an extra test
    * @return a tuple, whose the first element is the pattern and the second
    *   element is the extra test
    */
  def separatePattern(term: Term): (Term, Opt[Term]) = term match {
    case App(and @ Var("and"), PlainTup(lhs, rhs)) => separatePattern(lhs) match {
      case (pattern, N) => (pattern, S(rhs))
      case (pattern, S(lhsRhs)) => (pattern, S(App(and, PlainTup(lhsRhs, rhs))))
    }
    case _ => (term, N)
  }

  /**
    * Hard-coded subtyping relations used in normalization and coverage checking.
    * Pass literals in `L` and pass variables together with `TypeSymbol` in `R`.
    */
  private[ucs] def compareCasePattern(
      lhs: Opt[Lit \/ TypeSymbol],
      rhs: Opt[Lit \/ TypeSymbol]
  ): Bool = (lhs, rhs) match {
    case (S(lhs), S(rhs)) => compareCasePattern(lhs, rhs)
    case (_, _) => false
  }
  /**
    * Hard-coded subtyping relations used in normalization and coverage checking.
    * Pass literals in `L` and pass variables together with `TypeSymbol` in `R`.
    */
  private[stages] def compareCasePattern(
      lhs: Lit \/ TypeSymbol,
      rhs: Lit \/ TypeSymbol
  ): Bool = (lhs, rhs) match {
    case (_, R(s)) if s.name === "Object" => true
    case (R(s1), R(s2)) if (s1.name === "true" || s1.name === "false") && s2.name === "Bool" => true
    case (R(s1), R(s2)) if s1.name === "Int" && s2.name === "Num" => true
    case (R(s1: ClassLikeSymbol), R(s2: ClassLikeSymbol)) => s1 <:< s2
    case (L(IntLit(_)), R(s)) if s.name === "Int" || s.name === "Num" => true
    case (L(StrLit(_)), R(s)) if s.name === "Str" => true
    case (L(DecLit(_)), R(s)) if s.name === "Num" => true
    case (_, _) => false
  }
}
