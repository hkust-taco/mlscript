package mlscript.ucs

import scala.collection.mutable.{Set => MutSet}

import mlscript._
import mlscript.utils.shorthands._

object helpers {
  def mkMonuple(t: Term): Tup = Tup(N -> Fld(false, false, t) :: Nil)

  def mkBinOp(lhs: Term, op: Var, rhs: Term): Term =
    App(App(op, mkMonuple(lhs)), mkMonuple(rhs))

  // Split a term joined by `and` into a list of terms.
  // E.g. x and y and z => x, y, z
  def splitAnd(t: Term): Ls[Term] =
    t match {
      case App(
        App(Var("and"),
            Tup((_ -> Fld(_, _, lhs)) :: Nil)),
        Tup((_ -> Fld(_, _, rhs)) :: Nil)
      ) =>
        splitAnd(lhs) :+ rhs
      case _ => t :: Nil
    }

  
  def separatePattern(term: Term): (Term, Opt[Term]) =
    term match {
      case App(
        App(and @ Var("and"),
            Tup((_ -> Fld(_, _, lhs)) :: Nil)),
        Tup((_ -> Fld(_, _, rhs)) :: Nil)
      ) =>
        separatePattern(lhs) match {
          case (pattern, N) => (pattern, S(rhs))
          case (pattern, S(lshRhs)) => (pattern, S(mkBinOp(lshRhs, and, rhs)))
        }
      case _ => (term, N)
    }

  def mkBindings(bindings: Ls[(Bool, Var, Term)], body: Term): Term = {
    val generated = MutSet.empty[(Bool, Var, Term)]
    def rec(bindings: Ls[(Bool, Var, Term)]): Term =
      bindings match {
        case Nil => body
        case (head @ (isRec, nameVar, value)) :: tail =>
          if (generated.contains(head)) {
            rec(tail)
          } else {
            generated += head
            Let(isRec, nameVar, value, rec(tail))
          }
      }
    rec(bindings)
  }

  def mkLetFromFields(scrutinee: Scrutinee, fields: Ls[Str -> Var], body: Term): Term = {
    def rec(fields: Ls[Str -> Var]): Term =
      fields match {
        case Nil => body
        case (field -> (aliasVar @ Var(alias))) :: tail =>
          Let(false, aliasVar, Sel(scrutinee.reference, Var(field)).desugaredFrom(scrutinee.term), rec(tail))
      }
    rec(fields)
  }
}

/**
  * Classes with multiple `Loc`s should derive from this.
  * The utilities below keep record of the original locations.
  * TODO: Rename this class.
  */
abstract class WithLocations(val terms: Set[(Term, Loc)])