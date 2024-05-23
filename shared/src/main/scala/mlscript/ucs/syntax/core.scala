package mlscript
package ucs
package syntax

import collection.mutable.{Set => MutSet}
import utils._, shorthands._, pretyper.symbol.ClassLikeSymbol, context.Scrutinee

package object core {
  sealed abstract class Pattern extends Located {
    def refined: Bool
    def toSimpleTerm: SimpleTerm = this match {
      case Pattern.Literal(literal) => literal
      case Pattern.Class(nme, _, _) => nme
      case Pattern.Name(_) => die
    }
    def declaredVars: Iterator[Var] = this match {
      case _: Pattern.Literal | _: Pattern.Class => Iterator.empty
      case Pattern.Name(nme) => Iterator.single(nme)
    }
    override def toString(): String = this match {
      case Pattern.Literal(literal) => literal.idStr
      case Pattern.Name(Var(name)) => name
      case Pattern.Class(Var(name), _, rfd) => (if (rfd) "refined " else "") + name
    }
  }
  object Pattern {
    final case class Literal(literal: Lit) extends Pattern {
      override def refined: Bool = false
      override def children: Ls[Located] = literal :: Nil
    }
    final case class Name(nme: Var) extends Pattern {
      override def refined: Bool = false
      override def children: Ls[Located] = nme :: Nil
    }
    /**
      * @param nme the name of the class-like symbol
      * @param originallyRefined whether the class is marked as refined from
      *                          in source AST
      */
    final case class Class(nme: Var, symbol: ClassLikeSymbol, originallyRefined: Bool) extends Pattern {
      override def children: Ls[Located] = nme :: Nil

      /**
        * A mutable field to override the refinement status of the class. 
        * During normalization, if a case can be further refined in its
        * descendants branches, we should mark it as `refined`. See relevant
        * tests in `Normalization.mls`.
        */
      var refined: Bool = originallyRefined
    }
  }

  final case class Branch(scrutinee: Var, pattern: Pattern, continuation: Split) extends Located {
    override def children: List[Located] = scrutinee :: pattern :: continuation :: Nil

    def showDbg: String = s"${scrutinee.showDbg} is $pattern"
  }

  sealed abstract class Split extends Located {
    @inline def ::(head: Branch): Split = {
      val res = Split.Cons(head, this)
      // res.withFallbackOf(head.continuation)
      if (head.continuation.isFallback) res.markAsFallback() else res
    }
    
    /**
      * Returns true if the split has an else branch.
      */
    lazy val isFull: Bool = this match {
      case Split.Cons(_, tail) => tail.isFull
      case Split.Let(_, _, _, tail) => tail.isFull
      case Split.Else(_) => true
      case Split.Nil => false
    }

    lazy val isEmpty: Bool = this match {
      case Split.Let(_, _, _, tail) => tail.isEmpty
      case Split.Else(_) | Split.Cons(_, _) => false
      case Split.Nil => true
    }

    override lazy val freeVars: Set[Var] = this match {
      case Split.Cons(Branch(scrutinee, pattern, continuation), tail) =>
        continuation.freeVars ++ tail.freeVars
      case Split.Let(true, nme, rhs, tail) => tail.freeVars ++ rhs.freeVars - nme
      case Split.Let(false, nme, rhs, tail) => tail.freeVars - nme ++ rhs.freeVars
      case Split.Else(term) => term.freeVars
      case Split.Nil => Set.empty
    }

    /**
      * Remove duplicated bindings.
      */
    def withoutBindings(vars: Set[Var]): Split = this match {
      case self @ Split.Cons(head @ Branch(_, _, continuation), tail) =>
        self.copy(head.copy(continuation = continuation.withoutBindings(vars)), tail.withoutBindings(vars))
      case self @ Split.Let(_, name, _, tail) if vars contains name => tail.withoutBindings(vars)
      case self @ Split.Let(_, _, _, tail) => self.copy(tail = tail.withoutBindings(vars))
      case Split.Else(_) | Split.Nil => this
    }

    final override def children: Ls[Located] = this match {
      case Split.Cons(head, tail) => head :: tail :: Nil
      case Split.Let(rec, name, term, tail) => name :: term :: tail :: Nil
      case Split.Else(default) => default :: Nil
      case Split.Nil => Nil
    }

    // TODO: Make the following flag temporary. It is only meaningful in a
    // single run of specialization. The flag is useless outside specialization
    // functions.

    /**
     * The split is concatenated as a fallback when specializing the given
     * scrutinee and pattern.
     */

    private var _fallback: Bool = false

    def isFallback: Bool = _fallback

    def markAsFallback(): this.type = {
      _fallback = true
      this match {
        case Split.Cons(head, tail) =>
          head.continuation.markAsFallback()
          tail.markAsFallback()
        case Split.Let(_, _, _, tail) => tail.markAsFallback()
        case _: Split.Else | Split.Nil => ()
      }
      this
    }

    def clearFallback(): this.type = {
      _fallback = false
      this match {
        case Split.Cons(head, tail) =>
          head.continuation.clearFallback()
          tail.clearFallback()
        case Split.Let(_, _, _, tail) => tail.clearFallback()
        case _: Split.Else | Split.Nil => ()
      }
      this
    }

    // private val _fallbackSource = MutSet.empty[(Scrutinee, Pattern)]

    // def isFallbackOf(scrutinee: Scrutinee, pattern: Pattern): Bool =
    //   _fallbackSource.contains((scrutinee, pattern))

    // def markAsFallback(target: Opt[(Scrutinee, Pattern)]): this.type =
    //   target.fold[this.type](this)(this.markAsFallback)

    // def markAsFallback(target: (Scrutinee, Pattern)): this.type = {
    //   _fallbackSource += target
    //   this match {
    //     case Split.Cons(head, tail) =>
    //       head.continuation.markAsFallback(target)
    //       tail.markAsFallback(target)
    //     case Split.Let(_, _, _, tail) => tail.markAsFallback(target)
    //     case _: Split.Else | Split.Nil => ()
    //   }
    //   this
    // }

    // def withFallbackOf(that: Split): this.type = {
    //   _fallbackSource ++= that._fallbackSource
    //   this
    // }
  }

  object Split {
    final case class Cons(head: Branch, tail: Split) extends Split
    final case class Let(rec: Bool, name: Var, term: Term, tail: Split) extends Split
    final case class Else(default: Term) extends Split
    final case object Nil extends Split
  }
}
