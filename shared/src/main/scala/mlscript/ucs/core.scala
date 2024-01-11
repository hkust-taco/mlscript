package mlscript.ucs

import collection.mutable.Buffer
import mlscript.{Diagnostic, Lit, Loc, Located, Message, Term, Var}
import mlscript.utils._, shorthands._
import mlscript.ucs.core.Split.Cons
import mlscript.ucs.core.Split.Let
import mlscript.ucs.core.Split.Else
import mlscript.ucs.stages.Desugaring

package object core {
  sealed abstract class Pattern extends Located {
    override def toString(): String = this match {
      case Pattern.Literal(literal) => literal.toString
      case Pattern.Name(Var(name)) => name
      case Pattern.Class(Var(name), rfd) => (if (rfd) "refined " else "") + name
      case Pattern.Tuple(fields) => fields.iterator.map(_.fold("_")(_.name)).mkString("(", ", ", ")")
      case Pattern.Record(Nil) => "{}"
      case Pattern.Record(entries) => entries.iterator.map { case (nme, als) => s"$nme: $als" }.mkString("{ ", ", ", " }")
    }
  }
  object Pattern {
    final case class Literal(literal: Lit) extends Pattern {
      override def children: Ls[Located] = literal :: Nil
    }
    final case class Name(nme: Var) extends Pattern {
      override def children: Ls[Located] = nme :: Nil
    }
    final case class Class(nme: Var, refined: Bool) extends Pattern {
      override def children: Ls[Located] = nme :: Nil
    }
    final case class Tuple(elements: List[Opt[Var]]) extends Pattern {
      override def children: Ls[Located] = elements.flatten
    }
    final case class Record(entries: List[(Var -> Var)]) extends Pattern {
      override def children: Ls[Located] = entries.iterator.flatMap { case (nme, als) => nme :: als :: Nil }.toList
    }

    def getParametersLoc(parameters: List[Opt[Var]]): Opt[Loc] =
      parameters.foldLeft(None: Opt[Loc]) {
        case (acc, N) => acc
        case (N, S(nme)) => nme.toLoc
        case (S(loc), S(nme)) => S(nme.toLoc.fold(loc)(loc ++ _))
      }
    def getParametersLoc(parameters: Opt[List[Opt[Var]]]): Opt[Loc] =
      parameters.fold(None: Opt[Loc])(getParametersLoc)

    def showParameters(parameters: Opt[List[Opt[Var]]]): Str =
      parameters.fold("empty")(_.map(_.fold("_")(_.name)).mkString("[", ", ", "]"))
  }

  final case class Branch(scrutinee: Var, pattern: Pattern, continuation: Split)

  sealed abstract class Split {
    @inline
    def ::(head: Branch): Split = Split.Cons(head, this)

    /**
      * Concatenates two splits. Beware that `that` may be discarded if `this`
      * has an else branch. Make sure to make diagnostics for discarded `that`.
      */
    def ++(that: Split): Split = this match {
      case me: Split.Cons => me.copy(tail = me.tail ++ that)
      case me: Split.Let => me.copy(tail = me.tail ++ that)
      case _: Split.Else => this
      case Split.Nil => that
    }
    
    /**
      * Returns true if the split has an else branch.
      */
    lazy val hasElse: Bool = this match {
      case Split.Cons(_, tail) => tail.hasElse
      case Split.Let(_, _, _, tail) => tail.hasElse
      case Split.Else(_) => true
      case Split.Nil => false
    }

    lazy val freeVars: Set[Var] = this match {
      case Split.Cons(Branch(scrutinee, pattern, continuation), tail) =>
        // FIXME: It is safe to ignore `pattern` for now.
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
      case self @ Cons(head @ Branch(_, _, continuation), tail) =>
        self.copy(head.copy(continuation = continuation.withoutBindings(vars)), tail.withoutBindings(vars))
      case self @ Let(_, name, _, tail) if vars contains name => tail.withoutBindings(vars)
      case self @ Let(_, _, _, tail) => self.copy(tail = tail.withoutBindings(vars))
      case Else(_) | Split.Nil => this
    }

    private val diagnostics: Buffer[Message -> Opt[Loc]] = Buffer.empty

    def withDiagnostic(diagnostic: Message -> Opt[Loc]): this.type = {
      diagnostics += diagnostic
      this
    }

    def collectDiagnostics(): Ls[Message -> Opt[Loc]] =
      diagnostics.toList ++ (this match {
        case Split.Cons(_, tail) => tail.collectDiagnostics()
        case Split.Let(_, _, _, tail) => tail.collectDiagnostics()
        case Split.Else(_) | Split.Nil => Nil
      })
  }

  object Split {
    final case class Cons(head: Branch, tail: Split) extends Split
    final case class Let(rec: Bool, name: Var, term: Term, tail: Split) extends Split
    final case class Else(default: Term) extends Split
    final case object Nil extends Split

    def just(term: Term): Split = Else(term)
  }
}