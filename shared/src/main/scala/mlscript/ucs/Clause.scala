package mlscript.ucs

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import scala.collection.mutable.Buffer

/**
  * A `Clause` represents a minimal unit of logical predicate in the UCS.
  * There are three kinds of clauses: boolean test, class match, and tuple match.
  */
sealed abstract class Clause {
  /**
    * Local interleaved let bindings declared before this condition.
    */
  var bindings: Ls[LetBinding] = Nil

  /**
    * Locations of terms that build this `Clause`.
    *
    * @return
    */
  val locations: Ls[Loc]

  protected final def bindingsToString: String =
    if (bindings.isEmpty) "" else " with " + (bindings match {
      case Nil => ""
      case bindings => bindings.map(_.name.name).mkString("(", ", ", ")")
    })
}

sealed abstract class MatchClause extends Clause {
  val scrutinee: Scrutinee
}

object Clause {
  final case class MatchLiteral(
    override val scrutinee: Scrutinee,
    literal: SimpleTerm
  )(override val locations: Ls[Loc]) extends MatchClause {
    override def toString(): String = s"«$scrutinee is $literal" + bindingsToString
  }

  final case class MatchAny(override val scrutinee: Scrutinee)(override val locations: Ls[Loc]) extends MatchClause {
    override def toString(): String = s"«$scrutinee is any" + bindingsToString
  }

  final case class MatchClass(
    override val scrutinee: Scrutinee,
    className: Var,
    fields: Ls[Str -> Var]
  )(override val locations: Ls[Loc]) extends MatchClause {
    override def toString(): String = s"«$scrutinee is $className»" + bindingsToString
  }

  final case class MatchTuple(
    scrutinee: Scrutinee,
    arity: Int,
    fields: Ls[Str -> Var]
  )(override val locations: Ls[Loc]) extends Clause {
    override def toString(): String = s"«$scrutinee is Tuple#$arity»" + bindingsToString
  }

  final case class BooleanTest(test: Term)(
    override val locations: Ls[Loc]
  ) extends Clause {
    override def toString(): String = s"«$test»" + bindingsToString
  }

  /**
    * @param isField whether this binding is extracting a class field
    */
  final case class Binding(name: Var, term: Term, isField: Bool)(
    override val locations: Ls[Loc]
  ) extends Clause {
    override def toString(): String = s"«$name = $term»" + bindingsToString
  }
}
