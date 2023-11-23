package mlscript

import mlscript.utils._, shorthands._

package object pretyper {
  def shortName(term: Term): Str = term match {
    case Var(name) => s"Var(\"$name\")"
    case literal: Lit => literal.toString
    case _ =>
      val name = term.getClass.getSimpleName
      val arity = term.children.length // Imprecise
      if (arity === 0) { name } else s"${name}(${(", _" * arity).drop(2)})"
  }
}
