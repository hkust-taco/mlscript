package mlscript.ucs.old

import scala.collection.mutable.{Set => MutSet}

import mlscript._
import mlscript.utils.shorthands._

object helpers {
  /**
    * Generate a chain of `Let` from a list of bindings.
    *
    * @param bindings a list of bindings, 
    * @param body the final body
    */
  def mkBindings(bindings: Ls[LetBinding], body: Term, defs: Set[Var]): Term = {
    def rec(bindings: Ls[LetBinding], defs: Set[Var]): Term =
      bindings match {
        case Nil => body
        case LetBinding(_, isRec, nameVar, value) :: tail =>
          if (defs.contains(nameVar)) {
            rec(tail, defs)
          } else {
            Let(isRec, nameVar, value, rec(tail, defs + nameVar))
          }
      }
    rec(bindings, defs)
  }
}
