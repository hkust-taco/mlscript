package mlscript.ucs

import mlscript.{Loc, Var}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.utils._, shorthands._

package object context {
  type NamedScrutinee = (Var -> Scrutinee)

  type MatchRegistry = Map[NamedScrutinee, CaseSet]

  // implicit class MatchRegistryOps(val self: MatchRegistry) extends AnyVal {
  //   def showDbg: Str = 
  // }

  type SeenRegistry = Map[NamedScrutinee, (TypeSymbol, Ls[Loc], CaseSet)]

  implicit class SeenRegistryOps(val self: SeenRegistry) extends AnyVal {
    def showDbg: Str = if (self.isEmpty) "empty" else
      self.iterator.map { case ((k, _), (s, _, _)) => s"${k.name} is ${s.name}" }.mkString(", ")
  }
}
