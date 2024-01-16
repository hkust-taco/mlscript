package mlscript.ucs

import mlscript.{Loc, Var}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.utils._, shorthands._

package object context {
  type NamedScrutinee = (Var -> Scrutinee)

  type MatchRegistry = Map[NamedScrutinee, CaseSet]

  type SeenRegistry = Map[NamedScrutinee, (TypeSymbol, Ls[Loc], CaseSet)]  
}
