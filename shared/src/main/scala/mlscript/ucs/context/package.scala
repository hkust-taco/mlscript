package mlscript.ucs

import mlscript.{Loc, Var}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.utils._, shorthands._

package object context {
  type NamedScrutineeData = (Var -> ScrutineeData)

  type MatchRegistry = Map[NamedScrutineeData, CaseSet]

  type SeenRegistry = Map[NamedScrutineeData, (TypeSymbol, Ls[Loc], CaseSet)]  
}
