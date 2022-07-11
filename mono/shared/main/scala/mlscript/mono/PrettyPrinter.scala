package mlscript.mono

import mlscript.{TypingUnit, NuFunDef, NuTypeDef, Term}

// For pretty printing terms in debug output.
object PrettyPrinter:
  def show(term: Term): String = term.toString

  def show(unit: TypingUnit): String =
    s"TypingUnit " + unit.entities.iterator.map {
      case Left(term) => show(term)
      case Right(tyDef: NuTypeDef) => tyDef.kind.str + " " + tyDef.nme.name
      case Right(funDef: NuFunDef) => "fun " + funDef.nme.name
    }.mkString("{", "; ", "}")