package mlscript.mono

import mlscript.{TypingUnit, NuFunDef, NuTypeDef, Term}

// For pretty printing terms in debug output.
object PrettyPrinter:
  def show(term: Term): String = term.toString

  def show(unit: TypingUnit): String =
    val singleLine = s"TypingUnit " + unit.entities.iterator.map {
      case Left(term) => show(term)
      case Right(tyDef: NuTypeDef) => tyDef.kind.str + " " + tyDef.nme.name
      case Right(funDef: NuFunDef) => "fun " + funDef.nme.name
    }.mkString("{", "; ", "}")
    if (singleLine.length < 60)
      singleLine
    else
      s"TypingUnit " + unit.entities.iterator.map {
        case Left(term) => show(term)
        case Right(tyDef: NuTypeDef) => tyDef.kind.str + " " + tyDef.nme.name
        case Right(funDef: NuFunDef) => "fun " + funDef.nme.name
      }.map("  " + _).mkString("{\n", "\n", "\n}")
  
  def show(funDef: NuFunDef): String =
    s"${funDef.nme.name}"
      + (if funDef.targs.isEmpty
         then ""
         else funDef.targs.map(_.name).mkString("[", ", ", "]"))
      + funDef.specParams.map(_._1.name).mkString("(", ", ", ")")

  def show(tyDef: NuTypeDef): String =
    s"${tyDef.kind.str} ${tyDef.nme.name}"
      + (if tyDef.tparams.isEmpty
         then ""
         else tyDef.tparams.map(_.name).mkString("[", ",", "]"))
      + (if tyDef.parents.isEmpty
         then ""
         else ": " + tyDef.parents.map(_.base.name).mkString(", "))
