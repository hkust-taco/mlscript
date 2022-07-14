package mlscript.mono

import mlscript.{TypingUnit, NuFunDef, NuTypeDef, Term}

// For pretty printing terms in debug output.
object PrettyPrinter:
  def show(term: Term): String = term.toString
  def show(unit: TypingUnit): String = showTypingUnit(unit, 0)
  def show(funDef: NuFunDef): String = showFunDef(funDef)
  def show(tyDef: NuTypeDef): String = showTypeDef(tyDef, 0)

  def showTypingUnit(unit: TypingUnit, indent: Int = 0): String =
    val head = if indent == 0 then "TypingUnit " else " "
    val singleLine = head + unit.entities.iterator.map {
      case Left(term) => show(term)
      case Right(tyDef: NuTypeDef) => showTypeDef(tyDef)
      case Right(funDef: NuFunDef) => showFunDef(funDef)
    }.mkString("{", "; ", "}")
    if (singleLine.length < 60)
      singleLine
    else
      val indentStr = " " * (indent * 2)
      head + unit.entities.iterator.map {
        case Left(term) => show(term)
        case Right(tyDef: NuTypeDef) => showTypeDef(tyDef)
        case Right(funDef: NuFunDef) => showFunDef(funDef)
      }.map(indentStr + "  " + _).mkString("{\n", "\n", s"\n$indentStr}")
  
  def showFunDef(funDef: NuFunDef): String =
    s"${funDef.nme.name}"
      + (if funDef.targs.isEmpty
         then ""
         else funDef.targs.map(_.name).mkString("[", ", ", "]"))
      + (if funDef.specParams.isEmpty
         then ""
         else funDef.specParams.map(_._1.name).mkString(" ", " ", ""))
      + " = "
      + funDef.body.fold(_.toString, _.body.show)

  def showTypeDef(tyDef: NuTypeDef, indent: Int = 0): String =
    s"${tyDef.kind.str} ${tyDef.nme.name}"
      + (if tyDef.tparams.isEmpty
         then ""
         else tyDef.tparams.map(_.name).mkString("[", ",", "]"))
      + (if tyDef.parents.isEmpty
         then ""
         else ": " + tyDef.parents.map(_.base.name).mkString(", "))
      + showTypingUnit(tyDef.body, indent + 1)
