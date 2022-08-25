package mlscript.mono

import mlscript.{TypingUnit, NuFunDef, NuTypeDef, Term}
import mlscript.mono.debug.DebugOutput

// For pretty printing terms in debug output.
object PrettyPrinter:
  def show(term: Term): DebugOutput = DebugOutput.Code(term.toString.linesIterator.toList)
  def show(unit: TypingUnit): DebugOutput = DebugOutput.Code(showTypingUnit(unit, 0).linesIterator.toList)
  def show(funDef: NuFunDef): DebugOutput = DebugOutput.Code(showFunDef(funDef).linesIterator.toList)
  def show(tyDef: NuTypeDef): DebugOutput = DebugOutput.Code(showTypeDef(tyDef, 0).linesIterator.toList)

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
      + " = "
      + funDef.rhs.fold(_.toString, _.body.show)

  def showTypeDef(tyDef: NuTypeDef, indent: Int = 0): String =
    s"${tyDef.kind.str} ${tyDef.nme.name}"
      + (if tyDef.tparams.isEmpty
         then ""
         else tyDef.tparams.map(_.name).mkString("[", ",", "]"))
      + (if tyDef.parents.isEmpty
         then ""
         else ": " + tyDef.parents.map(_.print).mkString(", "))
      + showTypingUnit(tyDef.body, indent + 1)
