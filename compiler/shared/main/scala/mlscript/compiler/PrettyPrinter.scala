package mlscript.compiler

import mlscript.{TypingUnit, NuFunDef, NuTypeDef, Term, Tup}
import mlscript.compiler.DebugOutput

// For pretty printing terms in debug output.
object PrettyPrinter:
  def show(term: Term): DebugOutput = DebugOutput.Code(term.showDbg.linesIterator.toList)
  def show(unit: TypingUnit): DebugOutput = DebugOutput.Code(showTypingUnit(unit, 0).linesIterator.toList)
  def show(funDef: NuFunDef): DebugOutput = DebugOutput.Code(showFunDef(funDef).linesIterator.toList)
  def show(tyDef: NuTypeDef): DebugOutput = DebugOutput.Code(showTypeDef(tyDef, 0).linesIterator.toList)

  def showTypingUnit(unit: TypingUnit, indent: Int = 0): String =
    val head = if indent == 0 then "TypingUnit " else " "
    val singleLine = head + unit.entities.iterator.map {
      case term: Term => show(term)
      case tyDef: NuTypeDef => showTypeDef(tyDef)
      case funDef: NuFunDef => showFunDef(funDef)
      case others => others.showDbg
    }.mkString("{", "; ", "}")
    if (singleLine.length < 60)
      singleLine
    else
      val indentStr = " " * (indent * 2)
      head + unit.entities.iterator.map {
        case term: Term => show(term)
        case tyDef: NuTypeDef => showTypeDef(tyDef)
        case funDef: NuFunDef => showFunDef(funDef)
        case others => others.showDbg
      }.map(indentStr + "  " + _).mkString("{\n", "\n", s"\n$indentStr}")
  
  def showFunDef(funDef: NuFunDef): String =
    val st = (funDef.isLetRec) match {
      case None => "fun"
      case Some(false) => "let"
      case Some(true) => "let'"
    }
    s"$st ${funDef.nme.name}"
      + (if funDef.tparams.isEmpty
         then ""
         else funDef.tparams.map(_.name).mkString("[", ", ", "]"))
      + " = "
      + funDef.rhs.fold(_.showDbg, _.show(newDefs = true))

  def showTypeDef(tyDef: NuTypeDef, indent: Int = 0): String =
    s"${tyDef.kind.str} ${tyDef.nme.name}"
      + (if tyDef.tparams.isEmpty
         then ""
         else tyDef.tparams.map(_._2.name).mkString("[", ",", "]"))
      + tyDef.params.fold("")(params => s"(${params.showDbg})")
      + (if tyDef.parents.isEmpty
         then ""
         else ": " + tyDef.parents.map(_.showDbg).mkString(", "))
      + showTypingUnit(tyDef.body, indent + 1)
