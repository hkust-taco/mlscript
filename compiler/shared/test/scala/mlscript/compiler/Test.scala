package mlscript.compiler

import mlscript.utils.shorthands.*
import scala.util.control.NonFatal
import scala.collection.mutable.StringBuilder
import mlscript.{DiffTests, ModeType, TypingUnit}
import mlscript.compiler.TreeDebug
import mlscript.Polyfill
import mlscript.compiler.simpledef.SimpleDef
import simpledef.SimpleDef

class DiffTestCompiler extends DiffTests {
  import DiffTestCompiler.*
  override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit, output: Str => Unit): (List[Str], Option[TypingUnit]) = 
    val outputBuilder = StringBuilder()
    if (mode.lift) output(PrettyPrinter.showTypingUnit(unit))

    var rstUnit = unit;
    try
      val lifter = ClassLifter(mode.fullExceptionStack)
      if (mode.lift || basePath.contains("Lifter")) {
        output("Lifted:")
        rstUnit = lifter.liftTypingUnit(unit)
        output(PrettyPrinter.showTypingUnit(rstUnit))
      }
      if (mode.showParse) output(rstUnit.toString())
      if (mode.dbgLifting) 
        output(lifter.getLog)
    catch
      case NonFatal(err) =>
        output("Lifting failed: " ++ err.toString())
        if mode.fullExceptionStack then 
          outputBuilder ++= "\n" ++ err.getStackTrace().map(_.toString()).mkString("\n")
    if(mode.simpledef || basePath.contains("Defunctionalize")) {
      output("\nSimpledef:")
      val treeDebug = new TreeDebug(if mode.dbgSimpledef then output else (str) => ())
      val pd = SimpleDef(treeDebug)
      pd(rstUnit)
      val defuncAST = pd.rewriteProgram(rstUnit)
      output(defuncAST.showDbg.replace(";", "\n"))
      output("End simpledef\n")
      return (outputBuilder.toString().linesIterator.toList, Some(defuncAST))
    }
    if (mode.lift || basePath.contains("Lifter")) {
      (outputBuilder.toString().linesIterator.toList, Some(rstUnit))  
    } else {
      (outputBuilder.toString().linesIterator.toList, None)
    }
  
  override def postTypingProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit, output: Str => Unit): (List[Str], Option[TypingUnit]) = 
    if (!mode.postProcessAfterTyping) 
      return (Nil, None)
    
    val outputBuilder = StringBuilder()

    if(mode.simpledef || basePath.contains("Defunctionalize")) {
      output("\nSimpledef:")
      val treeDebug = new TreeDebug(if mode.dbgSimpledef then output else (str) => ())
      val pd = SimpleDef(treeDebug)
      pd(unit)
      val defuncAST = pd.rewriteProgram(unit)
      output(defuncAST.showDbg.replace(";", "\n"))
      output("End simpledef\n")
      return (outputBuilder.toString().linesIterator.toList, Some(defuncAST))
    }
    (outputBuilder.toString().linesIterator.toList, None)
    
  override protected lazy val files = allFiles.filter { file =>
      val fileName = file.baseName
      validExt(file.ext) && filter(file.relativeTo(pwd))
  }
}

object DiffTestCompiler {

  private val pwd = os.pwd
  private val dir = pwd/"compiler"/"shared"/"test"/"diff"
  
  private val allFiles = os.walk(dir).filter(_.toIO.isFile)
  
  private val validExt = Set("fun", "mls")

  private def filter(file: os.RelPath) = DiffTests.filter(file)
  
}
