package mlscript
package compiler

import utils.shorthands.*
import scala.util.control.NonFatal
import scala.collection.mutable.StringBuilder
import mlscript.compiler.TreeDebug
import simpledef.SimpleDef

class DiffTestCompiler extends DiffTests {
  import DiffTestCompiler.*
  override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit, output: Str => Unit, raise: Diagnostic => Unit): (List[Str], Option[TypingUnit]) = 
    val outputBuilder = StringBuilder()

    var rstUnit = unit;
    try
      val lifter = ClassLifter(mode.fullExceptionStack)
      if (mode.lift) {
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
    if (mode.lift) {
      (outputBuilder.toString().linesIterator.toList, Some(rstUnit))  
    } else {
      (outputBuilder.toString().linesIterator.toList, None)
    }
  
  override def postTypingProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit, output: Str => Unit): Option[TypingUnit] = 
    if(mode.simpledef || basePath.contains("Defunctionalize")) {
      output("\nSimpledef:")
      val treeDebug = new TreeDebug(if mode.dbgSimpledef then output else (str) => ())
      val pd = SimpleDef(treeDebug)
      pd(unit)
      val defuncAST = pd.rewriteProgram(unit)
      output(defuncAST.showDbg.replace(";", "\n"))
      output("End simpledef\n")
      return Some(defuncAST)
    }
    None
    
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
