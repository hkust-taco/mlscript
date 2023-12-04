package mlscript.compiler

import mlscript.utils.shorthands.*
import scala.util.control.NonFatal
import scala.collection.mutable.StringBuilder
import mlscript.codegen.Helpers.inspect as showStructure
import mlscript.{DiffTests, ModeType, TypingUnit}
import mlscript.compiler.debug.TreeDebug
import mlscript.compiler.mono.Monomorph
import mlscript.compiler.printer.ExprPrinter
import mlscript.compiler.mono.MonomorphError

class DiffTestCompiler extends DiffTests {
  import DiffTestCompiler.*
  override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit): (List[Str], Option[TypingUnit]) = 
    val outputBuilder = StringBuilder()
    outputBuilder ++= "Parsed:\n"
    outputBuilder ++= showStructure(unit)

    outputBuilder ++= "\nLifted:\n"
    var rstUnit = unit;
    try
      val lifter = ClassLifter(mode.fullExceptionStack)
      rstUnit = lifter.liftTypingUnit(unit)
      outputBuilder ++= s"${mlscript.codegen.Helpers.inspect(rstUnit)}\n"
      outputBuilder ++= PrettyPrinter.showTypingUnit(rstUnit)
      if (mode.dbgLifting) 
        outputBuilder ++= lifter.getLog
    catch
      case NonFatal(err) =>
        outputBuilder ++= "Lifting failed: " ++ err.toString()
        if mode.fullExceptionStack then 
          outputBuilder ++= "\n" ++ err.getStackTrace().map(_.toString()).mkString("\n")
    if(mode.mono || mode.numono){
      outputBuilder ++= "\nMono:\n"
      val treeDebug = new TreeDebug()
      try{
        val monomorph = new Monomorph(treeDebug)
        if (mode.numono)
          then
            val defuncAST = monomorph.nuDefunctionalize(rstUnit)
            outputBuilder ++= s"${mlscript.codegen.Helpers.inspect(defuncAST)}\n"
            outputBuilder ++= PrettyPrinter.showTypingUnit(defuncAST)++"\n"
            if mode.dbgDefunc then
              outputBuilder ++= treeDebug.getLines.mkString("\n")
            return (outputBuilder.toString().linesIterator.toList, Some(defuncAST))
          else
            val monomorphized = monomorph.defunctionalize(rstUnit)
            outputBuilder ++= "\nDefunc result: \n"
            outputBuilder ++= ExprPrinter.print(monomorphized)
            outputBuilder ++= "\n"
            if mode.dbgDefunc then
              outputBuilder ++= treeDebug.getLines.mkString("\n")
            return (outputBuilder.toString().linesIterator.toList, if mode.revConv then Some(monomorph.toTypingUnit(monomorphized)) else None)
      }catch{
        case error: MonomorphError => outputBuilder ++= (error.getMessage()/* :: error.getStackTrace().map(_.toString()).toList).mkString("\n"*/)
        // case error: StackOverflowError => outputBuilder ++= (error.getMessage() :: error.getStackTrace().take(40).map(_.toString()).toList).mkString("\n")
      }
      // outputBuilder ++= treeDebug.getLines.mkString("\n")
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
