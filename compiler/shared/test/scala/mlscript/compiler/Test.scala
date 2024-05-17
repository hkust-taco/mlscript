package mlscript.compiler

import mlscript.utils.shorthands.*
import scala.util.control.NonFatal
import scala.collection.mutable.StringBuilder
import mlscript.{DiffTests, ModeType, TypingUnit}
import mlscript.compiler.TreeDebug
import mlscript.compiler.mono.Monomorph
import mlscript.compiler.mono.MonomorphError

class DiffTestCompiler extends DiffTests {
  import DiffTestCompiler.*
  override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit, output: Str => Unit): (List[Str], Option[TypingUnit]) = 
    val outputBuilder = StringBuilder()
    if (mode.lift) output(PrettyPrinter.showTypingUnit(unit))

    output("Lifted:")
    var rstUnit = unit;
    try
      val lifter = ClassLifter(mode.fullExceptionStack)
      if (!mode.nolift) rstUnit = lifter.liftTypingUnit(unit)
      if (mode.showParse) output(rstUnit.toString())
      output(PrettyPrinter.showTypingUnit(rstUnit))
      if (mode.dbgLifting) 
        output(lifter.getLog)
    catch
      case NonFatal(err) =>
        output("Lifting failed: " ++ err.toString())
        if mode.fullExceptionStack then 
          output("\n" ++ err.getStackTrace().map(_.toString()).mkString("\n"))
    if(mode.mono){
      output("Mono:")
      val treeDebug = new TreeDebug(if mode.dbgDefunc then output else (str) => ())
      try{
        val monomorph = new Monomorph(treeDebug)
        val defuncAST = monomorph.defunctionalize(rstUnit)
        if (mode.showParse) output(defuncAST.toString())
        output(PrettyPrinter.showTypingUnit(defuncAST))
        return (outputBuilder.toString().linesIterator.toList, Some(defuncAST))
      }catch{
        case error: MonomorphError => 
          if (mode.expectCodeGenErrors)
            output(error.getMessage() ++ "\n" ++ (error.getStackTrace().take(10).map(_.toString()).toList).mkString("\n"))
        return (Nil, None)
        // case error: StackOverflowError => outputBuilder ++= (error.getMessage() :: error.getStackTrace().take(40).map(_.toString()).toList).mkString("\n")
      }
    }
    if (mode.lift) {
      (outputBuilder.toString().linesIterator.toList, Some(rstUnit))  
    } else {
      (outputBuilder.toString().linesIterator.toList, None)
    }
  
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
