package mlscript.compiler

import mlscript.utils.shorthands.*
import scala.util.control.NonFatal
import scala.collection.mutable.StringBuilder
import mlscript.{DiffTests, ModeType, TypingUnit}
import mlscript.compiler.TreeDebug
import mlscript.compiler.mono.Monomorph
import mlscript.compiler.mono.MonomorphError
import mlscript.Polyfill
import mlscript.compiler.polydef.Polydef

class DiffTestCompiler extends DiffTests {
  import DiffTestCompiler.*
  override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit, output: Str => Unit): (List[Str], Option[TypingUnit]) = 
    val outputBuilder = StringBuilder()
    //output("Parsed:")    
    //output(unit.toString())
    if (mode.lift) output(PrettyPrinter.showTypingUnit(unit))

    //outputBuilder ++= "\nLifted:\n"
    var rstUnit = unit;
    try
      val lifter = ClassLifter(mode.fullExceptionStack)
      if (!mode.nolift)
        output("Lifted:")
        rstUnit = lifter.liftTypingUnit(unit)
        output(PrettyPrinter.showTypingUnit(rstUnit))
      if (mode.showParse) output(rstUnit.toString())
      //outputBuilder ++= s"${mlscript.codegen.Helpers.inspect(rstUnit)}\n"
      //outputBuilder ++= PrettyPrinter.showTypingUnit(rstUnit)
      if (mode.dbgLifting) 
        output(lifter.getLog)
    catch
      case NonFatal(err) =>
        outputBuilder ++= "Lifting failed: " ++ err.toString()
        if mode.fullExceptionStack then 
          outputBuilder ++= "\n" ++ err.getStackTrace().map(_.toString()).mkString("\n")
    if(mode.polydef) {
      output("\nPolydef:")
      val treeDebug = new TreeDebug(if mode.dbgPolydef then output else (str) => ())
      val pd = Polydef(treeDebug)
      pd(rstUnit)
      output(pd.termMap.toString())
      output(pd.exprToProdType.toString())
      output(s"TypeVars: ${pd.varsName.mkString("\n")}")
      output(s"Upper bounds: ${pd.upperBounds.mkString("\n")}")
      output(s"Lower bounds: ${pd.lowerBounds.mkString("\n")}")
      output("Polydef end\n")
    }
    if(mode.mono){
      output("Mono:")
      //outputBuilder ++= "\nMono:\n"
      val treeDebug = new TreeDebug(if mode.dbgDefunc then output else (str) => ())
      try{
        val monomorph = new Monomorph(treeDebug)
        val defuncAST = monomorph.defunctionalize(rstUnit)
        //output(defuncAST.toString())
        output(PrettyPrinter.showTypingUnit(defuncAST))
        //outputBuilder ++= s"${mlscript.codegen.Helpers.inspect(defuncAST)}\n"
        //outputBuilder ++= PrettyPrinter.showTypingUnit(defuncAST)++"\n"
        //if mode.dbgDefunc then
        //  outputBuilder ++= treeDebug.getLines.mkString("\n")
        return (outputBuilder.toString().linesIterator.toList, Some(defuncAST))
      }catch{
        case error: MonomorphError => outputBuilder ++= (error.getMessage()/* :: error.getStackTrace().map(_.toString()).toList).mkString("\n"*/)
        // case error: StackOverflowError => outputBuilder ++= (error.getMessage() :: error.getStackTrace().take(40).map(_.toString()).toList).mkString("\n")
      }
      // outputBuilder ++= treeDebug.getLines.mkString("\n")
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
