package mlscript.compiler

import mlscript.utils.shorthands.*
import scala.util.control.NonFatal
import scala.collection.mutable.StringBuilder
import mlscript.{DiffTests, ModeType, TypingUnit}
import mlscript.compiler.debug.TreeDebug
import mlscript.compiler.mono.Monomorph
import mlscript.compiler.printer.ExprPrinter
import mlscript.compiler.mono.MonomorphError

class DiffTestCompiler extends DiffTests {
  import DiffTestCompiler.*
    override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit, output: Str => Unit): (List[Str], Option[TypingUnit]) = 
    val outputBuilder = StringBuilder()

    output("\nLifted:")
    var rstUnit = unit;
    try
      rstUnit = ClassLifter(mode.fullExceptionStack).liftTypingUnit(unit)
      output(PrettyPrinter.showTypingUnit(rstUnit))
    catch
      case NonFatal(err) =>
        output("Lifting failed: " ++ err.toString())
        if mode.fullExceptionStack then 
          output("\n" ++ err.getStackTrace().map(_.toString()).mkString("\n"))
    if(mode.mono){
      output("Mono:")
      val treeDebug = new TreeDebug()
      try{
        val monomorph = new Monomorph(treeDebug)
        val monomorphized = monomorph.defunctionalize(rstUnit)
        output("\nDefunc result: ")
        output(ExprPrinter.print(monomorphized))
      }catch{
        case error: MonomorphError => outputBuilder ++= (error.getMessage() :: error.getStackTrace().map(_.toString()).toList).mkString("\n")
        // case error: StackOverflowError => outputBuilder ++= (error.getMessage() :: error.getStackTrace().take(40).map(_.toString()).toList).mkString("\n")
      }
      // outputBuilder ++= treeDebug.getLines.mkString("\n")
    }
    (outputBuilder.toString().linesIterator.toList, Some(rstUnit))
  
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
