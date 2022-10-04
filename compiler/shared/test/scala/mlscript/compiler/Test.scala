package mlscript.compiler

import mlscript.DiffTests
import mlscript.utils.shorthands.Str
import mlscript.TypingUnit
import mlscript.codegen.Helpers.inspect as showStructure
import scala.collection.mutable.StringBuilder
import mlscript.compiler.ClassLifter
import mlscript.Term

class DiffTestCompiler extends DiffTests {
  import DiffTestCompiler.*
  override def postProcess(basePath: List[Str], testName: Str, unit: TypingUnit): List[Str] = 
    val outputBuilder = StringBuilder()
    outputBuilder ++= "Parsed:\n"
    outputBuilder ++= showStructure(unit)

    outputBuilder ++= "\nLifted:\n"
    var monoUnit = unit;
    try{
      monoUnit = ClassLifter().liftTypingUnit(unit)
      outputBuilder ++= PrettyPrinter.showTypingUnit(monoUnit)
    }catch{
      case any: Throwable => outputBuilder ++= "Lifting failed: " ++ any.toString() ++ "\n" ++ any.getStackTrace().map(_.toString()).mkString("\n")
    }
    outputBuilder.toString().linesIterator.toList
  
  override protected lazy val files = allFiles.filter { file =>
      val fileName = file.baseName
      validExt(file.ext) && filter(file.relativeTo(pwd))
  }
}

object DiffTestCompiler{

  private val pwd = os.pwd
  private val dir = pwd/"compiler"/"shared"/"test"/"diff"
  
  private val allFiles = os.walk(dir).filter(_.toIO.isFile)
  
  private val validExt = Set("fun", "mls")

  private def filter(file: os.RelPath) = DiffTests.filter(file)
}
