package mlscript.compiler

import mlscript.DiffTests
import mlscript.utils.shorthands.Str
import mlscript.TypingUnit
import mlscript.codegen.Helpers.inspect as showStructure
import scala.collection.mutable.StringBuilder
import mlscript.compiler.ClassLifter
import mlscript.Term

class Test extends DiffTests {
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
}

object Test {
  private val dir = os.pwd/"mono"/"shared"/"test"/"diff"
}
