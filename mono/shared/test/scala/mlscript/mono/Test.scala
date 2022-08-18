package mlscript.mono

import mlscript.DiffTests
import mlscript.utils.shorthands.Str
import mlscript.TypingUnit
import mlscript.codegen.Helpers.inspect as showStructure
import scala.collection.mutable.StringBuilder
import mlscript.mono.printer.ExprPrinter
import mlscript.mono.debug.TreeDebug

class Test extends DiffTests(Test.dir) {
  override def postProcess(basePath: List[Str], testName: Str, unit: TypingUnit): List[Str] = 
    val debug = TreeDebug()
    val monomorph = new Monomorph(debug)
    try {
      val monomorphized = monomorph.monomorphize(unit)
      val outputBuilder = StringBuilder()
      outputBuilder ++= "Parsed:\n"
      outputBuilder ++= showStructure(unit)
      outputBuilder ++= "\nMonomorphized:\n"
      outputBuilder ++= ExprPrinter.print(monomorphized)
      outputBuilder.toString().linesIterator.toList
    } catch {
      case error: MonomorphError => error.getMessage() :: debug.getLines
      case other: Throwable => other.toString().linesIterator.toList
    }
}

object Test {
  private val dir = os.pwd/"mono"/"shared"/"test"/"diff"
}
