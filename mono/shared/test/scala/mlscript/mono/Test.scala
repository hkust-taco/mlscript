package mlscript.mono

import mlscript.DiffTests
import mlscript.utils.shorthands.Str
import mlscript.TypingUnit
import mlscript.codegen.Helpers.inspect as showStructure
import scala.collection.mutable.StringBuilder
import mlscript.mono.printer.ExprPrinter

class Test extends DiffTests(Test.dir) {
  override def postProcess(basePath: List[Str], testName: Str, unit: TypingUnit): List[Str] = 
    val monomorph = new Monomorph(false)
    val output = try {
      val monomorphized = monomorph.monomorphize(unit)
      val outputBuilder = StringBuilder()
      outputBuilder ++= "Parsed:\n"
      outputBuilder ++= showStructure(unit)
      outputBuilder ++= "\nMonomorphized:\n"
      outputBuilder ++= ExprPrinter.print(monomorphized)
      outputBuilder.toString()
    } catch {
      case error: MonomorphError => error.getMessage()
      case other: Throwable => other.toString()
    }
    output.linesIterator.toList
}

object Test {
  private val dir = os.pwd/"mono"/"shared"/"test"/"diff"
}
