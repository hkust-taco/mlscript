package mlscript.mono

import mlscript.DiffTests
import mlscript.utils.shorthands.Str
import mlscript.TypingUnit

class Test extends DiffTests(Test.dir) {
  override def postProcess(basePath: List[Str], testName: Str, unit: TypingUnit): List[Str] = 
    val monomorph = new Monomorph(false)
    val output = try {
      val result = monomorph.monomorphize(unit)
      result.toString()
    } catch {
      case error: MonomorphError => error.getMessage()
      case other: Throwable => other.toString()
    }
    output.linesIterator.toList
}

object Test {
  private val dir = os.pwd/"mono"/"shared"/"test"/"diff"
}
