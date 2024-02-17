package mlscript.compiler


import mlscript.utils.shorthands._
import mlscript.compiler.ir._
import scala.collection.mutable.StringBuilder
import mlscript.{DiffTests, ModeType, TypingUnit}
import mlscript.compiler.ir.{Interpreter, Fresh, FreshInt, Builder}

class IRDiffTestCompiler extends DiffTests {
  import IRDiffTestCompiler.*

  override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit): List[Str] = 
    val outputBuilder = StringBuilder()
    if (mode.useIR || mode.irVerbose)
      try
        outputBuilder ++= "\n\nIR:\n"
        val gb = Builder(Fresh(), FreshInt(),  FreshInt(), FreshInt())
        val graph = gb.buildGraph(unit)
        outputBuilder ++= graph.toString()
        outputBuilder ++= "\n\nPromoted:\n"
        outputBuilder ++= graph.toString()
        var interp_result: Opt[Str] = None
        if (mode.interpIR)
          outputBuilder ++= "\n\nInterpreted:\n"
          val ir = Interpreter(mode.irVerbose).interpret(graph)
          interp_result = Some(ir)
          outputBuilder ++= ir
          outputBuilder ++= "\n"

      catch
        case err: Exception =>
          outputBuilder ++= s"\nIR Processing Failed: ${err.getMessage()}"
          outputBuilder ++= "\n" ++ err.getStackTrace().map(_.toString()).mkString("\n")
        case err: StackOverflowError =>
          outputBuilder ++= s"\nIR Processing Failed: ${err.getMessage()}"
          outputBuilder ++= "\n" ++ err.getStackTrace().map(_.toString()).mkString("\n")
      
    outputBuilder.toString().linesIterator.toList
  
  override protected lazy val files = allFiles.filter { file =>
      val fileName = file.baseName
      validExt(file.ext) && filter(file.relativeTo(pwd))
  }
}

object IRDiffTestCompiler {

  private val pwd = os.pwd
  private val dir = pwd/"compiler"/"shared"/"test"/"diff-ir"
  
  private val allFiles = os.walk(dir).filter(_.toIO.isFile)
  
  private val validExt = Set("fun", "mls")

  private def filter(file: os.RelPath) = DiffTests.filter(file)
  
}
