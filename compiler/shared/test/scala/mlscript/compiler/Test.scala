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
  override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit): List[Str] = 
    val outputBuilder = StringBuilder()
    outputBuilder ++= "Parsed:\n"
    outputBuilder ++= showStructure(unit)

    if (mode.graphOpt)
      try
        outputBuilder ++= "\n\nGraphOpt:\n"
        val go = GraphOptimizer()
        val graph = go.buildGraph(unit)
        outputBuilder ++= graph.toString()
        outputBuilder ++= "\n\nPromoted ------------------------------------\n"
        val graph2 = go.simplifyProgram(go.promoteJoinPoints(graph))
        val graph3 = go.activeAnalyze(graph2)
        outputBuilder ++= graph3.toString()
        if (mode.goInterp)
          outputBuilder ++= "\n\nInterpreted ------------------------------\n"
          outputBuilder ++= GOInterpreter.interpret(graph3)
          outputBuilder ++= "\n"
        // outputBuilder ++= "\n\nSplitted ------------------------------------\n"
        // val graph4 = go.simplifyProgram(go.splitFunction(graph3))
        // val graph5 = go.activeAnalyze(graph4)
        // outputBuilder ++= graph5.toString()
        // outputBuilder ++= "\n\nScalarReplaced ------------------------------\n"
        // val graph6 = go.simplifyProgram(go.replaceScalar(graph5))
        // val graph7 = go.activeAnalyze(graph6)
        // outputBuilder ++= graph7.toString()
       
        var changed = true
        var g = graph3
        val fuel_limit = 15
        var fuel = fuel_limit
        while (changed && fuel > 0)
          val new_g = go.optimize(g)
          changed = g != new_g
          g = new_g
          if (changed)
            outputBuilder ++= "\n\nOptimized ------------------------------\n"
            outputBuilder ++= new_g.toString()
          fuel -= 1
        

        outputBuilder ++= "\n"

        if (mode.goInterp)
          outputBuilder ++= "\n\nInterpreted ------------------------------\n"
          outputBuilder ++= GOInterpreter.interpret(g)
          outputBuilder ++= "\n"

        outputBuilder ++= s"\n\nFuel used: ${fuel_limit - fuel}"

        if (fuel == 0)
          throw GraphOptimizingError("Fuel exhausted")

      catch
        case err @ GOInterpreterError(msg) =>
          outputBuilder ++= s"\nGOInterp failed: ${msg}"
          outputBuilder ++= "\n" ++ err.getStackTrace().map(_.toString()).mkString("\n")
        case err @ GraphOptimizingError(msg) =>
          outputBuilder ++= s"\nGraphOpt failed: ${msg}"
          outputBuilder ++= "\n" ++ err.getStackTrace().map(_.toString()).mkString("\n")
        case err =>
          outputBuilder ++= s"\nGraphOpt failed"
          outputBuilder ++= "\n" ++ err.getStackTrace().map(_.toString()).mkString("\n")

    outputBuilder.toString().linesIterator.toList
  
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
