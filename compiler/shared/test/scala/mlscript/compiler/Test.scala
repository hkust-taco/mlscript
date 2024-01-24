package mlscript.compiler

import mlscript.utils.shorthands.*
import scala.util.control.NonFatal
import scala.collection.mutable.StringBuilder
import mlscript.{DiffTests, ModeType, TypingUnit}
import mlscript.compiler.debug.TreeDebug
import mlscript.compiler.mono.Monomorph
import mlscript.compiler.printer.ExprPrinter
import mlscript.compiler.mono.MonomorphError
import mlscript.compiler.optimizer.{GraphOptimizer, GraphInterpreter, Fresh, FreshInt}
import mlscript.compiler.optimizer.GraphBuilder

class DiffTestCompiler extends DiffTests {
  import DiffTestCompiler.*
  override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit): List[Str] = 
    val outputBuilder = StringBuilder()

    if (mode.graphOpt || mode.graphOptVerbose)
      try
        outputBuilder ++= "\n\nGraphOpt:\n"
        val f1 = Fresh()
        val f2 = FreshInt()
        val f3 = FreshInt()
        val f4 = FreshInt()
        val gb = GraphBuilder(f1, f2, f3, f4)
        val go = GraphOptimizer(f1, f2, f3, f4, mode.graphOptVerbose)
        val graph = gb.buildGraph(unit)
        outputBuilder ++= graph.toString()
        outputBuilder ++= "\n\nPromoted ------------------------------------\n"
        val graph2 = go.simplifyProgram(graph)
        val graph3 = go.activeAnalyze(graph2)
        val graph4 = go.recBoundaryAnalyze(graph3)
        outputBuilder ++= graph4.toString()
        if (mode.graphInterp)
          outputBuilder ++= "\n\nInterpreted ------------------------------\n"
          outputBuilder ++= GraphInterpreter(mode.graphOptVerbose).interpret(graph4)
          outputBuilder ++= "\n"
       
        var changed = true
        var g = graph4
        val fuel_limit = 20
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

        if (mode.graphInterp)
          outputBuilder ++= "\n\nInterpreted ------------------------------\n"
          outputBuilder ++= GraphInterpreter(mode.graphOptVerbose).interpret(g)
          outputBuilder ++= "\n"

        outputBuilder ++= s"\n\nFuel used: ${fuel_limit - fuel}"

        if (fuel == 0)
          throw optimizer.GraphOptimizingError("Fuel exhausted")

      catch
        case err: Exception =>
          outputBuilder ++= s"\nGraphOpt failed: ${err.getMessage()}"
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
