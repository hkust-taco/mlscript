package mlscript.compiler


import mlscript.utils.shorthands._
import mlscript.compiler.ir._
import scala.collection.mutable.StringBuilder
import mlscript.{DiffTests, ModeType, TypingUnit}
import mlscript.compiler.ir.{Fresh, FreshInt, Builder}
import mlscript.compiler.codegen.cpp._
import mlscript.Diagnostic
import mlscript.compiler.optimizer.TailRecOpt

import IRDiffTestCompiler.*

class IRDiffTestCompiler extends DiffTests(State) {
  def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) = {
    val p = new java.io.PrintWriter(f)
    try { op(p) } finally { p.close() }
  }

  override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit, output: Str => Unit, raise: Diagnostic => Unit): (List[Str], Option[TypingUnit]) = 
    val outputBuilder = StringBuilder()
    if (mode.useIR || mode.irVerbose)
      try
        val (fresh, freshFnId, freshClassId, freshTag) = (Fresh(), FreshInt(), FreshInt(), FreshInt())
        val gb = Builder(fresh, freshFnId, freshClassId, freshTag, raise, mode.irVerbose)
        var graph = gb.buildGraph(unit)

        if mode.noTailRecOpt then
          output("\n\nIR:")
          output(graph.toString())
        else
          val tailRecOpt = new TailRecOpt(freshFnId, freshClassId, freshTag, raise)
          val (g, comps) = tailRecOpt.run_debug(graph)
          output("\n\nStrongly Connected Tail Calls:")
          output(comps.toString)
          graph = g
          output(graph.toString())
        output("\nPromoted:")
        output(graph.toString)
        var interp_result: Opt[Str] = None
        if (mode.interpIR)
          output("\nInterpreted:")
          val ir = Interpreter(mode.irVerbose).interpret(graph)
          interp_result = Some(ir)
          output(ir)
        if (mode.genCpp)
          val cpp = codegen(graph)
          if (mode.showCpp)
            output("\nCpp:")
            output(cpp.toDocument.print)
          if (mode.writeCpp)
            printToFile(java.io.File(s"compiler/shared/test/diff-ir/cpp/${testName}.cpp")) { p =>
              p.println(cpp.toDocument.print)
            }
          if (mode.runCpp)
            val auxPath = os.pwd/"compiler"/"shared"/"test"/"diff-ir"/"cpp"
            val cppHost = CppCompilerHost(auxPath.toString)
            if !cppHost.ready then
              output("\nCpp Compilation Failed: Cpp compiler or GNU Make not found")
            else
              output("\n")
              cppHost.compileAndRun(cpp.toDocument.print, output)
      catch
        case err: Exception =>
          output(s"\nIR Processing Failed: ${err.getMessage()}")
          output("\n" ++ err.getStackTrace().mkString("\n"))
        case err: StackOverflowError =>
          output(s"\nIR Processing Failed: ${err.getMessage()}")
          output("\n" ++ err.getStackTrace().mkString("\n"))
      
    (outputBuilder.toString.linesIterator.toList, None)
  
}

object IRDiffTestCompiler {
  
  lazy val State =
    new DiffTests.State(DiffTests.pwd/"compiler"/"shared"/"test"/"diff-ir")
  
}
