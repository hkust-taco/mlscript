package mlscript.compiler


import mlscript.utils.shorthands._
import mlscript.compiler.ir._
import scala.collection.mutable.StringBuilder
import mlscript.{DiffTests, ModeType, TypingUnit}
import mlscript.compiler.ir.{Fresh, FreshInt, Builder}
import mlscript.compiler.codegen.cpp.{CppCodeGen, CppCompilerHost}
import mlscript.compiler.optimizer.OptimizingError
import mlscript.Diagnostic

class IRDiffTestCompiler extends DiffTests {
  import IRDiffTestCompiler.*
  def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) = {
    val p = new java.io.PrintWriter(f)
    try { op(p) } finally { p.close() }
  }
  override def postProcess(mode: ModeType, basePath: List[Str], testName: Str, unit: TypingUnit, output: Str => Unit, raise: Diagnostic => Unit): (List[Str], Option[TypingUnit]) = 
    val outputBuilder = StringBuilder()
    if (mode.useIR || mode.irVerbose)
      try
        output("\n\nIR:")
        val (fresh, freshFnId, freshClassId, freshTag) = (Fresh(), FreshInt(), FreshInt(), FreshInt())
        val gb = Builder(fresh, freshFnId, freshClassId, freshTag, mode.irVerbose)
        val graph = gb.buildGraph(unit)
        output(graph.toString())
        output("\nPromoted:")
        output(graph.toString())
        var interp_result: Opt[Str] = None
        if (mode.interpIR)
          output("\nInterpreted:")
          //val ir = Interpreter(mode.irVerbose).interpret(graph)
          //interp_result = Some(ir)
          //output(ir)
        if (mode.genCpp)
          val cpp = CppCodeGen().codegen(graph)
          if (mode.showCpp)
            output("\nCpp:")
            output(cpp.toDocument.print)
          if (mode.writeCpp)
            printToFile(java.io.File(s"compiler/shared/test/diff-ir/cpp/${testName}.cpp")) { p =>
              p.println(cpp.toDocument.print)
            }
          if (mode.runCpp)
            val auxPath = os.pwd/"compiler"/"shared"/"test"/"diff-ir"/"cpp"
            val cppHost = CppCompilerHost(auxPath.toString())
            if !cppHost.ready then
              output("\nCpp Compilation Failed: Cpp compiler or GNU Make not found")
            else
              output("\n")
              cppHost.compileAndRun(cpp.toDocument.print, output)

        // if (mode.irOpt)
        //   val go = Optimizer(fresh, freshFnId, freshClassId, freshTag, mode.irVerbose)
        //   var changed = true
        //   var g = graph
        //   var fuel = mode.irOptFuel
        //   while (changed && fuel > 0)
        //     val new_g = go.optimize(g)
        //     changed = g != new_g
        //     g = new_g
        //     if (changed)
        //       output("\nOptimized:")
        //       output(new_g.toString())
        //     fuel -= 1

        //   if (mode.interpIR)
        //     output("\nInterpreted:")
        //     val ir = Interpreter(mode.irVerbose).interpret(g)
        //     output(ir)
        //     if ir != interp_result.get then
        //       throw optimizer.OptimizingError("Interpreted result changed after optimization")
        //     output("")

        //   output(s"\nFuel used: ${mode.irOptFuel - fuel}")

        //   if (fuel == 0)
        //     throw optimizer.OptimizingError("Fuel exhausted")

      catch
        case err: OptimizingError =>
          output(s"\nOpt Failed: ${err.getMessage()}")
          output("\n" ++ err.getStackTrace().map(_.toString()).mkString("\n"))
        case err: Exception =>
          output(s"\nIR Processing Failed: ${err.getMessage()}")
          output("\n" ++ err.getStackTrace().map(_.toString()).mkString("\n"))
        case err: StackOverflowError =>
          output(s"\nIR Processing Failed: ${err.getMessage()}")
          output("\n" ++ err.getStackTrace().map(_.toString()).mkString("\n"))
      
    (outputBuilder.toString().linesIterator.toList, None)
  
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
