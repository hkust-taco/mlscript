package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import document.*
import codegen.Block
import codegen.llir.*
import codegen.cpp.*
import hkmc2.syntax.Tree.Ident
import hkmc2.codegen.Path
import hkmc2.semantics.Term.Blk
import hkmc2.codegen.llir.Fresh
import hkmc2.utils.Scope
import hkmc2.codegen.llir.Ctx
import hkmc2.codegen.llir._

abstract class LlirDiffMaker extends BbmlDiffMaker:
  val llir = NullaryCommand("llir")
  val cpp = NullaryCommand("cpp")
  val sllir = NullaryCommand("sllir")
  val scpp = NullaryCommand("scpp")
  val rcpp = NullaryCommand("rcpp")
  val intl = NullaryCommand("intl")
  val wcpp = Command[Str]("wcpp", false)(x => x.stripLeading())

  def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) =
    val p = new java.io.PrintWriter(f)
    try { op(p) } finally { p.close() }

  override def processTerm(trm: Blk, inImport: Bool)(using Raise): Unit = 
    super.processTerm(trm, inImport)
    if llir.isSet then
      val low = ltl.givenIn:
        codegen.Lowering()
      val le = low.program(trm)
      given Scope = Scope.empty
      val fresh = Fresh()
      val fuid = FreshInt()
      val cuid = FreshInt()
      val llb = LlirBuilder(tl)(fresh, fuid, cuid)
      given Ctx = Ctx.empty
      try
        val llirProg = llb.bProg(le)
        if sllir.isSet then
          output("LLIR:")
          output(llirProg.show())
        if cpp.isSet || scpp.isSet || rcpp.isSet || wcpp.isSet then
          val cpp = codegen.cpp.CppCodeGen.codegen(llirProg)
          if scpp.isSet then
            output("\nCpp:")
            output(cpp.toDocument.toString)
          val auxPath =  os.Path(rootPath) / "hkmc2"/"shared"/"src"/"test"/"mlscript-compile"/"cpp"
          if wcpp.isSet then
            printToFile(java.io.File((auxPath / s"${wcpp.get.get}.cpp").toString)):
               p => p.println(cpp.toDocument.toString)
          if rcpp.isSet then
            val cppHost = CppCompilerHost(auxPath.toString, output.apply)
            if !cppHost.ready then
              output("\nCpp Compilation Failed: Cpp compiler or GNU Make not found")
            else
              output("\n")
              cppHost.compileAndRun(cpp.toDocument.toString)
        if intl.isSet then
          val intr = codegen.llir.Interpreter(verbose = true)
          output("\nInterpreted:")
          output(intr.interpret(llirProg))
      catch
        case e: LowLevelIRError =>
          output("Stopped due to an error during the Llir generation")

