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
import hkmc2.utils.Scope
import hkmc2.codegen.llir._
import hkmc2.codegen.cpp._
import hkmc2.semantics.Elaborator
import scala.collection.mutable.ListBuffer

abstract class LlirDiffMaker extends BbmlDiffMaker:
  val llir = NullaryCommand("llir")
  val sllir = NullaryCommand("sllir")
  val intl = NullaryCommand("intl")
  val lprelude = NullaryCommand("lpre")

  // C++ codegen generation commands for individual blocks
  val cpp = NullaryCommand("cpp")
  val scpp = NullaryCommand("scpp")
  val rcpp = NullaryCommand("rcpp")
  val wcpp = Command[Str]("wcpp", false)(x => x.stripLeading())

  // C++ codegen generation commands for the whole program
  val wholeCpp = NullaryCommand("wholeCpp")
  val sWholeCpp = NullaryCommand("showWholeCpp")
  val rWholeCpp = NullaryCommand("runWholeCpp")
  val wWholeCpp = Command[Str]("writeWholeCpp", false)(x => x.stripLeading())

  def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) =
    val p = new java.io.PrintWriter(f)
    try { op(p) } finally { p.close() }

  given Elaborator.Ctx = curCtx
  
  object Llir: // Avoid polluting the namespace
    val freshId = FreshInt()
    var ctx = codegen.llir.Ctx.empty
    val scope = Scope.empty
    val wholeProg = ListBuffer.empty[Program]
  import Llir.*
  
  def mkWholeProgram: Program =
    if wholeProg.length == 0 then
      throw new Exception("No program to make")
    else
      Program(
        classes = wholeProg.iterator.flatMap(_.classes).toSet,
        defs = wholeProg.iterator.flatMap(_.defs).toSet,
        entry = wholeProg.last.entry
      )

  override def processTerm(trm: Blk, inImport: Bool)(using Config, Raise): Unit = 
    super.processTerm(trm, inImport)
    if llir.isSet then
      val low = ltl.givenIn:
        codegen.Lowering()
      var le = low.program(trm)
      given Scope = scope
      given Ctx = ctx
      val llb = LlirBuilder(tl, freshId)
      try
        val (llirProg, ctx2) = llb.bProg(le)
        ctx = ctx2
        wholeProg += llirProg
        if sllir.isSet && !silent.isSet then
          output("LLIR:")
          if debug.isSet then
            output(LlirDebugPrinter.mkDocument(llirProg).toString)
          else
            output(LlirPrinter(using summon[Raise], Scope.empty).mkDocument(llirProg).toString)
        def cppGen(name: String, prog: Program, gen: Bool, show: Bool, run: Bool, write: Opt[Str]): Unit =
          tl.log(s"Generating $name")
          if gen || show || run || write.isDefined then
            val cpp = CppCodeGen(ctx.builtinSym.hiddenClasses, tl).codegen(prog)
            if show then
              output(s"\n$name:")
              output(cpp.toDocument.toString)
            val rPath = os.Path(rootPath)
            val auxPath = rPath/"hkmc2"/"shared"/"src"/"test"/"mlscript-compile"/"cpp"
            if write.isDefined then
              printToFile(java.io.File((auxPath / s"${write.get}").toString)):
                p => p.println(cpp.toDocument.toString)
            if run then 
              val cppHost = CppCompilerHost(auxPath.toString, output.apply)
              if !cppHost.ready then
                output("\nCpp Compilation Failed: Cpp compiler or GNU Make not found")
              else if !silent.isSet then
                output("\n")
                cppHost.compileAndRun(cpp.toDocument.toString)
        cppGen("Cpp", llirProg, 
          cpp.isSet, scpp.isSet, rcpp.isSet, wcpp.get)
        cppGen("WholeProgramCpp", mkWholeProgram,
          wholeCpp.isSet, sWholeCpp.isSet, rWholeCpp.isSet, wWholeCpp.get)
        if intl.isSet then
          val intr = codegen.llir.Interpreter(tl)
          output("\nInterpreted:")
          output(intr.interpret(llirProg))
      catch
        case e: LowLevelIRError =>
          output("Stopped due to an error during the Llir generation")
