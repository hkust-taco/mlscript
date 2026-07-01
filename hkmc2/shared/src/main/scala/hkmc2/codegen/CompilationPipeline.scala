package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.Config
import hkmc2.semantics.Elaborator.{Ctx, State}
import hkmc2.semantics.SymbolPrinter
import hkmc2.utils.TL

class CompilationPipeline(using Config, Raise, State, Ctx, SymbolPrinter):
  
  case class CompilationPass(name: Str, transform: Program => Program)
  
  def preOptimizeHook(prog: Program): Program =
    prog
  
  def passHook(pass: CompilationPass, before: Program, after: Program): Program =
    after
  
  private def blockPass(pass: Block => Block)(prog: Program): Program =
    val blk = pass(prog.main)
    if blk is prog.main then prog else Program(prog.imports, blk)
  
  def run(prog: Program, printer: Program => Str, symbolsToPreserve: Set[BoundSymbol], otl: TL)(using TL): Program =
    val allPasses = List(
      CompilationPass("LambdaRewriter", LambdaRewriter.desugar),
      CompilationPass("Deforest", prog =>
        val outterTl = tl
        config.deforest match
          case None => prog
          case Some(dCfg) =>
            flowAnalysis.FlowAnalysis.mkTraceLogger(dCfg.config, "deforest > ", outterTl).givenIn:
              deforest.Deforest(prog)),
      CompilationPass("EtaExpansion", EtaExpansion.apply),
      CompilationPass("Lifter", prog =>
        if config.liftDefns.isDefined then
          blockPass(Lifter(_).transform)(prog)
        else prog),
      CompilationPass("HandlerLowering", prog =>
        config.effectHandlers.fold(prog): opt =>
          HandlerLowering(new HandlerPaths, opt).translateProgram(prog)),
      CompilationPass("Flattening", blockPass(_.flattened)),
      CompilationPass("BufferableTransform", BufferableTransform().transform),
      CompilationPass("MergeMatchArmTransformer", MergeMatchArmTransformer.applyProgram),
      CompilationPass("FirstClassFunctionTransformer", prog =>
        if config.funcToCls then
          blockPass(blk => Lifter(FirstClassFunctionTransformer().transform(blk)).transform)(prog)
        else prog),
      CompilationPass("ClassParamFlattener", ClassParamFlattener.apply),
      CompilationPass("ReflectionInstrumenter", ReflectionInstrumenter(using summon).apply),
      CompilationPass("TailRecOpt", TailRecOpt().transform),
      CompilationPass("PreOptimizeHook", preOptimizeHook),
      CompilationPass("WorkerWrapper", WorkerWrapper(symbolsToPreserve, otl, printer)),
      CompilationPass("BlockSimplifier", BlockSimplifier(symbolsToPreserve, otl, printer).apply),
      CompilationPass("DeadParamElim", otl.givenIn(DeadParamElim.apply)),
    )
    allPasses.foldLeft(prog): (before, pass) =>
      val after = pass.transform(before)
      passHook(pass, before, after)
