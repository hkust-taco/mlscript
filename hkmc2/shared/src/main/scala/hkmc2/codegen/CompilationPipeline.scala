package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.Config
import hkmc2.semantics.Elaborator.{Ctx, State}
import hkmc2.semantics.SymbolPrinter
import hkmc2.utils.TL

class CompilationPipeline(using Config, Raise, State, Ctx, SymbolPrinter):
  
  def preOptimizeHook(prog: Program) = ()
  
  def passHook(passName: Str, before: Program, after: Program) = ()
  
  private inline def blockPass(inline pass: Block => Block)(prog: Program): Program =
    val blk = pass(prog.main)
    if blk is prog.main then prog else Program(prog.imports, blk)
  
  def run(prog: Program, printer: Program => Str, symbolsToPreserve: Set[BoundSymbol], otl: TL)(using TL): Program =
    var result = prog
    inline def runPass(passName: Str)(inline transform: Program => Program) =
      val before = result
      result = transform(before)
      passHook(passName, before, result)
    
    runPass("LambdaRewriter")(LambdaRewriter.desugar)
    runPass("Deforest"): prog =>
      val outterTl = tl
      config.deforest match
        case None => prog
        case Some(dCfg) =>
          flowAnalysis.FlowAnalysis.mkTraceLogger(dCfg.config, "deforest > ", outterTl).givenIn:
            deforest.Deforest(prog)
    runPass("EtaExpansion")(EtaExpansion.apply)
    runPass("Lifter"): prog =>
      if config.liftDefns.isDefined then
        blockPass(Lifter(_).transform)(prog)
      else prog
    runPass("HandlerLowering"): prog =>
      config.effectHandlers.fold(prog): opt =>
        HandlerLowering(new HandlerPaths, opt).translateProgram(prog)
    runPass("Flattening")(blockPass(_.flattened))
    runPass("BufferableTransform")(BufferableTransform().transform)
    runPass("MergeMatchArmTransformer")(MergeMatchArmTransformer.applyProgram)
    runPass("FirstClassFunctionTransformer"): prog =>
      if config.funcToCls then
        blockPass(FirstClassFunctionTransformer().transform(_))(prog)
      else prog
    runPass("Lifter"): prog =>
      if config.funcToCls then
        blockPass(Lifter(_).transform)(prog)
      else prog
    runPass("ClassParamFlattener")(ClassParamFlattener.apply)
    runPass("ReflectionInstrumenter")(ReflectionInstrumenter(using summon).apply)
    runPass("TailRecOpt")(TailRecOpt().transform)
    preOptimizeHook(result)
    runPass("WorkerWrapper")(WorkerWrapper(symbolsToPreserve, otl, printer))
    runPass("BlockSimplifier")(BlockSimplifier(symbolsToPreserve, otl, printer).apply)
    runPass("DeadParamElim")(otl.givenIn(DeadParamElim.apply))
    
    result
