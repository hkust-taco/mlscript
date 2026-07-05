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
    preOptimizeHook(result)
    
    // * We run this pass here first, before inlining so that the @tailrec/@tailcall annotations
    // * can be properly checked.
    runPass("TailRecOpt")(TailRecOpt(true).transform)
    
    runPass("WorkerWrapper")(WorkerWrapper(symbolsToPreserve, otl, printer))
    
    // * First simplification pass
    runPass("BlockSimplifier 1")(BlockSimplifier(symbolsToPreserve, otl, printer).apply)
    
    runPass("DeadParamElim")(otl.givenIn(DeadParamElim.apply))
    
    // * More tailrec opportunities might be revealed after WorkerWrapper + BlockSimplifier,
    // * which might bring split curried recursive calls (such as those coming out of Deforest + EtaExpansion)
    // * into proper tail positions.
    runPass("TailRecOpt")(TailRecOpt(false).transform)
    
    // * Final simplification pass
    runPass("BlockSimplifier 2")(BlockSimplifier(symbolsToPreserve, otl, printer).apply)
    
    result
