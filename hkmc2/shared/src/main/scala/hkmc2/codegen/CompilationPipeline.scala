package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.Config
import hkmc2.semantics.Elaborator.{Ctx, State}
import hkmc2.semantics.SymbolPrinter
import hkmc2.utils.TL

class CompilationPipeline(using Config, Raise, State, Ctx, SymbolPrinter):
  
  def preOptimizeHook(prog: Program): Program =
    prog
  
  def run(prog: Program, printer: Program => Str, symbolsToPreserve: Set[BoundSymbol], otl: TL)(using TL): Program =
    
    var result = prog
    
    result = LambdaRewriter.desugar(result)
    
    result =
      val outterTl = tl
      config.deforest match
        case None => result
        case Some(dCfg) =>
          flowAnalysis.FlowAnalysis.mkTraceLogger(dCfg.config, "deforest > ", outterTl).givenIn:
            deforest.Deforest(result)
    
    result = EtaExpansion(result)
    
    if config.liftDefns.isDefined then
      result = Program(result.imports, Lifter(result.main).transform)
    
    result = config.effectHandlers.fold(result): opt =>
      HandlerLowering(new HandlerPaths, opt).translateProgram(result)
    
    result = Program(result.imports, result.main.flattened)
    
    result = BufferableTransform().transform(result)
    
    // * TODO[Anto]: Can we remove MergeMatchArmTransformer? Seems no longer necessary
    result = Program(result.imports, MergeMatchArmTransformer.applyBlock(result.main))
    
    if config.funcToCls then
      result = Program(result.imports, Lifter(FirstClassFunctionTransformer().transform(result.main)).transform)
    
    result = ClassParamFlattener(result)
    
    result = ReflectionInstrumenter(using summon).apply(result)
    
    if config.tailRecOpt then
      result = TailRecOpt().transform(result)
    
    result = preOptimizeHook(result)
    
    if !summon[Config].noOpt then
      result = WorkerWrapper(symbolsToPreserve, otl, printer)(result)
      result = BlockSimplifier(symbolsToPreserve, otl, printer)(result)
      result = otl.givenIn(DeadParamElim(result))
    
    result
