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
  
  private inline def blockPass(prog: Program, inline pass: Block => Block): Program =
    val blk = pass(prog.main)
    if blk is prog.main then prog else Program(prog.imports, blk)
  
  def run(prog: Program, printer: Program => Str, symbolsToPreserve: Set[BoundSymbol], otl: TL)(using TL): Program =
    
    var result = prog
    var lastPassProg = prog
    def hook(passName: Str) =
      passHook(passName, lastPassProg, result)
      lastPassProg = result
    
    result = LambdaRewriter.desugar(result)
    hook("LambdaRewriter")
    
    result =
      val outterTl = tl
      config.deforest match
        case None => result
        case Some(dCfg) =>
          flowAnalysis.FlowAnalysis.mkTraceLogger(dCfg.config, "deforest > ", outterTl).givenIn:
            deforest.Deforest(result)
    hook("Deforest")
    
    result = EtaExpansion(result)
    hook("EtaExpansion")
    
    if config.liftDefns.isDefined then
      result = blockPass(result, Lifter(_).transform)
    hook("Lifter")
    
    result = config.effectHandlers.fold(result): opt =>
      HandlerLowering(new HandlerPaths, opt).translateProgram(result)
    hook("HandlerLowering")
    
    result = blockPass(result, _.flattened)
    hook("Flattening")
    
    result = BufferableTransform().transform(result)
    hook("BufferableTransform")
    
    result = blockPass(result, MergeMatchArmTransformer.applyBlock(_))
    hook("MergeMatchArmTransformer")
    
    if config.funcToCls then
      result = blockPass(result, FirstClassFunctionTransformer().transform(_))
      hook("FirstClassFunctionTransformer")
      result = blockPass(result, Lifter(_).transform)
      hook("Lifter")
    
    result = ClassParamFlattener(result)
    hook("ClassParamFlattener")
    
    result = ReflectionInstrumenter(using summon).apply(result)
    hook("ReflectionInstrumenter")
    
    if config.tailRecOpt then
      result = TailRecOpt().transform(result)
      hook("TailRecOpt")
    
    preOptimizeHook(result)
    
    result = WorkerWrapper(symbolsToPreserve, otl, printer)(result)
    hook("WorkerWrapper")
    
    result = BlockSimplifier(symbolsToPreserve, otl, printer)(result)
    hook("BlockSimplifier")
    
    result = otl.givenIn(DeadParamElim(result))
    hook("DeadParamElim")
    
    result
