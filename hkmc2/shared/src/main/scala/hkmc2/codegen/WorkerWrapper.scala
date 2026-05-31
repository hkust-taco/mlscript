package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import semantics.Elaborator.State


/** Introduces flat worker functions for curried functions.
  *
  * The wrapper keeps the original calling convention and is marked `@inline`,
  * so direct saturated calls can be rewritten by the existing inliner to call
  * the worker. For tiny bodies, creating a worker would only add noise: the
  * wrapper body would inline the worker immediately under the stricter
  * `altSmallThreshold`, so we mark the original function inline directly.
  */
class WorkerWrapper
    (_symbolsToPreserve: Set[BoundSymbol], tl: TL, printer: Program => Str)
    (using DebugPrinter, State, Config, Raise)
  extends BlockTransformer(SymbolSubst.Id):
  import tl.*
  
  private def withInline(annotations: Ls[Annot]): Ls[Annot] =
    if annotations.contains(Annot.Inline) then annotations else Annot.Inline :: annotations
  
  private def withoutInline(annotations: Ls[Annot]): Ls[Annot] =
    annotations.filterNot(_ == Annot.Inline)
  
  private def isPlainParamList(params: ParamList): Bool =
    params.flags == ParamListFlags.empty && params.restParam.isEmpty
  
  private def canUncurry(fun: FunDefn): Bool =
    fun.owner.isEmpty && fun.params.lengthCompare(1) > 0 && fun.params.forall(isPlainParamList)
  
  private def isBelowAltInlineThreshold(body: Block): Bool =
    config.inlining.exists: cfg =>
      body.size <= cfg.altSmallThreshold
  
  private def freshParam(param: Param, mapping: collection.mutable.Map[Symbol, Symbol]): Param =
    val freshSym = new VarSymbol(param.sym.id)
    mapping(param.sym) = freshSym
    Param(param.flags, freshSym, param.sign, param.modulefulness).withSignTypeOf(param)
  
  private def flattenParams(params: Ls[ParamList]): (ParamList, Map[Symbol, Symbol]) =
    val mapping = collection.mutable.LinkedHashMap.empty[Symbol, Symbol]
    val flatParams = params.flatMap: params =>
      params.params.map(freshParam(_, mapping))
    PlainParamList(flatParams) -> mapping.toMap
  
  private def rewriteParams(body: Block, mapping: Map[Symbol, Symbol]): Block =
    val subst = new SymbolSubst:
      override def mapVarSym(sym: VarSymbol): VarSymbol =
        mapping.get(sym) match
        case S(mapped: VarSymbol) => mapped
        case _ => sym
    BlockTransformer(subst).applyBlock(body)
  
  private def mkWorkerWrapper(fun: FunDefn, body: Block, rest: Block): Block =
    val (workerParams, paramMapping) = flattenParams(fun.params)
    val workerSym = new BlockMemberSymbol(s"${fun.sym.nme}$$worker", Nil, nameIsMeaningful = true)
    val workerBody = rewriteParams(body, paramMapping)
    val worker = FunDefn.withFreshSymbol(
      N,
      workerSym,
      workerParams :: Nil,
      workerBody,
    )(fun.configOverride, withoutInline(fun.annotations))
    val workerArgs = fun.params.flatMap(_.params).map: param =>
      Arg(N, param.sym.asSimpleRef)
    val wrapperBody = Return(
      Call(worker.asPath, workerArgs ne_:: Nil)(isMlsFun = true, mayRaiseEffects = true, explicitTailCall = false),
    )
    val wrapper = FunDefn(
      fun.owner,
      fun.sym,
      fun.dSym,
      fun.params,
      wrapperBody,
    )(fun.configOverride, withInline(fun.annotations))
    log(s"▶ Worker-wrapper: ${fun.dSym.showDbg} -> ${worker.dSym.showDbg}")
    Scoped(Set.single(worker.sym), Define(wrapper, Define(worker, rest)))
  
  private def mkInlineOnly(fun: FunDefn, body: Block): FunDefn =
    val annotations = withInline(fun.annotations)
    if (annotations is fun.annotations) && (body is fun.body) then fun
    else FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, body)(fun.configOverride, annotations)
  
  override def applyProgram(prog: Program): Program =
    val res = super.applyProgram(prog)
    if res isnt prog then log("▶ Worker-wrapper:\n" + printer(res))
    res
  
  override def applyBlock(block: Block): Block = block match
    case Define(fun: FunDefn, rest) if canUncurry(fun) =>
      val body = applyFunBodyLikeBlock(fun.body)
      val rest2 = applySubBlock(rest)
      if isBelowAltInlineThreshold(body) then
        val fun2 = mkInlineOnly(fun, body)
        if (fun2 is fun) && (rest2 is rest) then block else Define(fun2, rest2)
      else
        mkWorkerWrapper(fun, body, rest2)
    case _ =>
      super.applyBlock(block)
  
end WorkerWrapper

object WorkerWrapper:
  def apply(symbolsToPreserve: Set[BoundSymbol], tl: TL, printer: Program => Str)(p: Program)
      (using DebugPrinter, State, Config, Raise): Program =
    if config.inlining.isEmpty then p
    else (new WorkerWrapper(symbolsToPreserve, tl, printer)).applyProgram(p)
