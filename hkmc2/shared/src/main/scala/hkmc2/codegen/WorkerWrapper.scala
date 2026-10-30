package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
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
  * Original `@noInline` and `@generator` annotations are transferred to the
  * worker, while the forwarding wrapper remains inlineable.
  */
class WorkerWrapper
    (tl: TL, printer: Program => Str)
    (using DebugPrinter, State, Config, Raise)
  extends BlockTransformer(SymbolSubst.Id):
  import tl.*
  
  // Collect replacements while splitting functions, then substitute across the whole
  // program so forward references and recursive calls use the direct-result wrapper.
  private val wrapperSymbols = collection.mutable.Map.empty[TermSymbol, TermSymbol]

  private def withInline(annotations: Ls[Annot]): Ls[Annot] =
    if annotations.exists(_.isInstanceOf[Annot.Inline]) then annotations else Annot.Inline()(N) :: annotations
  
  private def withoutInline(annotations: Ls[Annot]): Ls[Annot] =
    annotations.filterNot(_.isInstanceOf[Annot.Inline])
  
  // * Optional parameters are excluded because uncurrying concatenates the parameter lists,
  // * so the arguments of a later list would be assigned to the omitted optional parameters.
  // * TODO: support this once we normalize known-call sites in the future.
  private def isPlainParamList(params: LoweredParamList): Bool =
    params.flags == ParamListFlags.empty && params.restParam.isEmpty && !params.hasOptParams
  
  private def effectiveConfig(fun: FunDefn): Config =
    fun.configOverride.getOrElse(config)

  private def canUncurry(fun: FunDefn): Bool =
    effectiveConfig(fun).inlining.isDefined &&
      fun.owner.isEmpty && fun.params.lengthCompare(1) > 0 && fun.params.forall(isPlainParamList)
  
  private def isBelowAltInlineThreshold(fun: FunDefn, body: Block): Bool =
    effectiveConfig(fun).inlining.exists: cfg =>
      body.size <= cfg.altSmallThreshold
  
  private def freshParam(param: Param, mapping: collection.mutable.Map[Symbol, Symbol]): Param =
    val freshSym = new VarSymbol(param.sym.id, erasedType = param.sym.erasedType, mut = param.sym.mut)
    mapping(param.sym) = freshSym
    Param(param.flags, freshSym, param.sign, param.modulefulness)(param.toLoc).withSignTypeOf(param)
  
  private def flattenParams(params: Ls[LoweredParamList]): (LoweredParamList, Map[Symbol, Symbol]) =
    val mapping = collection.mutable.LinkedHashMap.empty[Symbol, Symbol]
    val flatParams = params.flatMap: params =>
      params.params.map(freshParam(_, mapping))
    LoweredParamList.plain(flatParams)(Loc(params)) -> mapping.toMap
  
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
    val workerSignature = FunDefn.Signature.fromParams(workerParams :: Nil, fun.signature.result)
    val workerDSym = TermSymbol(syntax.Fun, N, syntax.Tree.Ident(workerSym.nme))
    workerSym.tsym = S(workerDSym)
    val worker = FunDefn(
      N,
      workerSym,
      workerDSym,
      workerSignature,
      workerBody,
    )(fun.configOverride, withoutInline(fun.annotations))
    val workerArgs = fun.params.flatMap(_.params).map: param =>
      Arg(N, param.sym.asSimpleRef)
    val wrapperBody = Return(
      Call(worker.asPath, workerArgs ne_:: Nil)(CallMetadata.mlsFunWithEffect, N),
    )
    // The generator body now belongs to the worker. The wrapper returns its Iterator
    // directly, while the source symbol keeps the payload for later source cloning.
    val wrapperAnnotations = withInline(fun.annotations.filter:
      case Annot.NoInline() | Annot.Generator() => false
      case _ => true)
    val wrapperSignature =
      if fun.generator then FunDefn.Signature.fromParams(fun.params,
        ErasedResult.fromAnnotations(fun.signature.erasure.ret, wrapperAnnotations))
      else fun.signature
    val wrapperDSym =
      if wrapperSignature.erasure isnt fun.signature.erasure then
        val copy = SymbolRefresher.copyTermSymbol(fun.dSym, fun.owner, S(wrapperSignature.erasure))
        assert(!wrapperSymbols.contains(fun.dSym), "A generator symbol must have only one definition")
        wrapperSymbols(fun.dSym) = copy
        copy
      else fun.dSym
    val wrapper = FunDefn(
      fun.owner,
      fun.sym,
      wrapperDSym,
      wrapperSignature,
      wrapperBody,
    )(fun.configOverride, wrapperAnnotations)
    log(dbg"▶ Worker-wrapper: ${fun.dSym.showDbg} -> ${worker.dSym.showDbg}")
    Scoped(Set.single(worker.sym), Define(wrapper, Define(worker, rest)))
  
  private def mkInlineOnly(fun: FunDefn, body: Block): FunDefn =
    val annotations = withInline(fun.annotations)
    if (annotations is fun.annotations) && (body is fun.body) then fun
    else fun.copy(fun.owner, fun.sym, fun.dSym, fun.signature, body)(fun.configOverride, annotations)
  
  override def applyProgram(prog: Program): Program =
    val transformed = super.applyProgram(prog)
    val replacements = wrapperSymbols.toMap
    wrapperSymbols.clear()
    val res = if replacements.isEmpty then transformed else
      val subst = new SymbolSubst:
        override def mapTermSym(sym: TermSymbol): TermSymbol = replacements.getOrElse(sym, sym)
      BlockTransformer(subst).applyProgram(transformed)
    if res isnt prog then log("▶ Worker-wrapper:\n" + printer(res))
    res
  
  override def applyBlock(block: Block): Block = block match
    case Define(fun: FunDefn, rest) if canUncurry(fun) =>
      val body = applyFunBodyLikeBlock(fun.body)
      val rest2 = applySubBlock(rest)
      if isBelowAltInlineThreshold(fun, body) && !fun.noInline then
        val fun2 = mkInlineOnly(fun, body)
        if (fun2 is fun) && (rest2 is rest) then block else Define(fun2, rest2)
      else
        mkWorkerWrapper(fun, body, rest2)
    case _ =>
      super.applyBlock(block)
  
end WorkerWrapper

object WorkerWrapper:
  def apply(symbolsToPreserve: Set[ScopedSymbol], tl: TL, printer: Program => Str)(p: Program)
      (using DebugPrinter, State, Config, Raise): Program =
    (new WorkerWrapper(tl, printer)).applyProgram(p)
