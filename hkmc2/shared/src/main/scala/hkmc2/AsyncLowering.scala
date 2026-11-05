package hkmc2
package codegen

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.boundary
import sourcecode.{ Line, FileName, Name }

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.utils.SymbolSubst
import hkmc2.Message.MessageContext

import syntax.{Literal, Tree}
import semantics.*
import semantics.Elaborator.ctx
import semantics.Elaborator.State
import hkmc2.Config.EffectHandlers


class AsyncLowering(using TL, Raise, Elaborator.State, Elaborator.Ctx, Config):
  
  private type Wrapper = (symbol: TermSymbol, signature: FunDefn.Signature)
  
  private class Rewriter(wrappers: collection.Map[TermSymbol, Wrapper]) extends BlockTransformer(new SymbolSubst:
    override def mapTermSym(sym: TermSymbol): TermSymbol = wrappers.get(sym).fold(sym)(_.symbol)):
    var inAsyncFun: Bool = false
    
    inline def wrapAwait[T](innerAllowAwait: Bool)(inline thunk: => T): T =
      val saved = inAsyncFun
      inAsyncFun = innerAllowAwait
      val result = thunk
      inAsyncFun = saved
      result
    
    override def applyFunDefn(fun: FunDefn): FunDefn =
      if !fun.async then return wrapAwait(false)(super.applyFunDefn(fun))
      val bodySym = BlockMemberSymbol(fun.sym.nme + "$async", Nil, fun.sym.nameIsMeaningful)
      val bodyDsym = TermSymbol(syntax.Fun, N, fun.dSym.id)
      val noAsync = fun.annotations.filterNot(_.isInstanceOf[Annot.Async])
      // Only the wrapper has the source argument lists; their affine annotations
      // cannot describe the zero-argument thunk.
      val bodyAnnotations = noAsync.filterNot(_.isInstanceOf[Annot.Affine])
      val bodySignature = FunDefn.Signature.fromParams(
        LoweredParamList.plain(Nil)(N) :: Nil,
        ErasedResult.fromAnnotations(fun.signature.result.bodyType, noAsync))
      // The thunk stays inside the wrapper, so it shares the wrapper's parameter
      // bindings and lexical receivers. Handler lowering saved the wrapper's
      // arguments and receiver for resumption; reentering it creates a new thunk
      // whose state machine restores the suspended locals.
      val body = FunDefn(N, bodySym, bodyDsym, bodySignature,
        wrapAwait(true)(applyFunBodyLikeBlock(fun.body)))(fun.configOverride, bodyAnnotations)
      val wrapper = wrappers(fun.dSym)
      val wrapped = Call(Value.SimpleRef(State.runtimeSymbol)(N).selSN("toJsAsync"),
        (body.asPath.asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun, N)
      // The dynamic runtime helper has no result annotation. Reestablish the wrapper's
      // return representation here so it survives both ordinary returns and inlining.
      val wrapperBody = Scoped(Set.single(bodySym), Define(body,
        Return(wrapped.coerceTo(wrapper.signature.result.bodyType.getOrElse(ErasedType.Unknown), fun.dSym.toLoc))))
      FunDefn(fun.owner, fun.sym, wrapper.symbol, wrapper.signature, wrapperBody)(fun.configOverride, noAsync)
    
    override def applyPath(p: Path)(k: Path => Block): Block =
      p match
        case s: Select if s.symbol.contains(ctx.builtins.handlers.await) =>
          if config.effectHandlers.isEmpty && !inAsyncFun then
            raise(ErrorReport(
              msg"Only await inside of async bodies are allowed if effect handlers are not enabled." ->
              p.toLoc :: Nil,
              source = Diagnostic.Source.Compilation))
          k(State.runtimeSymbol.asSimpleRef.sel(ctx.builtins.handlers.await))
        case _ =>
          super.applyPath(p)(k)
  
  def transform(prog: Program): Program =
    // The source symbol's Async result remains available to imported or cloned source
    // bodies. The lowered wrapper returns Promise directly and needs a fresh symbol.
    // Allocate every replacement first so forward and recursive calls see the same one.
    val wrappers = mutable.Map.empty[TermSymbol, Wrapper]
    new BlockTraverser:
      applyProgram(prog)
      override def applyFunDefn(fun: FunDefn): Unit =
        if fun.async then
          val result = ErasedResult.fromAnnotations(fun.signature.erasure.ret,
            fun.annotations.filterNot(_.isInstanceOf[Annot.Async]))
          val signature = FunDefn.Signature.fromParams(fun.params, result)
          assert(!wrappers.contains(fun.dSym), "An async symbol must have only one definition")
          wrappers(fun.dSym) = (SymbolRefresher.copyTermSymbol(fun.dSym, fun.owner, S(signature.erasure)), signature)
        super.applyFunDefn(fun)
    new Rewriter(wrappers).applyProgram(prog)
