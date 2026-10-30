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
import scala.collection.mutable.ArrayBuffer


class AsyncLowering(using TL, Raise, Elaborator.State, Elaborator.Ctx, Config):
  
  private type Wrapper = (symbol: TermSymbol, signature: FunDefn.Signature)
  
  private class Rewriter(wrappers: collection.Map[TermSymbol, Wrapper]) extends BlockTransformer(new SymbolSubst:
    override def mapTermSym(sym: TermSymbol): TermSymbol = wrappers.get(sym).fold(sym)(_.symbol)):
    val collectedFunDefn: ArrayBuffer[FunDefn] = new ArrayBuffer
    var inAsyncFun: Bool = false
    
    inline def wrapAwait[T](innerAllowAwait: Bool)(inline thunk: => T): T =
      val saved = inAsyncFun
      inAsyncFun = innerAllowAwait
      val result = thunk
      inAsyncFun = saved
      result
    
    override def applyFunDefn(fun: FunDefn): FunDefn =
      if !fun.async then return wrapAwait(false)(super.applyFunDefn(fun))
      val outerBms = BlockMemberSymbol(fun.sym.nme, Nil, fun.sym.nameIsMeaningful)
      val outerParams = fun.params.flatMap: pl =>
        pl.allParams.map: p =>
          val v = p.sym
          val nv = VarSymbol(v.id, erasedType = v.erasedType, mut = v.mut)
          (p, p.copy(sym = nv)(p.toLoc))
      val symMap = outerParams.iterator.map(p => p._1.sym -> p._2.sym).toMap
      val thisVar = VarSymbol(Tree.Ident("this"), erasedType = fun.owner.flatMap(_.asThis.erasedType), mut = false)
      val thisParam = fun.owner.map(_ => Param.simple(thisVar))
      val outerDsym = TermSymbol(syntax.Fun, N, fun.dSym.id)
      val noAsync = fun.annotations.filterNot(_.isInstanceOf[Annot.Async])
      val outerSignature = FunDefn.Signature.fromParams(
        LoweredParamList.plain((thisParam.iterator ++ outerParams.iterator.map(_._2)).toList)(N) ::
          LoweredParamList.plain(Nil)(N) :: Nil,
        ErasedResult.fromAnnotations(fun.signature.result.bodyType, noAsync))
      // The extracted helper has fresh parameter bindings. Substitute assignment
      // destinations as well as reads, including assignments inside nested closures.
      val paramSubst = new SymbolSubst:
        override def mapVarSym(sym: VarSymbol): VarSymbol = symMap.getOrElse(sym, sym)
      val transformer = new BlockTransformer(paramSubst):
        override def applyValue(v: Value)(k: Value => Block): Block = v match
          case Value.This(sym) if fun.owner.contains(sym) =>
            k(Value.SimpleRef(thisVar)(v.toLoc))
          case _ => super.applyValue(v)(k)
      val newBody = transformer.applyBlock(wrapAwait(true)(applyFunBodyLikeBlock(fun.body)))
      collectedFunDefn += FunDefn(N, outerBms, outerDsym, outerSignature, newBody)(fun.configOverride, noAsync)
      val callArgs = (fun.owner.iterator.map(s => Arg(N, Value.This(s)(N))) ++ fun.params.iterator.flatMap(_.allParams.iterator.map(p => Arg(N, Value.SimpleRef(p.sym)(N))))).toList
      val outerCall = Call(Value.MemberRef(outerBms, outerDsym)(N), callArgs ne_:: Nil)(CallMetadata.mlsFunWithEffect, N)
      val tmp = TempSymbol(N, initErasedType = outerCall.erasedType, "tmp")
      val wrapperBody = blockBuilder
        .assignScoped(tmp, outerCall)
        .ret(Call(Value.SimpleRef(State.runtimeSymbol)(N).selSN("toJsAsync"), (tmp.asSimpleRef.asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun, N))
      val wrapper = wrappers(fun.dSym)
      FunDefn(fun.owner, fun.sym, wrapper.symbol, wrapper.signature, wrapperBody)(fun.configOverride, noAsync)
    
    override def applyMainBlock(main: Block): Block =
      collectedFunDefn.foldRight(super.applyMainBlock(main)): (defn, acc) =>
        Scoped(Set.single(defn.sym), Define(defn, acc))
    
    override def applyPath(p: Path)(k: Path => Block): Block =
      p match
        case s: Select if s.symbol.contains(ctx.builtins.handlers.await) =>
          if config.effectHandlers.isEmpty && !inAsyncFun then
            raise(ErrorReport(
              msg"Only await inside of async bodies are allowed if effect handlers are not enabled." ->
              p.toLoc :: Nil,
              source = Diagnostic.Source.Compilation))
          k(State.runtimeSymbol.asSimpleRef.sel(new Tree.Ident("await"), ctx.builtins.handlers.await))
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
