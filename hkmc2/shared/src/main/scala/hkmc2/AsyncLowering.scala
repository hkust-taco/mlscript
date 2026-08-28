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
  
  object Rewriter extends BlockTransformer(SymbolSubst.Id):
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
      val outerDsym = TermSymbol(syntax.Fun, N, fun.dSym.id)
      val outerParams = fun.params.flatMap: pl =>
        pl.allParams.map: p =>
          val v = p.sym
          val nv = VarSymbol(v.id)
          (p, p.copy(sym = nv))
      val symMap = outerParams.iterator.map(p => p._1.sym -> p._2.sym).toMap[SimpleSymbol, SimpleSymbol]
      val thisVar = VarSymbol(Tree.Ident("this"))
      val thisParam = fun.owner.map(_ => Param.simple(thisVar))
      val vars = fun.params.flatMap(_.paramSyms)
      val noAsync = fun.annotations.filterNot(_ is Annot.Async)
      val transformer = new BlockTransformer(SymbolSubst.Id):
        override def applySimpleSymbol(sym: SimpleSymbol): SimpleSymbol =
          symMap.getOrElse(sym, sym)
        override def applyValue(v: Value)(k: Value => Block): Block = v match
          case Value.This(sym) if fun.owner.contains(sym) =>
            k(Value.SimpleRef(thisVar))
          case _ => super.applyValue(v)(k)
      val newBody = transformer.applyBlock(wrapAwait(true)(applyFunBodyLikeBlock(fun.body)))
      collectedFunDefn += FunDefn(N, outerBms, outerDsym, PlainParamList((thisParam.iterator ++ outerParams.iterator.map(_._2)).toList) :: PlainParamList(Nil) :: Nil, newBody)(fun.configOverride, noAsync)
      val callArgs = (fun.owner.iterator.map(s => Arg(N, Value.This(s))) ++ fun.params.iterator.flatMap(_.allParams.iterator.map(p => Arg(N, Value.SimpleRef(p.sym))))).toList
      val tmp = TempSymbol(N, "tmp")
      val wrapperBody = blockBuilder
        .assignScoped(tmp, Call(Value.MemberRef(outerBms, outerDsym), callArgs ne_:: Nil)(CallMetadata.mlsFunWithEffect))
        .ret(Call(Value.SimpleRef(State.runtimeSymbol).selSN("toJsAsync"), (tmp.asSimpleRef.asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun))
      FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, wrapperBody)(fun.configOverride, noAsync)
    
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
    Rewriter.applyProgram(prog)
