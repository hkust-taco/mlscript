package hkmc2
package codegen
package deforest

import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap}
import hkmc2.syntax.{ImmutVal, MutVal, LetBind, HandlerBind, ParamBind, Fun, Ins}



class DeforestRewriter(val solver: DeforestConstrainSolver):
  import solver.FinalDest
  given tl: TraceLogger = solver.tl
  given dState: Deforest.State = solver.dState
  given eState: Elaborator.State = solver.collector.elabState
  
  private val _symSubst = new SymbolSubst()
  
  val newFunInstances: collection.Map[InstantiationId, (BlockMemberSymbol, TermSymbol)] =
    val store = MutMap.empty[InstantiationId, (BlockMemberSymbol, TermSymbol)]
    for (ctor, FinalDest(dest, sels)) <- solver.finalCtorDests do
      for case ctorInstId@(referringTo :: _) <- List(ctor.instId, dest.instId) do
        store.getOrElseUpdate(
          ctorInstId,
          new BlockMemberSymbol(ctorInstId.mkFunName, Nil, true) ->
          new TermSymbol(Fun, N, Tree.Ident(ctorInstId.mkFunName)))
    store
  end newFunInstances
  
  private class Rewriter(instId: InstantiationId) extends BlockTransformer(_symSubst):
    override def applyResult(r: Result)(k: Result => Block): Block =
      r match
      case ref@FunRef(f) if newFunInstances.isDefinedAt(ref.uid :: instId) =>
        val (bms, tSym) = newFunInstances(ref.uid :: instId)
        k(Value.Ref(bms, S(tSym)))
      // case ctor@CtorCall(cls, args) if solver.finalCtorDests.isDefinedAt() =>
        
        
  
  
  
  
  
  
  for (instId, bms) <- newFunInstances do
    tl.log(bms)
end DeforestRewriter

