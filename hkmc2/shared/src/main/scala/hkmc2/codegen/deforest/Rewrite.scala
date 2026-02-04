package hkmc2
package codegen
package deforest

import utils.*
import mlscript.utils.*, shorthands.*
import semantics.*
import syntax.Tree
import scala.collection.mutable.{Set as MutSet, Map as MutMap, LinkedHashMap}



class DeforestRewriter(val solver: DeforestConstrainSolver):
  import solver.FinalDest
  given tl: TraceLogger = solver.tl
  given dState: Deforest.State = solver.dState
  given eState: Elaborator.State = solver.collector.elabState
  
  val newFunInstances: collection.Map[InstantiationId, BlockMemberSymbol] =
    val store = MutMap.empty[InstantiationId, BlockMemberSymbol]
    for (ctor, FinalDest(dest, sels)) <- solver.finalCtorDests do
      for case ctorInstId@(referringTo :: _) <- (ctor.instantiationId ++ dest.instantiationId) do
        store.getOrElseUpdate(
          ctorInstId,
          new BlockMemberSymbol(ctorInstId.mkFunName, Nil, true))
    store
  end newFunInstances
  
  
  
  
  for (instId, bms) <- newFunInstances do
    tl.log(bms)
end DeforestRewriter

