package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*

import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.Map as MutMap

// Lifts classes and functions to the top-level.
// Assumes the input block does not have any `HandleBlock`s.
class Lifter(using State):
  
  // Describes the free variables of a function
  case class FreeVars(params: Set[Local], bodyVars: Set[Local])
  case class ParamOwner(f: FunDefn, isParam: Bool)

  // use mutable sets locally to avoid reconstructing everything
  private case class FreeVarsMut(params: MutSet[Local], bodyVars: MutSet[Local])
  
  // Given a function definition f and previously bound locals boundLocals,
  // creates a map FunDefn -> List[Local] where each function definitions f
  // in boundLocals is associated with a list of locals which both:
  // - First occur in f, i.e. is a free variable of f
  // - Are accessed by some definition within f
  // These are the variables which will be moved to the closure.
  // We do this once for every top-level function definition instead
  // of once for every function definition so that we only traverse
  // the tree once.
  private def findUsedLocalsImpl(f: FunDefn, lookup: Map[Local, ParamOwner]): Map[FunDefn, FreeVarsMut] =
    val params: Set[Local] = f.params.flatMap(_.paramSyms).toSet // note: doesn't type check without annotation
    val bodyVars = f.body.definedVars -- params

    // add this function's locals to the lookup map
    val lookupNext = lookup 
      ++ params.map(s => (s -> ParamOwner(f, true))) 
      ++ params.map(s => (s -> ParamOwner(f, false)))

    // collect all function definitions
    val vars: MutMap[FunDefn, FreeVarsMut] = MutMap.from(lookupNext.map:
      case _ -> ParamOwner(f, _) => f -> FreeVarsMut(MutSet(), MutSet())
    )

    def merge(next: Map[FunDefn, FreeVarsMut]) =
      for f -> FreeVarsMut(params, bodyVars) <- next do
        for l <- params do vars(f).params.add(l)
        for l <- bodyVars do vars(f).bodyVars.add(l)
    
    def addLocal(l: Local) = lookup.get(l) match
      case Some(ParamOwner(f, isParam)) =>
        if isParam then vars(f).params.add(l)
        else vars(f).bodyVars.add(l)
      case None => ()

    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) => 
          merge(findUsedLocalsImpl(f, lookupNext))
          super.applyBlock(b)
        case Define(c: ClsLikeDefn, rest) =>
          for f <- c.methods do merge(findUsedLocalsImpl(f, lookupNext))
          super.applyBlock(b)
        case Assign(lhs, _, rest) =>
          addLocal(lhs)
          super.applyBlock(b) 
        case _ => super.applyBlock(b)

      override def applyValue(v: Value): Value = v match
        case Value.Ref(l) => 
          addLocal(l)
          super.applyValue(v)
        
        case _ => super.applyValue(v)
    
    walker.applyBlock(f.body)

    vars.toMap

  def findUsedLocals(f: FunDefn) = findUsedLocalsImpl(f, Map()).map:
    case f -> FreeVarsMut(params, bodyVars) => f -> FreeVars(params.toSet, bodyVars.toSet)
      
  private def lift(f: FunDefn, clsMap: Map[ClassLikeSymbol, ClassLikeSymbol]) =
    val (blk, defns) = f.body.floatOutDefns

  // top-level
  def transform(b: Block) = b