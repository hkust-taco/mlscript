package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.Tree
import hkmc2.codegen.llir.FreshInt

import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.Map as MutMap

// Lifts classes and functions to the top-level.
// Assumes the input block does not have any `HandleBlock`s and lamdbas are
// rewritten as functions (lambdas will be removed from the IR soon).
class Lifter(using State):
  
  // Describes the free variables of a function.
  // vars: The free variables that are accessed or mutated by nested classes/functions.
  // mutated: The free variables that are mutated, but not accessed, by nested classes/functions.
  case class FreeVars(vars: Set[Local], mutated: Set[Local])

  // use mutable sets locally to avoid reconstructing everything
  private case class FreeVarsMut(vars: MutSet[Local], mutated: MutSet[Local])

  type UsedLocalsMap = Map[FunDefn, FreeVars]
  
  // Given a function definition f and previously bound locals boundLocals,
  // creates a map FunDefn -> List[Local] where each function definitions f
  // in boundLocals is associated with a list of locals which both:
  // - First occur in f, i.e. is a free variable of f
  // - Are accessed by some definition within f
  // These are the variables which will be moved to the closure.
  // We do this once for every top-level function definition instead
  // of once for every function definition so that we only traverse
  // the tree once.
  private def findUsedLocalsImpl(f: FunDefn, lookup: Map[Local, FunDefn]): Map[FunDefn, FreeVarsMut] =
    val definedVars = (f.body.definedVars ++ f.params.flatMap(_.paramSyms)).collect:
      case s: FlowSymbol => s

    println(definedVars)

    // add this function's locals to the lookup map
    val lookupNext = lookup ++ definedVars.map(_ -> f)

    // collect all function definitions
    val retMap: MutMap[FunDefn, FreeVarsMut] = MutMap.from(lookupNext.map:
      case _ -> f => f -> FreeVarsMut(MutSet(), MutSet())
    )

    // add this function in case this function has no locals
    if !retMap.contains(f) then retMap.addOne(f -> FreeVarsMut(MutSet(), MutSet()))

    def merge(next: Map[FunDefn, FreeVarsMut]) =
      for f -> (v @ FreeVarsMut(vars, mutated)) <- next do retMap.get(f) match
        case None => retMap.addOne(f -> v)
        case Some(value) =>
          for l <- vars do retMap(f).vars.add(l)
          for l <- mutated do retMap(f).mutated.add(l)
    
    def addLocal(l: Local, mut: Bool) = lookup.get(l) match
      case Some(f) =>
        if mut then retMap(f).mutated.add(l)
        retMap(f).vars.add(l)
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
          addLocal(lhs, true) // TODO: for now, we just assume if a symbol is assigned to, then it's mutable
          super.applyBlock(b) 
        case _ => super.applyBlock(b)

      override def applyValue(v: Value): Value = v match
        case Value.Ref(l) => 
          addLocal(l, false)
          super.applyValue(v)
        
        case _ => super.applyValue(v)
    
    walker.applyBlock(f.body)

    retMap.toMap

  def findUsedLocals(b: Block): UsedLocalsMap = 
    var usedMap: UsedLocalsMap = Map()
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) =>
          val m = findUsedLocalsImpl(f, Map()).map:
            case f -> FreeVarsMut(vars, mutated) => 
              f -> FreeVars(vars.toSet, mutated.toSet)
          usedMap ++= m
          super.applyBlock(b)
        case _ => super.applyBlock(b)
    walker.applyBlock(b)
    usedMap

  def createClosureCls(f: FunDefn)(using usedMap: UsedLocalsMap) =
    val nme = f.sym.nme + "$closure"

    val clsSym = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident(nme)
    )

    val FreeVars(vars, mutated) = usedMap(f)

    val fresh = FreshInt()

    val varsMap: Map[Local, VarSymbol] = vars.map(s =>
      val id = fresh.make
      s -> VarSymbol(Tree.Ident(s.nme + id + "$"))
    ).toMap
    
    val defn = ClsLikeDefn(
      None, clsSym, BlockMemberSymbol(nme, Nil), 
      syntax.Cls,
      S(PlainParamList(vars.toList.map(s => Param(FldFlags.empty, varsMap(s), None)))),
      None, Nil, Nil, Nil, End(), End()
    )

    (defn, varsMap)


  private def liftFn(f: FunDefn) =
    val (blk, defns) = f.body.floatOutDefns

  // top-level
  def transform(b: Block) =
    given usedMap: UsedLocalsMap = findUsedLocals(b)

    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) =>
          Define(createClosureCls(f)._1, Define(f, applyBlock(rest)))
        case _ => super.applyBlock(b)
    walker.applyBlock(b)