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
  
  // Describes the free variables of a function
  case class FreeVars(params: Set[Local], bodyVars: Set[Local])
  case class ParamOwner(f: FunDefn, isParam: Bool)

  // use mutable sets locally to avoid reconstructing everything
  private case class FreeVarsMut(params: MutSet[Local], bodyVars: MutSet[Local])

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
  private def findUsedLocalsImpl(f: FunDefn, lookup: Map[Local, ParamOwner]): Map[FunDefn, FreeVarsMut] =
    val params = f.params.flatMap(_.paramSyms).toSet
    val bodyVars = (f.body.definedVars -- params).collect:
      case s: FlowSymbol => s

    println(f.sym)
    println(params)
    println(bodyVars)

    // add this function's locals to the lookup map
    val lookupNext = lookup 
      ++ params.map(s => (s -> ParamOwner(f, true))) 
      ++ bodyVars.map(s => (s -> ParamOwner(f, false)))

    // collect all function definitions
    val vars: MutMap[FunDefn, FreeVarsMut] = MutMap.from(lookupNext.map:
      case _ -> ParamOwner(f, _) => f -> FreeVarsMut(MutSet(), MutSet())
    )

    // add this function in case this function has no locals
    if !vars.contains(f) then vars.addOne(f -> FreeVarsMut(MutSet(), MutSet()))

    def merge(next: Map[FunDefn, FreeVarsMut]) =
      for f -> (v @ FreeVarsMut(params, bodyVars)) <- next do vars.get(f) match
        case None => vars.addOne(f -> v)
        case Some(value) =>
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

  def findUsedLocals(b: Block): UsedLocalsMap = 
    var usedMap: UsedLocalsMap = Map()
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) =>
          val m = findUsedLocalsImpl(f, Map()).map:
            case f -> FreeVarsMut(params, bodyVars) => f -> FreeVars(params.toSet, bodyVars.toSet)
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

    val FreeVars(paramVars, bodyVars) = usedMap(f)
    val vars = paramVars ++ bodyVars

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


  private def lift(f: FunDefn) =
    val (blk, defns) = f.body.floatOutDefns

  // top-level
  def transform(b: Block) =
    given usedMap: UsedLocalsMap = findUsedLocals(b)
    // for debugging
    println(usedMap.map:
      case a -> b => a.sym -> b
    )

    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) =>
          Define(createClosureCls(f)._1, Define(f, applyBlock(rest)))
        case _ => super.applyBlock(b)
    walker.applyBlock(b)

    
      