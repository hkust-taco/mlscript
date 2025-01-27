package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.Tree
import hkmc2.codegen.llir.FreshInt

import scala.collection.mutable.ListBuffer as ListBuffer
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet

// Lifts classes and functions to the top-level.
// Assumes the input block does not have any `HandleBlock`s and lamdbas are
// rewritten as functions (lambdas will be removed from the IR soon).
class Lifter(using State):
  
  // Describes the free variables of a function.
  // vars: The free variables that are accessed or mutated by nested classes/functions.
  // mutated: The free variables that are mutated, but not accessed, by nested classes/functions.
  case class FreeVars(vars: List[Local], mutated: List[Local])

  // use mutable sets locally to avoid reconstructing everything
  // use the list to maintain the order (for a more readable output when debugging)
  // and a list to make sure it's unique
  private case class FreeVarsMut(varsSet: MutSet[Local], vars: ListBuffer[Local], mutated: MutSet[Local])

  class UsedLocalsMap(mp: Map[BlockMemberSymbol, FreeVars]):
    def apply(f: BlockMemberSymbol) = mp(f)
    private lazy val inverse = mp.flatMap:
      case fn -> vars => vars.vars.map(v => v -> fn)
    // gets the function to which a local belongs
    def lookup(l: Local) = inverse.get(l)
    def print = println(mp.map:
      case a -> b => a -> b
    )
  
  object UsedLocalsMap:
    def from(mp: Map[FunDefn, FreeVars]) =
      UsedLocalsMap(mp.map:
        case a -> b => a.sym -> b  
      )
    

  class LifterCtx(
    val usedLocals: UsedLocalsMap, 
    val localSyms: Map[Local, VarSymbol],
    val prevDefns: List[FunDefn],
    val capturePaths: Map[BlockMemberSymbol, Path],
    val bmsReqdCaptures: Map[BlockMemberSymbol, List[BlockMemberSymbol]], // required captures
    val bmsPaths: Map[BlockMemberSymbol, Path],
  ):
    // gets the function to which a local belongs
    def lookup(l: Local) = usedLocals.lookup(l)
    // the path to access the capture of a particular function
    def getCapturePath(b: BlockMemberSymbol) = capturePaths.get(b)
    // the path to access the capture of the function that a local belongs to
    def getLocalClosPath(l: Local) = lookup(l).flatMap(capturePaths.get(_))
    // the symbol in the capture corresponding to a particular local
    def getLocalSym(l: Local) = localSyms(l)
    // the path to a local value containing this function with the captures already applied
    def getBmsPath(b: BlockMemberSymbol) = bmsPaths.get(b)

    def addDefn(f: FunDefn) = 
      LifterCtx(usedLocals, localSyms, f :: prevDefns, capturePaths, bmsReqdCaptures, bmsPaths)
    def addLocalPaths(m: Map[Local, VarSymbol]) =
      LifterCtx(usedLocals, localSyms ++ m, prevDefns, capturePaths, bmsReqdCaptures, bmsPaths)
    def replCapturePaths(paths: Map[BlockMemberSymbol, Path]) = 
      LifterCtx(usedLocals, localSyms, prevDefns, paths, bmsReqdCaptures, bmsPaths)
    def addCapturePath(src: BlockMemberSymbol, path: Path) = 
      LifterCtx(usedLocals, localSyms, prevDefns, capturePaths + (src -> path), bmsReqdCaptures, bmsPaths)
    def addReqdCaptures(mp: Map[BlockMemberSymbol, List[BlockMemberSymbol]]) =
      LifterCtx(usedLocals, localSyms, prevDefns, capturePaths, bmsReqdCaptures ++ mp, bmsPaths)
    def addBmsPaths(paths: Map[BlockMemberSymbol, Path]) = 
      LifterCtx(usedLocals, localSyms, prevDefns, capturePaths, bmsReqdCaptures, bmsPaths ++ paths)
  
  def getVars(f: FunDefn): Set[Local] = 
    (f.body.definedVars ++ f.params.flatMap(_.paramSyms)).collect:
      case s: FlowSymbol => s
  
  // Given a function definition f and previously bound locals boundLocals,
  // creates a map FunDefn -> List[Local] where each function definitions f
  // in boundLocals is associated with a list of locals which both:
  // - First occur in f, i.e. is a free variable of f
  // - Are accessed by some definition within f
  // These are the variables which will be moved to the capture.
  // We do this once for every top-level function definition instead
  // of once for every function definition so that we only traverse
  // the tree once.
  private def findUsedLocalsImpl(f: FunDefn, lookup: Map[Local, FunDefn]): Map[FunDefn, FreeVarsMut] =
    val definedVars = getVars(f)

    // add this function's locals to the lookup map
    // NOTE: `lookup` will overwrite definitions already defined in previous functions
    // here, ++ must not be used as a commutative operator!
    val lookupNext = definedVars.map(_ -> f).toMap ++ lookup

    // collect all function definitions
    val retMap: MutMap[FunDefn, FreeVarsMut] = MutMap.from(lookupNext.map:
      case _ -> f => f -> FreeVarsMut(MutSet.empty, ListBuffer.empty, MutSet.empty)
    )

    // add this function in case this function has no locals
    if !retMap.contains(f) then retMap.addOne(f -> FreeVarsMut(MutSet.empty, ListBuffer.empty, MutSet.empty))

    // merge recursive call results
    def merge(next: Map[FunDefn, FreeVarsMut]) =
      for f -> (v @ FreeVarsMut(varsSet, vars, mutated)) <- next do 
        retMap.get(f) match
        case None => retMap.addOne(f -> v)
        case Some(value) =>
          val freeVars = retMap(f)
          for l <- vars if !freeVars.varsSet.contains(l) do 
            freeVars.varsSet.addOne(l)
            freeVars.vars.addOne(l)
          for l <- mutated do freeVars.mutated.addOne(l)
    
    def addLocal(l: Local, mut: Bool) = lookup.get(l) match
      case Some(f) =>
        val freeVars = retMap(f)
        if mut then freeVars.mutated.addOne(l)
        if !freeVars.varsSet.contains(l) then
          freeVars.varsSet.addOne(l)
          freeVars.vars.addOne(l)
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
    var usedMap: Map[FunDefn, FreeVars] = Map.empty
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) =>
          val m = findUsedLocalsImpl(f, Map.empty).map:
            case f -> FreeVarsMut(varsSet, vars, mutated) => 
              f -> FreeVars(vars.toList, mutated.toList)
          usedMap ++= m
          super.applyBlock(b)
        case _ => super.applyBlock(b)
    walker.applyBlock(b)
    UsedLocalsMap.from(usedMap)

  def createCaptureCls(f: FunDefn, ctx: LifterCtx) =
    val nme = f.sym.nme + "$capture"

    val clsSym = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident(nme)
    )

    val FreeVars(vars, mutated) = ctx.usedLocals(f.sym)
    println(vars)

    val fresh = FreshInt()

    val varsMap: Map[Local, VarSymbol] = vars.map: s =>
      val id = fresh.make
      s -> VarSymbol(Tree.Ident(s.nme + id + "$"))
    .toMap

    val varsList = vars.toList
    
    val defn = ClsLikeDefn(
      None, clsSym, BlockMemberSymbol(nme, Nil), 
      syntax.Cls,
      S(PlainParamList(varsList.map(s => Param(FldFlags.empty, varsMap(s), None)))),
      None, Nil, Nil, Nil, End(), End()
    )

    (defn, varsMap, varsList)

  def liftDefnsCls(c: ClsLikeDefn, ctx: LifterCtx): List[Defn] = ???

  private def needsCapture(captureFn: FunDefn, candidate: Defn) =
    val candVars = candidate.freeVars
    val captureFnVars = getVars(captureFn)
    !candVars.intersect(captureFnVars).isEmpty

  def liftDefnsFn(f: FunDefn, ctx: LifterCtx): List[Defn] =
    val (captureCls, varsMap, varsList) = createCaptureCls(f, ctx)
    
    val (blk, defns) = f.body.floatOutDefns

    // add the mapping from this function's locals to the capture's symbols and the capture path
    val captureSym = FlowSymbol("capture")
    val captureCtx = ctx
      .addLocalPaths(varsMap)
      .addCapturePath(f.sym, captureSym.asPath)

    val thisUsed = ctx.usedLocals(f.sym)

    val bmsCaptures: ListBuffer[(BlockMemberSymbol, List[BlockMemberSymbol])] = ListBuffer.empty

    val newDefns = defns.flatMap: d =>
      // add parameters for previous defns
      val includedCaptures = (f :: captureCtx.prevDefns).collect:
        case prev if needsCapture(prev, d) => (prev, VarSymbol(Tree.Ident(prev.sym.nme + "$capture")))

      if includedCaptures.isEmpty then d :: Nil
      else
        val extraParams = includedCaptures.map:
          case (d, sym) => Param(FldFlags.empty, sym, None)

        bmsCaptures.addOne(d.sym -> includedCaptures.map(_._1.sym))
        
        val newCapturePaths = includedCaptures.map:
          case (d, sym) => d.sym -> sym.asPath
        .toMap

        d match
        case d: FunDefn => 
          val newDef = FunDefn(
            f.owner, d.sym, PlainParamList(extraParams) :: d.params, d.body
          )
          liftDefnsFn(newDef, captureCtx.addDefn(f).replCapturePaths(newCapturePaths))
        case d: ClsLikeDefn => d :: Nil
          // TODO
          // liftDefnsCls(d)
        case _ => d :: Nil

    val withSymbols = bmsCaptures.map: (bms, captures) =>
      (bms, captures, VarSymbol(Tree.Ident(bms.nme + "$this")))
    
    val bmsPathsMap = withSymbols.map:
      case (bms, captures, sym) => bms -> sym.asPath
    .toMap

    val newCtx = captureCtx
      .addReqdCaptures(bmsCaptures.toMap)
      .addBmsPaths(bmsPathsMap)

    // println(f.sym)

    val start = withSymbols.foldRight(blockBuilder):
      case ((bms, captures, sym), acc) => 
        acc.assign(sym, Call(bms.asPath, captures.map(newCtx.getCapturePath(_).get.asArg))(false))

    val transformer = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Assign(lhs, rhs, rest) => newCtx.getLocalClosPath(lhs) match
          case None => super.applyBlock(b)
          case Some(closPath) => 
            AssignField(closPath, newCtx.getLocalSym(lhs).id, rhs, applyBlock(rest))(N)
        case _ => super.applyBlock(b)
        
      override def applyPath(p: Path): Path = p match
        case Value.Ref(b: BlockMemberSymbol) => newCtx.getBmsPath(b) match
          case None => super.applyPath(p)
          case Some(value) => value
        
        case Value.Ref(l) => 
          newCtx.getLocalClosPath(l) match
          case None => super.applyPath(p)
          case Some(closPath) => Select(closPath, newCtx.getLocalSym(l).id)(N)
        
        case _ => super.applyPath(p)

    if thisUsed.vars.size == 0 then
      FunDefn(f.owner, f.sym, f.params, start.rest(transformer.applyBlock(blk))) :: newDefns
    else
      val paramsSet = f.params.flatMap(_.paramSyms)
      val paramsList = varsList.filter(paramsSet.contains(_))
      val bod = blockBuilder
        .assign(captureSym, Instantiate(captureCls.sym.asPath, paramsList.map(_.asPath)))
        .chain(start)
        .rest(transformer.applyBlock(blk))
      FunDefn(f.owner, f.sym, f.params, bod) :: captureCls :: newDefns


  // top-level
  def transform(b: Block) =
    val ctx = LifterCtx(findUsedLocals(b), Map.empty, Nil, Map.empty, Map.empty, Map.empty)

    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) =>
          liftDefnsFn(f, ctx).foldLeft(rest)((acc, defn) => Define(defn, acc))
        case _ => super.applyBlock(b)
    walker.applyBlock(b)