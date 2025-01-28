package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.Tree
import hkmc2.codegen.llir.FreshInt

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.LinkedHashMap
import scala.collection.mutable.Map as MutMap
import scala.annotation.nowarn

// Lifts classes and functions to the top-level.
// Assumes the input block does not have any `HandleBlock`s and lamdbas are
// rewritten as functions (lambdas will be removed from the IR soon).
class Lifter(using State):
  
  // Describes the free variables of a function.
  // vars: The free variables that are accessed or mutated by nested classes/functions.
  // mutated: The free variables that are mutated, but not accessed, by nested classes/functions.
  case class FreeVars(vars: List[Local], mutated: List[Local])

  // use mutable sets locally to avoid reconstructing everything
  // linked hash sets preserve order
  private case class FreeVarsMut(vars: LinkedHashSet[Local], mutated: LinkedHashSet[Local])

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
  
  // usedLocals: describes the locals belonging to each function that are accessed/mutated by nested defns
  // localCaptureSyms: the symbols in a capture corresponding to a particular local
  // prevFnDefns: fun defns that have already been traversed
  // prevClsDefns: class defns that have already been traversed
  // capturePaths: the path to access a particular function's capture in the local scope
  // bmsReqdInfo: the (mutable) captures and (immutable) local variables each function requires
  // bmsPaths: the path to access a particular BlockMemberSymbol in the local scope w/ the captures already applied
  // localPaths: the path to access a particular local (possibly belonging to a prev fn/class) in the current scope
  case class LifterCtx(
    val usedLocals: UsedLocalsMap, 
    val localCaptureSyms: Map[Local, VarSymbol],
    val prevFnDefns: List[FunDefn],
    val prevClsDefns: List[ClsLikeDefn],
    val capturePaths: Map[BlockMemberSymbol, Path],
    val bmsReqdInfo: Map[BlockMemberSymbol, LiftedInfo], // required captures
    val bmsPaths: Map[BlockMemberSymbol, Path],
    val localPaths: Map[Local, Local]
  ):
    // gets the function to which a local belongs
    def lookup(l: Local) = usedLocals.lookup(l)
    // the path to access the capture of a particular function
    def getCapturePath(b: BlockMemberSymbol) = capturePaths.get(b)
    // the path to access the capture of the function that a local belongs to
    def getLocalClosPath(l: Local) = lookup(l).flatMap(capturePaths.get(_))
    // the symbol in the capture corresponding to a particular local
    def getLocalCaptureSym(l: Local) = localCaptureSyms.get(l)
    // the path to a local value containing this function with the captures already applied
    def getBmsPath(b: BlockMemberSymbol) = bmsPaths.get(b)
    // how to access a variable in the local scope
    def getLocalPath(l: Local) = localPaths.get(l)
    
    def addDefn(f: FunDefn) = copy(prevFnDefns = f :: prevFnDefns)
    def addLocalCaptureSyms(m: Map[Local, VarSymbol]) = copy(localCaptureSyms = localCaptureSyms ++ m)
    def getBmsReqdInfo(sym: BlockMemberSymbol) = bmsReqdInfo.get(sym)
    def replCapturePaths(paths: Map[BlockMemberSymbol, Path]) = copy(capturePaths = paths)
    def addCapturePath(src: BlockMemberSymbol, path: Path) = copy(capturePaths = capturePaths + (src -> path))
    def addBmsReqdInfo(mp: Map[BlockMemberSymbol, LiftedInfo]) = copy(bmsReqdInfo = bmsReqdInfo ++ mp)
    def addBmsPaths(paths: Map[BlockMemberSymbol, Path]) = copy(bmsPaths = bmsPaths ++ paths)
    def replLocalPaths(m: Map[Local, Local]) = copy(localPaths = m)
    def addLocalPaths(m: Map[Local, Local]) = copy(localPaths = localPaths ++ m)
    
  object LifterCtx:
    def empty = LifterCtx(UsedLocalsMap(Map.empty), Map.empty, Nil, Nil, Map.empty, Map.empty, Map.empty, Map.empty)
    def withLocals(u: UsedLocalsMap) = empty.copy(usedLocals = u)
  
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
      case _ -> f => f -> FreeVarsMut(LinkedHashSet.empty, LinkedHashSet.empty)
    )

    // add this function in case this function has no locals
    if !retMap.contains(f) then retMap.addOne(f -> FreeVarsMut(LinkedHashSet.empty, LinkedHashSet.empty))

    // merge recursive call results
    def merge(next: Map[FunDefn, FreeVarsMut]) =
      for f -> (v @ FreeVarsMut(vars, mutated)) <- next do retMap.get(f) match
        case None => retMap.addOne(f -> v)
        case Some(value) =>
          for l <- vars do retMap(f).vars.addOne(l)
          for l <- mutated do retMap(f).mutated.addOne(l)
    
    def addLocal(l: Local, mut: Bool) = lookup.get(l) match
      case Some(f) =>
        if mut then retMap(f).mutated.addOne(l)
        retMap(f).vars.addOne(l)
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
            case f -> FreeVarsMut(vars, mutated) => 
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

    val fresh = FreshInt()

    val varsMap: Map[Local, VarSymbol] = mutated.map: s =>
      val id = fresh.make
      s -> VarSymbol(Tree.Ident(s.nme + id + "$"))
    .toMap

    val varsList = mutated.toList
    
    val defn = ClsLikeDefn(
      None, clsSym, BlockMemberSymbol(nme, Nil), 
      syntax.Cls,
      S(PlainParamList(varsList.map(s => Param(FldFlags.empty, varsMap(s), None)))),
      Nil, None, Nil, Nil, Nil, End(), End()
    )

    (defn, varsMap, varsList)

  def liftDefnsCls(c: ClsLikeDefn, ctx: LifterCtx): List[Defn] = ???

  private def needsCapture(captureFn: FunDefn, candidate: Defn, ctx: LifterCtx) =
    val candVars = candidate.freeVars
    val captureFnVars = ctx.usedLocals(captureFn.sym).mutated.toSet
    !candVars.intersect(captureFnVars).isEmpty
  
  private def neededImutLocals(captureFn: FunDefn, candidate: Defn, ctx: LifterCtx) =
    val candVars = candidate.freeVars
    val captureFnVars = ctx.usedLocals(captureFn.sym)
    val mutVars = captureFnVars.mutated.toSet
    val imutVars = captureFnVars.vars
    imutVars.filter: s =>
      !mutVars.contains(s) && candVars.contains(s)

  case class LiftedInfo(
    val reqdCaptures: List[BlockMemberSymbol],
    val reqdVars: List[Local]
  )
  case class Lifted(
    val liftedDefn: Defn,
    val extraDefns: List[Defn],
    val info: Opt[LiftedInfo]
  ):
    def withInfo = LiftedInfo.apply.tupled andThen (info => Lifted(liftedDefn, extraDefns, S(info)))

  object Lifted:
    def of(d: Defn, ed: List[Defn]) = Lifted(d, ed, N)

  inline def liftOutDefn(base: FunDefn, d: Defn, ctx: LifterCtx): Lifted =
    @nowarn("msg=New anonymous class definition will be duplicated at each inline site") // inlined only at one place
    val includedCaptures = ctx.prevFnDefns.collect:
      case prev if needsCapture(prev, d, ctx) => (prev, VarSymbol(Tree.Ident(prev.sym.nme + "$capture")))

    val includedLocals = ctx.prevFnDefns.flatMap: ls =>
      neededImutLocals(ls, d, ctx).map: l =>
        (l, VarSymbol(Tree.Ident(l.nme)))

    if includedCaptures.isEmpty && includedLocals.isEmpty then Lifted.of(d, Nil)
    else
      val extraParamsCaptures = includedCaptures.map:
        case (d, sym) => Param(FldFlags.empty, sym, None)
      val newCapturePaths = includedCaptures.map:
        case (d, sym) => d.sym -> sym.asPath
      .toMap

      val extraParamsLocals = includedLocals.map:
        case (d, sym) => Param(FldFlags.empty, sym, None)
      val newLocalsPaths = includedLocals.map:
        case (d, sym) => d -> sym
      .toMap

      val extraParams = extraParamsLocals ++ extraParamsCaptures

      d match
      case d: FunDefn => 
        val newDef = FunDefn(
          base.owner, d.sym, PlainParamList(extraParams) :: d.params, d.body
        )
        val newCtx = ctx.replCapturePaths(newCapturePaths).replLocalPaths(newLocalsPaths)
        val (lifted, extra) = liftDefnsInFn(newDef, newCtx)
        Lifted.of(lifted, extra).withInfo(includedCaptures.map(_._1.sym), includedLocals.map(_._1))
      case d: ClsLikeDefn => Lifted.of(d, Nil)
        // TODO
        // liftDefnsCls(d)
      case _ => Lifted.of(d, Nil)

  def createCall(sym: BlockMemberSymbol, ctx: LifterCtx) : Call =
    val info = ctx.getBmsReqdInfo(sym).get
    val localsArgs = info.reqdVars.map(ctx.getLocalPath(_).get.asPath.asArg)
    val capturesArgs = info.reqdCaptures.map(ctx.getCapturePath(_).get.asArg)
    Call(sym.asPath, localsArgs ++ capturesArgs)(false)
  
  def liftDefnsInFn(f: FunDefn, ctx: LifterCtx): (Defn, List[Defn]) =
    val (captureCls, varsMap, varsList) = createCaptureCls(f, ctx)
    
    val (blk, nested) = f.body.floatOutDefns

    // add the mapping from this function's locals to the capture's symbols and the capture path
    val captureSym = FlowSymbol("capture")
    val captureCtx = ctx
      .addLocalCaptureSyms(varsMap) // how to access locals via. the capture class from now on
      .addCapturePath(f.sym, captureSym.asPath) // the path to this function's capture
    val nestedCtx = captureCtx.addDefn(f)

    val nestedLifted = nested.map(liftOutDefn(f, _, nestedCtx))
    val bmsInfo = nestedLifted.collect:
      case Lifted(liftedDefn, extraDefns, S(info)) => 
        liftedDefn.sym -> info
    .toMap
    val newDefns = nestedLifted.flatMap:
      case Lifted(liftedDefn, extraDefns, _) => liftedDefn :: extraDefns

    // creates the triple:
    // (bms, that bms's required captures, the symbol to that bms with captures applied)
    val withSymbols = bmsInfo.map: (bms, captures) =>
      (bms, captures, FlowSymbol(bms.nme + "$this"))
    
    val bmsPathsMap = withSymbols.map:
      case (bms, captures, sym) => bms -> sym.asPath
    .toMap

    val thisVars = ctx.usedLocals(f.sym)

    val newCtx = captureCtx
      .addBmsReqdInfo(bmsInfo.toMap)
      .addBmsPaths(bmsPathsMap)
      .addLocalPaths((thisVars.vars.toSet -- thisVars.mutated).map(s => s -> s).toMap)

    
    val start = withSymbols.foldRight(blockBuilder):
      case ((bms, captures, sym), acc) => 
        acc.assign(sym, Call(bms.asPath, captures.reqdCaptures.map(newCtx.getCapturePath(_).get.asArg))(false))
    
    // replaces references to BlockMemberSymbols as needed with fresh variables, and
    // returns the mapping from the symbol to the required variable. When possible,
    // it also directly rewrites Results.
    def rewriteBms(b: Block, ctx: LifterCtx) =
      val syms: LinkedHashMap[BlockMemberSymbol, Local] = LinkedHashMap.empty

      val walker = new BlockTransformerNoRec(SymbolSubst()):
        // only scan within the block. don't traverse

        // if possible, directly create the call and replace the result with it
        override def applyResult(r: Result): Result = r match
          case Value.Ref(l: BlockMemberSymbol) if ctx.bmsReqdInfo.contains(l) => createCall(l, newCtx) 
          case _ => super.applyResult(r)
        
        // otherwise, there's no choice but to create the call earlier
        override def applyValue(v: Value): Value = v match
          case Value.Ref(l: BlockMemberSymbol) if ctx.bmsReqdInfo.contains(l) => 
            val newSym = syms.get(l) match
              case None =>
                val newSym = FlowSymbol(l.nme + "$this")
                syms.addOne(l -> newSym)
                newSym
              case Some(value) => value
            Value.Ref(newSym)
          case _ => super.applyValue(v)
      (walker.applyBlock(b), syms.toList)
    end rewriteBms
        

    // rewrites references to variables
    val transformer1 = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Assign(lhs, rhs, rest) => newCtx.getLocalCaptureSym(lhs) match
          case Some(captureSym) => 
            AssignField(newCtx.getLocalClosPath(lhs).get, captureSym.id, applyResult(rhs), applyBlock(rest))(N)
          case None => newCtx.getLocalPath(lhs) match
            case None => super.applyBlock(b)
            case Some(value) => Assign(value, applyResult(rhs), applyBlock(rest))
        case _ => super.applyBlock(b)
        
      override def applyPath(p: Path): Path = p match
        /*
        case Value.Ref(b: BlockMemberSymbol) => newCtx.getBmsPath(b) match
          case None => super.applyPath(p)
          case Some(value) => value
        */
        case Value.Ref(l) => newCtx.getLocalCaptureSym(l) match
          case Some(captureSym) => Select(newCtx.getLocalClosPath(l).get, captureSym.id)(N)
          case None => newCtx.getLocalPath(l) match
            case Some(value) => Value.Ref(value)
            case None => super.applyPath(p) 
        case _ => super.applyPath(p)

    // rewrites references to block member symbols
    val transformer2 = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block =
        val (rewriten, syms) = rewriteBms(b, newCtx)
        val pre = syms.foldLeft(blockBuilder):
          case (blk, (bms, local)) => 
            blk.assign(local, createCall(bms, newCtx))
        pre.rest(super.applyBlock(rewriten))

    val transformed = blk |> transformer1.applyBlock |> transformer2.applyBlock

    if thisVars.mutated.size == 0 then
      (FunDefn(f.owner, f.sym, f.params, transformed), newDefns)
    else
      val paramsSet = f.params.flatMap(_.paramSyms)
      val paramsList = varsList.filter(paramsSet.contains(_))
      val bod = blockBuilder
        .assign(captureSym, Instantiate(captureCls.sym.asPath, paramsList.map(_.asPath)))
        .rest(transformed)
      (FunDefn(f.owner, f.sym, f.params, bod), captureCls :: newDefns)

  end liftDefnsInFn

  // top-level
  def transform(b: Block) =
    val ctx = LifterCtx.withLocals(findUsedLocals(b))

    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) =>
          val (d, extra) = liftDefnsInFn(f, ctx)
          (d :: extra).foldLeft(rest)((acc, defn) => Define(defn, acc))
        case _ => super.applyBlock(b)
    walker.applyBlock(b)