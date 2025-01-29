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
import scala.collection.mutable.Set as MutSet
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
  
  object UsedLocalsMap:
    def from(mp: Map[FunDefn, FreeVars]) =
      UsedLocalsMap(mp.map:
        case a -> b => a.sym -> b  
      ) 

  /**
    * The context of the class lifter.
    * @param usedLocals Describes the locals belonging to each function that are accessed/mutated by nested defns
    * @param localCaptureSyms The symbols in a capture corresponding to a particular local
    * @param prevFnDefns Function definitoins that have already been traversed
    * @param prevClsDefns Class definitions that have already been traversed
    * @param capturePaths The path to access a particular function's capture in the local scope
    * @param bmsReqdInfo The (mutable) captures and (immutable) local variables each function requires
    * @param bmsPaths The path to access a particular BlockMemberSymbol in the local scope with the captures already applied
    * @param localPaths The path to access a particular local (possibly belonging to a previous function) in the current scope
    * @param iSymPaths The path to access a particular `innerSymbol` (possibly belonging to a previous class) in the current scope
    */
  case class LifterCtx(
    val usedLocals: UsedLocalsMap, 
    val localCaptureSyms: Map[Local, LocalSymbol & NamedSymbol],
    val prevFnDefns: List[FunDefn],
    val prevClsDefns: List[ClsLikeDefn],
    val capturePaths: Map[BlockMemberSymbol, Path],
    val bmsReqdInfo: Map[BlockMemberSymbol, LiftedInfo], // required captures
    val bmsPaths: Map[BlockMemberSymbol, Path],
    val localPaths: Map[Local, Local],
    val iSymPaths: Map[InnerSymbol, Local]
  ):
    // gets the function to which a local belongs
    def lookup(l: Local) = usedLocals.lookup(l)
    // the path to access the capture of a particular function
    def getCapturePath(b: BlockMemberSymbol) = capturePaths.get(b)
    // the path to access the capture of the function that a local belongs to
    def getLocalClosPath(l: Local) = lookup(l).flatMap(capturePaths.get(_))
    // the symbol in the capture corresponding to a particular local
    def getLocalCaptureSym(l: Local) = localCaptureSyms.get(l)
    // how to access a variable in the local scope
    def getLocalPath(l: Local) = localPaths.get(l)
    def getIsymPath(l: InnerSymbol) = iSymPaths.get(l)
    
    def addFnDefn(f: FunDefn) = copy(prevFnDefns = f :: prevFnDefns)
    def addClsDefn(c: ClsLikeDefn) = copy(prevClsDefns = c :: prevClsDefns)
    def addLocalCaptureSyms(m: Map[Local, LocalSymbol & NamedSymbol]) = copy(localCaptureSyms = localCaptureSyms ++ m)
    def getBmsReqdInfo(sym: BlockMemberSymbol) = bmsReqdInfo.get(sym)
    def replCapturePaths(paths: Map[BlockMemberSymbol, Path]) = copy(capturePaths = paths)
    def addCapturePath(src: BlockMemberSymbol, path: Path) = copy(capturePaths = capturePaths + (src -> path))
    def addBmsReqdInfo(mp: Map[BlockMemberSymbol, LiftedInfo]) = copy(bmsReqdInfo = bmsReqdInfo ++ mp)
    def replLocalPaths(m: Map[Local, Local]) = copy(localPaths = m)
    def replIsymPaths(m: Map[InnerSymbol, Local]) = copy(iSymPaths = m)
    def addLocalPaths(m: Map[Local, Local]) = copy(localPaths = localPaths ++ m)
  
  object LifterCtx:
    def empty = LifterCtx(UsedLocalsMap(Map.empty), Map.empty, Nil, Nil, 
      Map.empty, Map.empty, Map.empty, Map.empty, Map.empty)
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

    // tracks if the locals here have been mutated more than once in this function
    val assignedOnce: MutSet[Local] = MutSet.empty
    val assignedTwice: MutSet[Local] = MutSet.empty

    def addLocal(l: Local, mut: Bool) = lookup.get(l) match
      case Some(f) =>
        if mut then retMap(f).mutated.addOne(l)
        retMap(f).vars.addOne(l)
      case None => if mut then
        if assignedOnce.contains(l) then
          assignedTwice.add(l)
        else
          assignedOnce.add(l)

    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) => 
          merge(findUsedLocalsImpl(f, lookupNext))
          super.applyBlock(b)
        case Define(c: ClsLikeDefn, rest) =>
          for f <- c.methods do merge(findUsedLocalsImpl(f, lookupNext))
          super.applyBlock(b)
        case Assign(lhs, rhs, rest) =>
          addLocal(lhs, true) // TODO: when proper immutable variables have been added, refactor this
          applyResult(rhs)
          super.applyBlock(b) 
        case _ => super.applyBlock(b)

      override def applyValue(v: Value): Value = v match
        case Value.Ref(l) => 
          addLocal(l, false)
          super.applyValue(v)
        
        case _ => super.applyValue(v)
    
    walker.applyBlock(f.body)

    // add mutable locals
    retMap(f).mutated ++= retMap(f).vars.intersect(assignedTwice)

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
  
  /**
    * Creates a capture class for a function consisting of its mutable (and possibly immutable) local variables.
    * @param f The function to create the capture class for.
    * @param ctx The lifter context. Determines which variables will be captured.
    * @return The triple (defn, varsMap, varsList), where `defn` is the capture class's definition,
    * `varsMap` maps the function's locals to the correpsonding `VarSymbol` in the class, and
    * `varsList` specifies the order of these variables in the class's constructor. 
    */
  def createCaptureCls(f: FunDefn, ctx: LifterCtx) =
    val nme = f.sym.nme + "$capture"

    val clsSym = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident(nme)
    )

    val FreeVars(vars, mutated) = ctx.usedLocals(f.sym)

    val fresh = FreshInt()

    val varsMap: Map[Local, TermSymbol] = mutated.map: s =>
      val id = fresh.make
      s -> TermSymbol(syntax.ParamBind, S(clsSym), Tree.Ident(s.nme + id + "$"))
    .toMap

    val varsList = mutated.toList
    
    val defn = ClsLikeDefn(
      None, clsSym, BlockMemberSymbol(nme, Nil), 
      syntax.Cls,
      S(PlainParamList(varsList.map(s => Param(FldFlags.empty, varsMap(s), None)))),
      Nil, None, Nil, Nil, Nil, End(), End()
    )

    (defn, varsMap, varsList)

  private val clsLikeCache: MutMap[Defn, Set[Local]] = MutMap.empty
  
  /**
    * Gets the inner symbols referenced within a class (including those within a member symbol).
    * @param c The class from which to get the inner symbols. 
    * @return The inner symbols reference within a class.
    */
  def getInnerSymbols(c: Defn) = clsLikeCache.get(c) match 
    case Some(value) => value
    case None =>
      val ret: Set[Local] = c.freeVars.collect:
        case s: InnerSymbol => s
        case t: TermSymbol if t.owner.isDefined => t.owner.get
      clsLikeCache.addOne(c -> ret)
      ret

  /**
    * Determines whether a certain class's `this` needs to be captured by a class being lifted.
    * @param captureCls The class in question that is considered for capture.
    * @param liftDefn The class being lifted.
    * @return Whether the class needs to be captured.
    */
  private def needsClsCapture(captureCls: ClsLikeDefn, liftDefn: Defn) =
    getInnerSymbols(liftDefn).contains(captureCls.isym)

  /**
    * Determines whether a certain function's mutable closure needs to be captured by a definition being lifted.
    * @param captureFn The function in question that is considered for capture.
    * @param liftDefn The definition being lifted.
    * @return Whether the function needs to be captured.
    */
  private def needsCapture(captureFn: FunDefn, liftDefn: Defn, ctx: LifterCtx) =
    val candVars = liftDefn.freeVars
    val captureFnVars = ctx.usedLocals(captureFn.sym).mutated.toSet
    !candVars.intersect(captureFnVars).isEmpty
  
  /**
    * Gets the immutable local variables of a function that need to captured by a definition being lifted. 
    * @param captureFn The function in question whose local variables need to be captured.
    * @param liftDefn The definition being lifted.
    * @return The local variables that need to be captured.
    */
  private def neededImutLocals(captureFn: FunDefn, liftDefn: Defn, ctx: LifterCtx) =
    val candVars = liftDefn.freeVars
    val captureFnVars = ctx.usedLocals(captureFn.sym)
    val mutVars = captureFnVars.mutated.toSet
    val imutVars = captureFnVars.vars
    imutVars.filter: s =>
      !mutVars.contains(s) && candVars.contains(s)

  case class LiftedInfo(
    val reqdCaptures: List[BlockMemberSymbol],
    val reqdVars: List[Local],
    val reqdInnerSyms: List[InnerSymbol]
  )

  case class Lifted(
    val liftedDefn: Defn,
    val extraDefns: List[Defn],
  )

  def createLiftInfoCont(d: Defn, parentCls: Opt[ClsLikeDefn], ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    
    // the commented code is incorrect, more in-depth analysis is needed to properly remove variables/captures
    // that aren't needed
    /*
    val includedCaptures = ctx.prevFnDefns.filter(needsCapture(_, d, ctx))

    val includedLocals = ctx.prevFnDefns.flatMap: ls =>
      neededImutLocals(ls, d, ctx)

    val clsCaptures: List[InnerSymbol] = ctx.prevClsDefns.filter(needsClsCapture(_, d)).map(_.isym).collect:
      // this line is just to satisfy the type system, in reality anything we capture is an InnerSymbol
      case s: InnerSymbol => s

    val info = LiftedInfo(includedCaptures.map(_.sym), includedLocals, clsCaptures)
    */

    // for now, we just include everything
    val includedCaptures = ctx.prevFnDefns.filter: f =>
      val FreeVars(vars, mut) = ctx.usedLocals(f.sym)
      mut.size != 0

    val includedLocals = ctx.prevFnDefns.flatMap: f =>
      val FreeVars(vars, mut) = ctx.usedLocals(f.sym)
      vars.filter(!mut.contains(_))

    val clsCaptures: List[InnerSymbol] = ctx.prevClsDefns.map(_.isym).filter: c => 
      parentCls match
      case Some(value) if d.isInstanceOf[FunDefn] => value != parentCls
      case _ => true
    .collect:
      // this line is just to satisfy the type system, in reality anything we capture is an InnerSymbol
      case s: InnerSymbol => s

    val info = LiftedInfo(includedCaptures.map(_.sym), includedLocals, clsCaptures)

    if includedCaptures.isEmpty && includedLocals.isEmpty && clsCaptures.isEmpty then Map.empty
    else d match
      case f: FunDefn => 
        createLiftInfoFn(f, parentCls, ctx) + (d.sym -> info)
      case c: ClsLikeDefn => 
        createLiftInfoCls(c, ctx) + (d.sym -> info)
      case _ => Map.empty
  
  def createLiftInfoFn(f: FunDefn, parentCls: Opt[ClsLikeDefn], ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val (_, defns) = f.body.floatOutDefns
    defns.flatMap(createLiftInfoCont(_, parentCls, ctx.addFnDefn(f))).toMap

  def createLiftInfoCls(c: ClsLikeDefn, ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val defns = c.preCtor.floatOutDefns._2 ++ c.ctor.floatOutDefns._2
    val newCtx = ctx.addClsDefn(c)
    defns.flatMap(f => createLiftInfoCont(f, S(c), newCtx)).toMap 
      ++ c.methods.flatMap(f => createLiftInfoFn(f, S(c), newCtx))
  
  def createLiftInfo(b: Block, ctx: LifterCtx) =
    var ret: Map[BlockMemberSymbol, LiftedInfo] = Map.empty
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) => 
          ret = ret ++ createLiftInfoFn(f, N, ctx)
          super.applyBlock(b)
        case _ => super.applyBlock(b)
    walker.applyBlock(b)
    ret
  
  def createCall(sym: BlockMemberSymbol, ctx: LifterCtx) : Call =
    val info = ctx.getBmsReqdInfo(sym).get
    val localsArgs = info.reqdVars.map(ctx.getLocalPath(_).get.asPath.asArg)
    val capturesArgs = info.reqdCaptures.map(ctx.getCapturePath(_).get.asArg)
    Call(sym.asPath, localsArgs ++ capturesArgs)(false)

  // deals with creating parameter lists
  def liftOutDefnCont(base: Defn, d: Defn, ctx: LifterCtx): Lifted = ctx.getBmsReqdInfo(d.sym) match
    case N => Lifted(d, Nil)
    case S(LiftedInfo(includedCaptures, includedLocals, clsCaptures)) =>
      val createSym = d match
        case d: ClsLikeDefn => ((nme: String) => TermSymbol(syntax.ParamBind, S(d.isym), Tree.Ident(nme)))
        case _ => ((nme: String) => VarSymbol(Tree.Ident(nme)))
      
      val capturesSymbols = includedCaptures.map: sym =>
        (sym, createSym(sym.nme + "$capture"))

      val localsSymbols = includedLocals.map:sym =>
        (sym, createSym(sym.nme))

      val isymSymbols = clsCaptures.map:sym =>
        (sym, createSym(sym.nme + "$instance"))

      val extraParamsCaptures = capturesSymbols.map: // parameter list
        case (d, sym) => Param(FldFlags.empty, sym, None)
      val newCapturePaths = capturesSymbols.map: // mapping from sym to param symbol
        case (d, sym) => d -> sym.asPath
      .toMap

      val extraParamsLocals = localsSymbols.map: // parameter list
        case (d, sym) => Param(FldFlags.empty, sym, None)
      val newLocalsPaths = localsSymbols.map: // mapping from sym to param symbol
        case (d, sym) => d -> sym
      .toMap

      val extraParamsIsyms = isymSymbols.map: // parameter list
        case (d, sym) => Param(FldFlags.empty, sym, None)
      val newIsymPaths = isymSymbols.map: // mapping from sym to param symbol
        case (d, sym) => d -> sym
      .toMap

      val extraParams = extraParamsIsyms ++ extraParamsLocals ++ extraParamsCaptures

      val newCtx = ctx
        .replCapturePaths(newCapturePaths)
        .replLocalPaths(newLocalsPaths)
        .replIsymPaths(newIsymPaths)

      d match
      case f: FunDefn => 
        val newDef = FunDefn(
          base.owner, f.sym, PlainParamList(extraParams) :: f.params, f.body
        )
        liftDefnsInFn(newDef, newCtx)
      case c: ClsLikeDefn =>
        val newDef = c.copy(
          owner = base.owner, auxParams = c.auxParams.appended(PlainParamList(extraParams))
        )
        liftDefnsInCls(newDef, newCtx)
      case _ => Lifted(d, Nil)
  
  def liftDefnsInCls(c: ClsLikeDefn, ctx: LifterCtx): Lifted = 
    val (preCtor, preCtorDefns) = c.preCtor.floatOutDefns
    val (ctor, ctorDefns) = c.ctor.floatOutDefns
    
    val newCtx = ctx // TODO: add block member symbol replacement

    val newPreCtor = rewriteBlk(preCtor, newCtx)
    val newCtor = rewriteBlk(ctor, newCtx)

    val ctorDefnsLifted = (preCtorDefns ++ ctorDefns).flatMap: defn =>
      val Lifted(liftedDefn, extraDefns) = liftOutDefnCont(c, defn, newCtx)
      liftedDefn :: extraDefns
    
    val fLifted = c.methods.flatMap: f =>
      val Lifted(liftedDefn, extraDefns) = liftDefnsInFn(f, newCtx)
      liftedDefn :: extraDefns

    val allDefs = (ctorDefnsLifted ++ fLifted).map:
      case f: FunDefn => f.copy(owner = S(c.isym))
      case c: ClsLikeDefn => c.copy(owner = c.owner) 
      case d => d
    
    val funDefs = allDefs.collect:
      case f: FunDefn => f
    
    val clsDefs = allDefs.collect:
      case c: ClsLikeDefn => c
    
    val newDef = c.copy(
      methods = funDefs,
      preCtor = newPreCtor,
      ctor = newCtor
    )
    
    Lifted(newDef, clsDefs)

  def rewriteBlk(b: Block, ctx: LifterCtx): Block =
    // replaces references to BlockMemberSymbols as needed with fresh variables, and
    // returns the mapping from the symbol to the required variable. When possible,
    // it also directly rewrites Results.
    def rewriteBms(b: Block, ctx: LifterCtx) =
      val syms: LinkedHashMap[BlockMemberSymbol, Local] = LinkedHashMap.empty

      val walker = new BlockTransformerNoRec(SymbolSubst()):
        // only scan within the block. don't traverse

        // if possible, directly create the call and replace the result with it
        override def applyResult(r: Result): Result = r match
          case Value.Ref(l: BlockMemberSymbol) if ctx.bmsReqdInfo.contains(l) => createCall(l, ctx)
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
        case Assign(lhs: InnerSymbol, rhs, rest) => ctx.getIsymPath(lhs) match
          case Some(value) => Assign(value, applyResult(rhs), applyBlock(rest))
          case None => super.applyBlock(b)
        
        case Assign(lhs, rhs, rest) => 
          ctx.getLocalCaptureSym(lhs) match
          case Some(captureSym) => 
            AssignField(ctx.getLocalClosPath(lhs).get, captureSym.id, applyResult(rhs), applyBlock(rest))(N)
          case None => ctx.getLocalPath(lhs) match
            case None => super.applyBlock(b)
            case Some(value) => Assign(value, applyResult(rhs), applyBlock(rest))
        case _ => super.applyBlock(b)
        
      override def applyPath(p: Path): Path = p match
        /*
        case Value.Ref(b: BlockMemberSymbol) => newCtx.getBmsPath(b) match
          case None => super.applyPath(p)
          case Some(value) => value
        */
        case Value.Ref(l: InnerSymbol) => ctx.getIsymPath(l) match
          case Some(value) => Value.Ref(value)
          case None => super.applyPath(p)
        case Value.Ref(l) => ctx.getLocalCaptureSym(l) match
          case Some(captureSym) => Select(ctx.getLocalClosPath(l).get, captureSym.id)(N)
          case None => ctx.getLocalPath(l) match
            case Some(value) => Value.Ref(value)
            case None => super.applyPath(p) 
        case _ => super.applyPath(p)

    // rewrites references to block member symbols
    val transformer2 = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block =
        val (rewriten, syms) = rewriteBms(b, ctx)
        val pre = syms.foldLeft(blockBuilder):
          case (blk, (bms, local)) => 
            blk.assign(local, createCall(bms, ctx))
        pre.rest(super.applyBlock(rewriten))

    b |> transformer1.applyBlock |> transformer2.applyBlock


  def liftDefnsInFn(f: FunDefn, ctx: LifterCtx): Lifted =
    val (captureCls, varsMap, varsList) = createCaptureCls(f, ctx)
    
    val (blk, nested) = f.body.floatOutDefns

    // add the mapping from this function's locals to the capture's symbols and the capture path
    val captureSym = FlowSymbol("capture")
    val captureCtx = ctx
      .addLocalCaptureSyms(varsMap) // how to access locals via. the capture class from now on
      .addCapturePath(f.sym, captureSym.asPath) // the path to this function's capture
    val nestedCtx = captureCtx.addFnDefn(f)

    // lift out the nested defns
    val nestedLifted = nested.map(liftOutDefnCont(f, _, nestedCtx))
    val newDefns = nestedLifted.flatMap:
      case Lifted(liftedDefn, extraDefns) => liftedDefn :: extraDefns

    // some book-keeping
    val thisVars = ctx.usedLocals(f.sym)
    val newCtx = captureCtx
      .addLocalPaths((thisVars.vars.toSet -- thisVars.mutated).map(s => s -> s).toMap)

    val transformed = rewriteBlk(blk, newCtx)

    if thisVars.mutated.size == 0 then
      Lifted(FunDefn(f.owner, f.sym, f.params, transformed), newDefns)
    else
      // move the function's parameters to the capture
      val paramsSet = f.params.flatMap(_.paramSyms)
      val paramsList = varsList.filter(paramsSet.contains(_))
      // moved when the capture is instantiated
      val bod = blockBuilder
        .assign(captureSym, Instantiate(captureCls.sym.asPath, paramsList.map(_.asPath)))
        .rest(transformed)
      Lifted(FunDefn(f.owner, f.sym, f.params, bod), captureCls :: newDefns)

  end liftDefnsInFn

  // top-level
  def transform(b: Block) =
    val ctx = LifterCtx.withLocals(findUsedLocals(b))
    val ctxx = ctx.addBmsReqdInfo(createLiftInfo(b, ctx))

    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) =>
          val Lifted(d, extra) = liftDefnsInFn(f, ctxx)
          (d :: extra).foldLeft(rest)((acc, defn) => Define(defn, acc))
        case _ => super.applyBlock(b)
    walker.applyBlock(b)