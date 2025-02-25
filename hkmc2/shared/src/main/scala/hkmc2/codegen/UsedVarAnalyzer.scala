package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.semantics.Elaborator.State

import scala.collection.mutable.Map as MutMap

/**
  * Analyzes which variables have been used and mutated by which functions.
  * Also finds which variables can be passed to a capture class without a heap
  * allocation (during class lifting) despite being mutable.
  *
  * Assumes the input trees have no lambdas.
  */
class UsedVarAnalyzer(b: Block, handlerPaths: Opt[HandlerPaths])(using State):
  import Lifter.*

  private case class DefnMetadata(
    definedLocals: Map[BlockMemberSymbol, Set[Local]], // locals defined explicitly by that function
    defnsMap: Map[BlockMemberSymbol, Defn], // map bms to defn
    existingVars: Map[BlockMemberSymbol, Set[Local]], // variables already existing when that defn is defined
    inScopeDefns: Map[BlockMemberSymbol, Set[BlockMemberSymbol]], // definitions that are in scope and not nested within this defn, and not including itself
    nestedDefns: Map[BlockMemberSymbol, List[Defn]], // definitions that are a successor of the current defn
    nestedDeep: Map[BlockMemberSymbol, Set[BlockMemberSymbol]], // definitions nested within another defn, including that defn (deep)
    nestedIn: Map[BlockMemberSymbol, BlockMemberSymbol], // the definition that a definition is directly nested in
  )
  private def createMetadata: DefnMetadata =
    var defnsMap: Map[BlockMemberSymbol, Defn] = Map.empty
    var definedLocals: Map[BlockMemberSymbol, Set[Local]] = Map.empty
    var existingVars: Map[BlockMemberSymbol, Set[Local]] = Map.empty
    var inScopeDefns: Map[BlockMemberSymbol, Set[BlockMemberSymbol]] = Map.empty
    var nestedDefns: Map[BlockMemberSymbol, List[Defn]] = Map.empty
    var nestedDeep: Map[BlockMemberSymbol, Set[BlockMemberSymbol]] = Map.empty
    var nestedIn: Map[BlockMemberSymbol, BlockMemberSymbol] = Map.empty

    def createMetadataFn(f: FunDefn, existing: Set[Local], inScope: Set[BlockMemberSymbol]): Unit =
      var nested: Set[BlockMemberSymbol] = Set.empty
      
      existingVars += (f.sym -> existing)
      val thisVars = Lifter.getVars(f) -- existing
      val newExisting = existing ++ thisVars

      val thisScopeDefns: List[Defn] = f.body.floatOutDefns()._2

      nestedDefns += f.sym -> thisScopeDefns

      val newInScope = inScope ++ thisScopeDefns.map(_.sym)
      for s <- thisScopeDefns do
        inScopeDefns += s.sym -> (newInScope - s.sym)
        nested += s.sym

      defnsMap += (f.sym -> f)
      definedLocals += (f.sym -> thisVars)

      for d <- thisScopeDefns do
        nestedIn += (d.sym -> f.sym)
        createMetadataDefn(d, newExisting, newInScope)
        nested ++= nestedDeep(d.sym)
      
      nestedDeep += f.sym -> nested

    def createMetadataDefn(d: Defn, existing: Set[Local], inScope: Set[BlockMemberSymbol]): Unit =
      d match
      case f: FunDefn =>
        createMetadataFn(f, existing, inScope)
      case c: ClsLikeDefn =>
        createMetadataCls(c, existing, inScope)
      case d => Map.empty

    def createMetadataCls(c: ClsLikeDefn, existing: Set[Local], inScope: Set[BlockMemberSymbol]): Unit =
      var nested: Set[BlockMemberSymbol] = Set.empty
      
      existingVars += (c.sym -> existing)
      val thisVars = Lifter.getVars(c) -- existing
      val newExisting = existing ++ thisVars

      val thisScopeDefns: List[Defn] =
        (c.methods ++ c.preCtor.floatOutDefns()._2 ++ c.ctor.floatOutDefns()._2)

      nestedDefns += c.sym -> thisScopeDefns
      
      val newInScope = inScope ++ thisScopeDefns.map(_.sym)
      for s <- thisScopeDefns do
        inScopeDefns += s.sym -> (newInScope - s.sym)
        nested += s.sym
      
      defnsMap += (c.sym -> c)
      definedLocals += (c.sym -> thisVars)

      for d <- thisScopeDefns do
        nestedIn += (d.sym -> c.sym)
        createMetadataDefn(d, newExisting, newInScope)
        nested ++= nestedDeep(d.sym)
      
      nestedDeep += c.sym -> nested
  
    new BlockTraverserShallow(SymbolSubst()):
      applyBlock(b)
      override def applyDefn(defn: Defn): Unit =
        inScopeDefns += defn.sym -> Set.empty
        createMetadataDefn(defn, b.definedVars, Set.empty)
    DefnMetadata(definedLocals, defnsMap, existingVars, inScopeDefns, nestedDefns, nestedDeep, nestedIn)

  val DefnMetadata(definedLocals, defnsMap, existingVars, 
    inScopeDefns, nestedDefns, nestedDeep, nestedIn) = createMetadata

  def isModule(s: BlockMemberSymbol) = defnsMap.get(s) match
    case S(c: ClsLikeDefn) => c.k is syntax.Mod
    case _ => false
    
  def isHandlerClsPath(p: Path) = handlerPaths match
    case None => false
    case Some(paths) => paths.isHandlerClsPath(p)
  
  private val blkMutCache: MutMap[Local, AccessInfo] = MutMap.empty
  private def blkAccessesShallow(b: Block, cacheId: Opt[Local] = N): AccessInfo =
    cacheId.flatMap(blkMutCache.get) match
    case Some(value) => value
    case None => 
      var accessed: AccessInfo = AccessInfo.empty
      new BlockTraverserShallow(SymbolSubst()):
        applyBlock(b)
        
        override def applyBlock(b: Block): Unit = b match
          case Assign(lhs, rhs, rest) =>
            accessed = accessed.addMutated(lhs)
            applyResult(rhs)
            applyBlock(rest)
          case Label(label, body, rest) =>
            accessed ++= blkAccessesShallow(body, S(label))
            applyBlock(rest)
          case _ => super.applyBlock(b)
        
        override def applyValue(v: Value): Unit = v match
          case Value.Ref(_: BuiltinSymbol) => super.applyValue(v)
          case RefOfBms(l) =>
            if !isModule(l) then accessed = accessed.addRefdDefn(l)
          case Value.Ref(l) =>
            accessed = accessed.addAccess(l)
          case _ => super.applyValue(v)

      cacheId match
        case None => ()
        case Some(value) => blkMutCache.addOne(value -> accessed)
      
      accessed

  private val accessedCache: MutMap[BlockMemberSymbol, AccessInfo] = MutMap.empty
  
  /**
    * Finds the variables which this definition could possibly mutate, excluding mutations through
    * calls to other functions and, in the case of functions, mutations of its own variables.
    *
    * @param defn The definition to search through.
    * @return The variables which this definition could possibly mutate.
    */
  private def findAccessesShallow(defn: Defn): AccessInfo = 
    def create = defn match
      case f: FunDefn =>
        val fVars = definedLocals(f.sym)
        blkAccessesShallow(f.body).withoutLocals(fVars)
      case c: ClsLikeDefn =>
        val methodSyms = c.methods.map(_.sym).toSet
        c.methods.foldLeft(blkAccessesShallow(c.preCtor) ++ blkAccessesShallow(c.ctor)):
          case (acc, fDefn) =>
            // class methods do not need to be lifted, so we don't count calls to their methods.
            // a previous reference to this class's block member symbol is enough to assume any
            // of the class's methods could be called.
            //
            // however, we must keep references to the class itself!
            val defnAccess = findAccessesShallow(fDefn)
            acc ++ defnAccess.withoutBms(methodSyms)
      case _: ValDefn => AccessInfo.empty
    
    accessedCache.getOrElseUpdate(defn.sym, create)

  // MUST be called from a top-level defn
  private def findAccesses(d: Defn): Map[BlockMemberSymbol, AccessInfo] =
    var defns: List[Defn] = Nil
    var definedVarsDeep: Set[Local] = Set.empty

    new BlockTraverser(SymbolSubst()):
      applyDefn(d)
      
      override def applyFunDefn(f: FunDefn): Unit =
        defns +:= f; definedVarsDeep ++= definedLocals(f.sym)
        super.applyFunDefn(f)
      
      override def applyDefn(defn: Defn): Unit =
        defn match
          case c: ClsLikeDefn => defns +:= c; definedVarsDeep ++= definedLocals(c.sym)
          case _ =>
        super.applyDefn(defn)

    val defnSyms = defns.map(_.sym).toSet
    val accessInfo = defns.map: d =>
      val AccessInfo(accessed, mutated, refdDefns) = findAccessesShallow(d)
      d.sym -> AccessInfo(
        accessed.intersect(definedVarsDeep),
        mutated.intersect(definedVarsDeep),
        refdDefns.intersect(defnSyms) // only care about definitions nested in this top-level definition
      )

    val accessInfoMap = accessInfo.toMap

    val edges =
      for
        (sym, AccessInfo(_, _, refd)) <- accessInfo
        r <- refd
        if defnSyms.contains(r)
      yield sym -> r
    .toSet

    // (sccs, sccEdges) forms a directed acyclic graph (DAG)
    val algorithms.SccsInfo(sccs, sccEdges, inDegs, outDegs) = algorithms.sccsWithInfo(edges, defnSyms)
    
    // all defns in the same scc must have at least the same accesses as each other
    val base = for (id, scc) <- sccs yield id ->
      scc.foldLeft(AccessInfo.empty):
        case (acc, sym) => acc ++ accessInfoMap(sym)
    
    // dp on DAG
    val dp: MutMap[Int, AccessInfo] = MutMap.empty
    def sccAccessInfo(scc: Int): AccessInfo = dp.get(scc) match
      case Some(value) => value
      case None =>
        val ret = sccEdges(scc).foldLeft(base(scc)):
          case (acc, nextScc) => acc ++ sccAccessInfo(nextScc)
        dp.addOne(scc -> ret)
        ret

    for
      (id, scc) <- sccs
      sym <- scc
    yield sym -> (sccAccessInfo(id).intersectLocals(existingVars(sym)))

  private def findAccessesTop =
    var accessMap: Map[BlockMemberSymbol, AccessInfo] = Map.empty
    new BlockTraverserShallow(SymbolSubst()):
      applyBlock(b)
      override def applyDefn(defn: Defn): Unit = defn match
        case _: FunDefn | _: ClsLikeDefn =>
          accessMap ++= findAccesses(defn)
        case _ => super.applyDefn(defn)
    
    accessMap
  
  val accessMap = findAccessesTop

  // TODO: let declarations inside loops (also broken without class lifting)
  // I'll fix it once it's fixed in the IR since we will have more tools to determine
  // what locals belong to what block.
  private def reqdCaptureLocals(f: FunDefn) =
    var (_, defns) = f.body.floatOutDefns()
    val defnSyms = defns.collect:
        case f: FunDefn => f.sym -> f
        case c: ClsLikeDefn => c.sym -> c
      .toMap

    val thisVars = definedLocals(f.sym)

    case class CaptureInfo(reqCapture: Set[Local], hasReader: Set[Local], hasMutator: Set[Local])

    def go(b: Block, reqCapture_ : Set[Local], hasReader_ : Set[Local], hasMutator_ : Set[Local]): CaptureInfo =
      var reqCapture = reqCapture_
      var hasReader = hasReader_
      var hasMutator = hasMutator_

      inline def merge(c: CaptureInfo) =
        reqCapture ++= c.reqCapture
        hasReader ++= c.hasReader
        hasMutator ++= c.hasMutator

      def rec(blk: Block) =
        go(blk, reqCapture, hasReader, hasMutator)
      
      new BlockTraverserShallow(SymbolSubst()):
        applyBlock(b)
        override def applyBlock(b: Block): Unit = b match
          case Assign(lhs, rhs, rest) =>
            applyResult(rhs)
            if hasReader.contains(lhs) || hasMutator.contains(lhs) then reqCapture += lhs
            applyBlock(rest)

          case Match(scrut, arms, dflt, rest) =>
            applyPath(scrut)
            val infos = arms.map:
              case (_, arm) => rec(arm)
            val dfltInfo = dflt.map:
              case arm => rec(arm)
            
            infos.map(merge) // IMPORTANT: rec all first, then merge, since each branch is mutually exclusive
            dfltInfo.map(merge)
            applyBlock(rest)
          case Label(label, body, rest) =>
            // for now, if the loop body mutates a variable and that variable is accessed or mutated by a defn,
            // or if it reads a variable that is later mutated by an instance inside the loop,
            // we put it in a capture. this preserves the current semantics of the IR (even though it's incorrect).
            // See the above TODO
            val c @ CaptureInfo(req, read, mut) = rec(body)
            merge(c)
            reqCapture ++= read.intersect(blkAccessesShallow(body, S(label)).mutated)
            reqCapture ++= mut.intersect(body.freeVars)
            applyBlock(rest)
          case Begin(sub, rest) =>
            rec(sub) |> merge
            applyBlock(rest)
          case TryBlock(sub, finallyDo, rest) =>
            // sub and finallyDo could be executed sequentially, so we must merge
            rec(sub) |> merge
            rec(finallyDo) |> merge
            applyBlock(rest)
          case Return(res, false) =>
            applyResult(res)
            hasReader = Set.empty
            hasMutator = Set.empty
          case _ => super.applyBlock(b)

        def handleCalledBms(called: BlockMemberSymbol): Unit = defnSyms.get(called) match
          case None => ()
          case Some(defn) =>
            // special case continuation classes
            defn match
              case c: ClsLikeDefn => c.parentPath match
                case S(path) if isHandlerClsPath(path) => return
                    // treat the continuation class as if it does not exist
                case _ => ()
              case _ => ()
            

            val AccessInfo(accessed, muted, refd) = accessMap(defn.sym)
            val muts = muted.intersect(thisVars)
            val reads = defn.freeVars.intersect(thisVars) -- muts
            // this not a naked reference. if it's a ref to a class, this can only ever create once instance
            // so the "one writer" rule applies
            for l <- muts do
              if hasReader.contains(l) || hasMutator.contains(l) || defn.isInstanceOf[FunDefn] then
                reqCapture += l
              hasMutator += l
            for l <- reads do
              if hasMutator.contains(l) then
                reqCapture += l
              hasReader += l
            // if this defn calls another defn that creates a class or has a naked reference to a
            // function, we must capture the latter's mutated variables in a capture, as arbitrarily
            // many mutators could be created from it
            for
              sym <- refd
              l <- accessMap(sym).mutated
            do
              reqCapture += l
              hasMutator += l

        override def applyResult(r: Result): Unit = r match
          case Call(RefOfBms(l), args) =>
            args.map(super.applyArg(_))
            handleCalledBms(l)
          case Instantiate(InstSel(l), args) =>
            args.map(super.applyPath(_))
            handleCalledBms(l)
          case _ => super.applyResult(r)
        
        override def applyPath(p: Path): Unit = p match
          case RefOfBms(l) =>
            defnSyms.get(l) match
            case None => super.applyPath(p)
            case Some(defn) =>
              val isMod = defn match
                case c: ClsLikeDefn => modOrObj(c)
                case _ => false
              if isMod then super.applyPath(p)
              else
                val AccessInfo(accessed, muted, refd) = accessMap(defn.sym)
                val muts = muted.intersect(thisVars)
                val reads = defn.freeVars.intersect(thisVars) -- muts
                // this is a naked reference, we assume things it mutates always needs a capture
                for l <- muts do
                  reqCapture += l
                  hasMutator += l
                for l <- reads do
                  if hasMutator.contains(l) then
                    reqCapture += l
                  hasReader += l
                // if this defn calls another defn that creates a class or has a naked reference to a
                // function, we must capture the latter's mutated variables in a capture, as arbitrarily
                // many mutators could be created from it
                for
                  sym <- refd
                  l <- accessMap(sym).mutated
                do
                  reqCapture += l
                  hasMutator += l
          
          case Value.Ref(l) =>
            if hasMutator.contains(l) then reqCapture += (l)
          case _ => super.applyPath(p)
        
        override def applyDefn(defn: Defn): Unit = defn match
          case c: ClsLikeDefn if modOrObj(c) =>
            handleCalledBms(c.sym)
            super.applyDefn(defn)
          case _ => super.applyDefn(defn)

      CaptureInfo(reqCapture, hasReader, hasMutator)

    val reqCapture = go(f.body, Set.empty, Set.empty, Set.empty).reqCapture
    val usedVars = defns.flatMap(_.freeVars.intersect(thisVars)).toSet
    (usedVars, reqCapture)

  // the current problem is that we need extra code to find which variables were really defined by a function
  // this may be resolved in the future when the IR gets explicit variable declarations
  private def findUsedLocalsFn(f: FunDefn): Map[BlockMemberSymbol, FreeVars] =
    val thisVars = definedLocals(f.sym)

    val (vars, cap) = reqdCaptureLocals(f)

    var usedMap: Map[BlockMemberSymbol, FreeVars] = Map.empty
    usedMap += (f.sym -> Lifter.FreeVars(vars.intersect(thisVars), cap.intersect(thisVars)))
    for d <- nestedDefns(f.sym) do
      usedMap ++= findUsedLocalsDefn(d)
    usedMap

  private def findUsedLocalsDefn(d: Defn) =
    d match
    case f: FunDefn => 
      findUsedLocalsFn(f)
    case c: ClsLikeDefn =>
      findUsedLocalsCls(c)
    case d => Map.empty

  private def findUsedLocalsCls(c: ClsLikeDefn): Map[BlockMemberSymbol, FreeVars] =
    nestedDefns(c.sym).foldLeft(Map.empty):
      case (acc, d) => acc ++ findUsedLocalsDefn(d)
  
  /**
    * Finds the used locals of functions which have been used by their nested definitions.
    *
    * @param b
    * @return
    */
  def findUsedLocals: Lifter.UsedLocalsMap =
    var usedMap: Map[BlockMemberSymbol, FreeVars] = Map.empty
    new BlockTraverserShallow(SymbolSubst()):
      applyBlock(b)
      override def applyDefn(defn: Defn): Unit =
        usedMap ++= findUsedLocalsDefn(defn)

    Lifter.UsedLocalsMap(usedMap)
