package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.semantics.Elaborator.State
import hkmc2.ScopeData.*
import hkmc2.Lifter.*

import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import scala.jdk.CollectionConverters.*
import java.util.IdentityHashMap
import java.util.Collections
import scala.collection.mutable.Buffer

object UsedVarAnalyzer:
  case class MutAccessInfo(
    accessed: MutSet[Local], 
    mutated: MutSet[Local], 
    refdDefns: MutSet[ScopedInfo]
  ):
    def toIMut = AccessInfo(accessed.toSet, mutated.toSet, refdDefns.toSet)
  object MutAccessInfo:
    def empty = MutAccessInfo(
      MutSet.empty,
      MutSet.empty,
      MutSet.empty
    )
/**
  * Analyzes which variables have been used and mutated by which functions.
  * Also finds which variables can be passed to a capture class without a heap
  * allocation (during class lifting) despite being mutable.
  *
  * Assumes the input trees have no lambdas.
  */
class UsedVarAnalyzer(b: Block, scopeData: ScopeData, handlerPaths: Opt[HandlerPaths])(using State, IgnoredScopes):
  import UsedVarAnalyzer.*

  
  def isHandlerClsPath(p: Path) = handlerPaths match
    case None => false
    case Some(paths) => paths.isHandlerClsPath(p)
  
  // Finds the locals that this block accesses/mutates, and the definitions which it could use.
  private def blkAccessesShallow(b: Block): AccessInfo =
    var accessed: MutAccessInfo = MutAccessInfo.empty
    new BlockTraverserShallow:
      applyBlock(b)
      
      override def applyBlock(b: Block): Unit = b match
        case s: Scoped =>
          accessed.refdDefns.add(scopeData.getUID(s))
        case Assign(lhs, rhs, rest) =>
          accessed.mutated.add(lhs)
          applyResult(rhs)
          applyBlock(rest)
        case _ => super.applyBlock(b)
      
      override def applyValue(v: Value): Unit = v match
        case Value.Ref(_: BuiltinSymbol, _) => super.applyValue(v)
        case RefOfBms(_, S(dSym)) =>
          accessed.refdDefns.add(scopeData.getNode(dSym).obj.toInfo)
        case Value.Ref(l, _) =>
          accessed.accessed.add(l)
        case _ => super.applyValue(v)
    accessed.toIMut
    
  /**
    * Finds the variables belonging to a parent scope which this scoped object could possibly 
    * access or mutate, excluding mutations through calls to other functions and mutations 
    * of their own variables. Also finds the other scoped objects that this definition may enter.
    * 
    * @param obj The scoped object to search through.
    * @return The variables which this definition could possibly mutate.
    */
  private def findAccessesShallow(obj: ScopedObject): AccessInfo =
    val accessed = obj match
      case ScopedObject.Top(b) => b match
        case s: Scoped => blkAccessesShallow(s.body)
        case _ => blkAccessesShallow(b)
      case ScopedObject.Func(f, _) =>
        blkAccessesShallow(f.body)
      case ScopedObject.Class(c) =>
        // We must assume that classes may access all their methods.
        // When the class symbol is referenced once, that symbol may be used in
        // arbitrary ways, which includes calling any of this class's methods.
        val res = blkAccessesShallow(c.preCtor) ++ blkAccessesShallow(c.ctor)
        res.copy(refdDefns = res.refdDefns ++ c.methods.map(_.dSym))
      case ScopedObject.ScopedBlock(uid, b) =>
        blkAccessesShallow(b.body)
      case ScopedObject.Companion(c, _) =>
        // There likely won't be nested companion classes in the future, but for now,
        // just assume they may access all their methods
        val res = blkAccessesShallow(c.ctor)
        res.copy(refdDefns = res.refdDefns ++ c.methods.map(_.dSym))
    // Variables introduced by this scoped object do not belong to a parent scope, so
    // we remove them
    accessed.withoutLocals(obj.definedLocals)
  
  private def combineInfos(m1: Map[ScopedInfo, AccessInfo], m2: Map[ScopedInfo, AccessInfo]): Map[ScopedInfo, AccessInfo] =
    if m2.size < m1.size then combineInfos(m2, m1)
    else m1.foldLeft(m2):
      case (acc, info -> accesses) => m1.get(info) match
        case Some(value) => acc + (info -> (accesses ++ value))
        case None => acc + (info -> accesses)
  
  val shallowAccesses: Map[ScopedInfo, AccessInfo] =
    scopeData.scopeTree.root.allChildren.map(obj => obj.toInfo -> findAccessesShallow(obj)).toMap
  
  // Optimization: Find all nodes which are accessed by their children
  // See the comment for findAccesses
  private val allEdges =
    for 
      (src, accesses) <- shallowAccesses
      refd <- accesses.refdDefns
      if src =/= refd
    yield
      (src, refd)
  private val accessedByChild = allEdges
    .groupBy(_._2) // group by edge destination
    .map:
      case (_: Unit) -> _ => () -> false
      case d -> edges =>
        val par = scopeData.getNode(d).parent.get.obj.toInfo
        d -> edges.exists:
          case a -> b => a =/= par
    .collect:
      case d -> true => d
    .toSet

  // Find:
  // - Map 1:
  //    - Variables that each scoped object has accessed, either through itself or a nested scoped object.
  //    - Variables that each scoped object has mutated, either through itself or a nested scoped object.
  //    - Scoped objects that each object accesses, either through itself or a nested scoped object.
  // - Map 2:
  //    - Variables that each scoped object has accessed, either through itself or a *lifted* scoped object.
  //    - Variables that each scoped object has mutated, either through itself or a lifted nested scoped object.
  //    - Scoped objects that each object accesses, either through itself or a lifted nested scoped object.
  //
  // The former includes ignored objects, and is used to do the readers/writers analysis. The latter is used to determine
  // whether we actually need to allocate a capture for the object. In particular, we never need to allocate a capture
  // for a variable if only nested scopes mutate it.
  //
  // Note that it is possible for a lifted scoped object to be reached by traversing through an ignored object.
  // 
  // Also observe that if a node is not accesed from any of its children, then we can re-use the result of its parent's analysis.
  private def findAccesses(s: ScopeNode): (Map[ScopedInfo, AccessInfo], Map[ScopedInfo, AccessInfo]) =
    // Note: these include `s`
    val children = s.allChildren
    val childInfo = children.map(_.toInfo).toSet

    // Traverses the node's children, and stops when a child that is accessed by one of its children is found.
    // The analysis will be performed on *all* of the traversed nodes simultaneously.
    // We will later recurse on the children of all these nodes.
    val nexts: Buffer[ScopeNode] = Buffer.empty
    def findNodes(s: ScopeNode): List[ScopeNode] = s :: s.children.flatMap: child =>
      if accessedByChild(child.obj.toInfo) then
        nexts.addOne(child)
        List.empty
      else findNodes(child)
    val nodes = findNodes(s)
    
    val allLocals = nodes.flatMap(node => node.obj.definedLocals).toSet
    
    val accessInfo = children.map: obj =>
      val a @ AccessInfo(accessed, mutated, refdDefns) = shallowAccesses(obj.toInfo)
      obj.toInfo -> AccessInfo(
        accessed = accessed.intersect(allLocals),
        mutated = mutated.intersect(allLocals),
        refdDefns = refdDefns.intersect(childInfo)
      )
    
    val accessInfoMap = accessInfo.toMap
    val edges: Set[(ScopedInfo, ScopedInfo)] =
      for
        (src, AccessInfo(_, _, refd)) <- accessInfo
        r <- refd
        // remove self-edges: they do not affect this analysis
        if src =/= r
        // very important: we only care about edges that flow into the subtree rooted at `s`
        if childInfo.contains(r) && r =/= s.obj.toInfo
      yield src -> r
    .toSet
    
    // (sccs, sccEdges) forms a directed acyclic graph (DAG)
    val algorithms.SccsInfo(sccs, sccEdges, inDegs, outDegs) = algorithms.sccsWithInfo(edges, childInfo)

    val rootInfo = s.obj.toInfo
    val (rootId, rootElems) = sccs.find:
        case (id, elems) => elems.contains(rootInfo)
      .get
    if rootElems.size != 1 then lastWords("SCC containing root had a degree other than 1.")
    
    // With respect to the current scoped object, we may "ignore" one of its children if and only if
    // it is ignored (not lifted), and its first lifted parent is the current scoped object. We "ignore"
    // it in the sense that it does not need to capture the current scoped object's variables, nor does
    // it require the current scoped object to create a capture class for its accessed variables.
    def isIgnored(s1: ScopedInfo) =
      scopeData.getNode(s1).firstLiftedParent.toInfo === s.obj.toInfo

    // All objects in the same scc must have at least the same accesses as each other
    def go(includeIgnored: Bool) =
      val base = for (id, scc) <- sccs yield
        // If all objects in this SCC are ignored, then we treat it as if it does not access anything,
        // unless we explicitly want to count ignored items (for the readers-mutators analysis)
        if !includeIgnored && scc.forall(isIgnored) then id -> AccessInfo.empty
        else id -> scc.foldLeft(AccessInfo.empty):
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
      yield sym -> sccAccessInfo(id).withoutLocals(scopeData.getNode(sym).obj.definedLocals)
    
    val (m1, m2) = (go(true), go(false))
    val subCases = nexts.map(findAccesses)
    subCases.foldLeft((m1, m2)):
      case ((acc1, acc2), (new1, new2)) => (combineInfos(acc1, new1), combineInfos(acc2, new2))
  
  // Searching from the root makes no sense. We instead start searching from each scope nested in the top-level
  private val (m1, m2) = scopeData.scopeTree.root.children.map(findAccesses).unzip
  val accessMapWithIgnored = m1.foldLeft[Map[ScopedInfo, AccessInfo]](Map.empty)(_ ++ _)
  val accessMap = m2.foldLeft[Map[ScopedInfo, AccessInfo]](Map.empty)(_ ++ _)

  private def reqdCaptureLocals(s: ScopeNode): (Set[Local], Set[Local]) =
    def withMtds(b: Block, mtds: List[FunDefn]) =
      val (ctorRead, ctorCap) = reqdCaptureLocals(b, s.children, s.obj.definedLocals)
      // all the mutated variables shall require a capture
      val additional = mtds
        .map: mtd =>
          accessMap(scopeData.getNode(mtd).obj.toInfo)
        .foldLeft(AccessInfo.empty):
          case (acc, value) => acc ++ value
      (ctorRead ++ additional.accessed, ctorCap ++ additional.mutated)
    s.obj match
    case ScopedObject.Top(b) => lastWords("reqdCaptureLocals called on top block")
    case ScopedObject.Class(cls) => withMtds(Begin(cls.preCtor, cls.ctor), cls.methods)
    case ScopedObject.Companion(comp, _) => withMtds(comp.ctor, comp.methods)
    case ScopedObject.Func(fun, _) => reqdCaptureLocals(fun.body, s.children, s.obj.definedLocals)
    case ScopedObject.ScopedBlock(uid, block) => reqdCaptureLocals(block, s.children, s.obj.definedLocals)
  

  // readers-mutators analysis
  private def reqdCaptureLocals(b: Block, childNodes: List[ScopeNode], thisVars: Set[Local]): (Set[Local], Set[Local]) =
    val scopeInfos: Map[ScopedInfo, ScopeNode] = childNodes.map(node => node.obj.toInfo -> node).toMap

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
      
      new BlockTraverserShallow:
        applyBlock(b)
        override def applyBlock(b: Block): Unit = b match
          case s: Scoped =>
            handleCalledScope(scopeData.getUID(s))
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

        def handleCalledScope(called: ScopedInfo): Unit = scopeInfos.get(called) match
          case None => ()
          case Some(node) =>
            val AccessInfo(accessed, muted, refd) = accessMapWithIgnored(called)
            val muts = muted.intersect(thisVars)
            val reads = accessed.intersect(thisVars) -- muts
            // this not a naked reference. if it's a ref to a class, this can only ever create once instance
            // so the "one writer" rule applies
            for l <- muts do
              if hasReader.contains(l) || hasMutator.contains(l) || node.obj.isInstanceOf[ScopedObject.Func] then
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
              l <- accessMapWithIgnored(sym).mutated
            do
              reqCapture += l
              hasMutator += l

        override def applyResult(r: Result): Unit = 
          r match
          case Call(RefOfBms(_, S(d)), args) =>
            args.map(super.applyArg(_))
            handleCalledScope(d)
          case Instantiate(mut, InstSel(_, S(d)), args) =>
            args.map(super.applyArg)
            handleCalledScope(d)
          case _ => super.applyResult(r)
        
        override def applyPath(p: Path): Unit = p match
          case RefOfBms(_, S(d)) =>
            scopeInfos.get(d) match
            case None => super.applyPath(p)
            case Some(defn) =>
              val isMod = defn.obj.isInstanceOf[ScopedObject.Companion]
              if isMod then super.applyPath(p)
              else
                val AccessInfo(accessed, muted, refd) = accessMapWithIgnored(d)
                val muts = muted.intersect(thisVars)
                val reads = accessed.intersect(thisVars) -- muts
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
                  l <- accessMapWithIgnored(sym).mutated
                do
                  reqCapture += l
                  hasMutator += l
          
          case Value.Ref(l, _) =>
            if hasMutator.contains(l) then reqCapture += (l)
          case _ => super.applyPath(p)
        
        override def applyDefn(defn: Defn): Unit = defn match
          case c: ClsLikeDefn if modOrObj(c) =>
            handleCalledScope(c.isym)
            super.applyDefn(defn)
          case _ => super.applyDefn(defn)

      CaptureInfo(reqCapture, hasReader, hasMutator)

    val (usedVarsL, mutatedVarsL) = scopeInfos.map:
        case (info, node) =>
          val a = accessMap(info).intersectLocals(thisVars)
          (a.accessed, a.mutated)
      .unzip
    val usedVars = usedVarsL.foldLeft[Set[Local]](Set.empty)(_ ++ _)
    val mutatedVars = mutatedVarsL.foldLeft[Set[Local]](Set.empty)(_ ++ _)
    val reqCapture = go(b, Set.empty, Set.empty, Set.empty).reqCapture.intersect(mutatedVars)

    (usedVars, reqCapture)
  
  val reqdCaptures: Map[ScopedInfo, (Set[Local], Set[Local])] = scopeData.root.allChildNodes
    .filter(node => !node.obj.isInstanceOf[ScopedObject.Top])
    .map: node =>
      node.obj.toInfo -> reqdCaptureLocals(node)
    .toMap
