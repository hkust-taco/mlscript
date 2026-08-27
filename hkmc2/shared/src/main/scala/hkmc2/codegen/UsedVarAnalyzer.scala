package hkmc2

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.semantics.Elaborator.State
import hkmc2.ScopeData.*
import hkmc2.Lifter.*

import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.Buffer


object UsedVarAnalyzer:
  case class MutAccessInfo(
    accessed: MutSet[ScopedOrInnerSymbol], 
    mutated: MutSet[ScopedOrInnerSymbol], 
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
class UsedVarAnalyzer(b: Block, scopeData: ScopeData)(using State):
  import UsedVarAnalyzer.*
  
  object SDSym:
    def unapply(v: DefinitionSymbol[?] | Option[DefinitionSymbol[?]]) = dSymUnapply(scopeData, v)
  
  private def isObj(s: ScopeNode) = s.obj match
    case c: ScopedObject.Class if c.isObj => true
    case _ => false
  
  // Finds the locals that this block accesses/mutates, and the definitions which it could use.
  private def blkAccessesShallow(b: Block): AccessInfo =
    var accessed: MutAccessInfo = MutAccessInfo.empty
    new BlockTraverserShallow:
      applyBlock(b)
      
      override def applyBlock(b: Block): Unit = b match
        case s: Scoped =>
          accessed.refdDefns.add(scopeData.getUID(s))
        case Assign(lhs, rhs, rest) =>
          lhs match
          case NoSymbol => ()
          case lhs: ScopedOrInnerSymbol =>
            accessed.accessed.add(lhs)
            accessed.mutated.add(lhs)
          applyResult(rhs)
          applyBlock(rest)
        case l: Label if l.loop =>
          accessed.refdDefns.add(l.label)
          applySubBlock(l.rest)
        case d: Define => d.defn match
          case v: ValDefn =>
            applyDefn(v)
            applySubBlock(d.rest)
          case c @ ClsLikeDefn(k = syntax.Obj) =>
            accessed.refdDefns.add(c.isym)
          case _ => applySubBlock(d.rest)
        
        case _ => super.applyBlock(b)
      
      override def applyPath(p: Path): Unit = p match
        case Value.SimpleRef(_: BuiltinSymbol) => super.applyPath(p)
        case RefOfDefn(SDSym(dSym), _) =>
          val node = scopeData.getNode(dSym)
          node.obj match
            // Here, we add an edge to a definition, even if it is the result of a field selection, if it is:
            // - Lifted, but not an object
            // - Is a module method
            // - Is a ctor of a lifted class
            // Otherwise, we ignore the disambiguated symbol and traverse into the the selection's path. Once
            // we reach the "base" reference to an object, then we add a reference to that as required.
            
            case ScopedObject.Func(isMethod = S(MethodKind.ModMethod)) =>
              accessed.refdDefns.add(node.obj.toInfo)
              super.applyPath(p)
            case ScopedObject.Func(isMethod = N) =>
              accessed.refdDefns.add(node.obj.toInfo)
              super.applyPath(p)
            case ScopedObject.ValDef(_) =>
              accessed.refdDefns.add(node.obj.toInfo)
            case _ if node.isLifted && !isObj(node) => accessed.refdDefns.add(node.obj.toInfo)
            case ScopedObject.ClassCtor(cls) if scopeData.getNode(cls).isLifted => accessed.refdDefns.add(node.obj.toInfo)
            case _ => p match
              case _: Value.Ref => node.obj match
                case c: ScopedObject.Class if c.isObj =>
                  accessed.accessed.add(c.cls.isym)
                case r: ScopedObject.Referencable[?] if !node.isLifted =>
                  accessed.refdDefns.add(r.toInfo)
                case _: ScopedObject.Class | _: ScopedObject.ClassCtor | _: ScopedObject.Companion => accessed.refdDefns.add(node.obj.toInfo)
                case _ => ()
              case _ => super.applyPath(p)
        
        case Value.RefLike(sym: ScopedOrInnerSymbol) =>
          accessed.accessed.add(sym)
        case _ => super.applyPath(p)
    accessed.toIMut
  
  def getParentCls(c: ClsLikeDefn) = c.parentPath.flatMap:
    case RefOfDefn(SDSym(parentCls), _) => S(parentCls)
    case _ => N
    
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
      case ScopedObject.Class(c, _) =>
        // We must assume that classes may access all their methods.
        // When the class symbol is referenced once, that symbol may be used in
        // arbitrary ways, which includes calling any of this class's methods.
        val res = blkAccessesShallow(c.preCtor) ++ blkAccessesShallow(c.ctor)
        val parentClsSym = getParentCls(c)
        res.copy(refdDefns = res.refdDefns ++ c.methods.map(_.dSym) ++ parentClsSym.toSet)
      case ScopedObject.ClassCtor(cls) =>
        // Recall that we interpret the ctor as just another function in the same scope
        // as the corresponding class, and initializes the class.
        AccessInfo.empty.addRefdScopedObj(scopeData.getNode(cls).obj.toInfo)
      case ScopedObject.ScopedBlock(uid, b) => blkAccessesShallow(b.body)
      case ScopedObject.Companion(c, _) =>
        // There likely won't be nested companion classes in the future, but for now,
        // just assume they may access all their methods
        val res = blkAccessesShallow(c.ctor)
        res.copy(refdDefns = res.refdDefns ++ c.methods.map(_.dSym))
      case ScopedObject.Loop(_, b) => blkAccessesShallow(b)
      case ScopedObject.ValDef(v) => AccessInfo.empty
    // Variables introduced by this scoped object do not belong to a parent scope, so
    // we remove them
    accessed.withoutLocals(obj.definedLocals)
  
  private def combineInfos(m1: Map[ScopedInfo, AccessInfo], m2: Map[ScopedInfo, AccessInfo]): Map[ScopedInfo, AccessInfo] =
    if m2.size < m1.size then combineInfos(m2, m1)
    else
      m2 ++
      m1.iterator.map: (k, v) =>
        k -> m2.get(k).fold(v)(_ ++ v)
  
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
    val (nodes, nexts) = s.partitionTree(x => accessedByChild(x.obj.toInfo))
    
    val allLocals = nodes.flatMap(node => node.obj.definedLocals).toSet
    
    val accessInfo = children.map: obj =>
      val a @ AccessInfo(accessed, mutated, refdDefns) = shallowAccesses(obj.toInfo)
      obj.toInfo -> AccessInfo(
        accessed = accessed.intersect(allLocals),
        mutated = mutated.intersect(allLocals),
        refdDefns = refdDefns.intersect(childInfo)
      )
    
    val accessInfoMap = accessInfo.toMap
    val rootInfo = s.obj.toInfo

    // The out-edges of `src` inside the subtree rooted at `s`
    def refdInSubtree(src: ScopedInfo): Iterator[ScopedInfo] =
      accessInfoMap(src).refdDefns.iterator.filter: r =>
        // remove self-edges: they do not affect this analysis
        src =/= r &&
        // very important: we only care about edges that flow into the subtree rooted at `s`
        childInfo.contains(r) && r =/= rootInfo
    
    // With respect to the current scoped object `s`, we may "ignore" one of its children `c` if and only if
    // it is ignored (not lifted), and `s` is in the subtree rooted at the first lifted parent of `c`. We
    // "ignore" `c` in the sense that it does not need to capture `s`'s scoped object's variables, nor does
    // it require the current scoped object to create a capture class for its accessed variables.
    def isIgnored(c: ScopedInfo) =
      s.inSubtree(scopeData.getNode(c).firstLiftedAncestor.toInfo)

    // All objects in the same scc must have at least the same accesses as each other.
    // An scc is handled only once every scc reachable from it has been handled, which is the
    // same as materializing the scc dag graph first and then dp on it.
    val withIgnored = MutMap.empty[ScopedInfo, AccessInfo]
    val withoutIgnored = MutMap.empty[ScopedInfo, AccessInfo]
    object sccTraversal extends SccAnalysis[ScopedInfo]:
      protected def successors(n: ScopedInfo) = refdInSubtree(n)
      protected def isHandled(n: ScopedInfo) = withIgnored.contains(n)
      protected def handleScc(members: Ls[ScopedInfo], sccId: Int): Unit =
        if members.contains(rootInfo) && members.size != 1 then
          lastWords("SCC containing root had a degree other than 1.")
        val united = members.foldLeft(AccessInfo.empty):
          case (acc, sym) => acc ++ accessInfoMap(sym)
        val succs = members.iterator.flatMap(refdInSubtree).toSet
        def foldSuccs(dp: MutMap[ScopedInfo, AccessInfo], base: AccessInfo): AccessInfo =
          succs.iterator.flatMap(dp.get).foldLeft(base):
            case (acc, next) => acc ++ next
        // If all objects in this SCC are ignored, then we treat it as if it does not access anything,
        // unless we explicitly want to count ignored items (for the readers-mutators analysis)
        val ignoredDropped = foldSuccs(withoutIgnored,
          if members.forall(isIgnored) then AccessInfo.empty else united)
        val ignoredIncluded = foldSuccs(withIgnored, united)
        members.foreach: sym =>
          withIgnored(sym) = ignoredIncluded
          withoutIgnored(sym) = ignoredDropped
    end sccTraversal
    
    sccTraversal.queryAll(childInfo)

    // Remove locals that are not yet defined
    def removeUnused(dp: collection.Map[ScopedInfo, AccessInfo]): Map[ScopedInfo, AccessInfo] =
      dp.iterator.map: (info, accesses) =>
        val node = scopeData.getNode(info)
        info -> accesses.intersectLocals(node.existingVars)
      .toMap

    val m1 = removeUnused(withIgnored)
    val m2 = removeUnused(withoutIgnored)
    
    val subCases = nexts.map(findAccesses)
    subCases.foldLeft((m1, m2)):
      case ((acc1, acc2), (new1, new2)) => (combineInfos(acc1, new1), combineInfos(acc2, new2))

  private def reqdCaptureLocals(s: ScopeNode): Map[ScopedInfo, Set[ScopedOrInnerSymbol]] =
    val (blk, parentCls) = s.obj match
      case ScopedObject.Top(b) => lastWords("reqdCaptureLocals called on top block")
      case ScopedObject.Class(cls, _) => (Begin(cls.preCtor, cls.ctor), getParentCls(cls))
      case ScopedObject.Companion(comp, _) => (comp.ctor, N)
      case ScopedObject.Func(fun, _) => (fun.body, N)
      case ScopedObject.ScopedBlock(uid, block) => (block, N)
      case ScopedObject.Loop(sym, block) => (block, N)
      case ScopedObject.ValDef(_) | ScopedObject.ClassCtor(_) => return Map.empty + (s.obj.toInfo -> Set.empty)

    val (nodes, nexts) = s.partitionTree2:
      case obj: (ScopedObject.ScopedBlock | ScopedObject.Loop | ScopedObject.ValDef) => false
      case _ => true
    
    val locals = nodes.flatMap(_.obj.definedLocals).toSet
    
    val cap = reqdCaptureLocalsBlk(blk, parentCls, nexts.toList, s.obj.definedLocals, locals)
    
    val cur: Map[ScopedInfo, Set[ScopedOrInnerSymbol]] = nodes.map: n =>
        n.obj.toInfo -> cap.intersect(n.obj.definedLocals.map(s => s: ScopedOrInnerSymbol))
      .toMap
    
    nexts.foldLeft(cur):
      case (mp, acc) => mp ++ reqdCaptureLocals(acc)

  // readers-mutators analysis
  private def reqdCaptureLocalsBlk(
    b: Block,
    superClass: Opt[DefinitionSymbol[?]],
    nextNodes: List[ScopeNode],
    startingVars: Set[ScopedOrInnerSymbol],
    thisVars: Set[ScopedOrInnerSymbol]
  ): Set[ScopedOrInnerSymbol] =
    val scopeInfos: Map[ScopedInfo, ScopeNode] = nextNodes.map(node => node.obj.toInfo -> node).toMap

    case class CaptureInfo(reqCapture: Set[ScopedOrInnerSymbol], hasReader: Set[ScopedOrInnerSymbol], hasMutator: Set[ScopedOrInnerSymbol], mutated: Set[ScopedOrInnerSymbol])
    
    // linearVars denotes the variables defined inside the scopes up to the nearest loop or the top level block.
    // If a loop modifies a non-linear variable and then one of its nested definitions accesses it, we must put put
    // that variable in a capture.
    def go(b: Block, reqCapture_ : Set[ScopedOrInnerSymbol], hasReader_ : Set[ScopedOrInnerSymbol], hasMutator_ : Set[ScopedOrInnerSymbol], mutated_ : Set[ScopedOrInnerSymbol])(using linearVars: Set[ScopedOrInnerSymbol]): CaptureInfo =
      var reqCapture = reqCapture_
      var hasReader = hasReader_
      var hasMutator = hasMutator_
      // note: the meaning of `mutated` is a bit strange: it basically means variables which are currently not linear that have been mutated
      // if a variable is in this set but is linear, then it's ignored
      var mutated = mutated_
      def linearValueVars = linearVars.map(s => s: ValueSymbol)

      inline def merge(c: CaptureInfo) =
        reqCapture ++= c.reqCapture
        hasReader ++= c.hasReader
        hasMutator ++= c.hasMutator
        mutated ++= c.mutated

      def rec(blk: Block)(using linearVars: Set[ScopedOrInnerSymbol]) =
        go(blk, reqCapture, hasReader, hasMutator, mutated_)
      
      new BlockTraverserShallow:
        applyBlock(b)
        override def applyBlock(b: Block): Unit = b match
          // Note that we traverse directly into scoped blocks without using handleCalledScope
          case s: Scoped =>
            rec(s.body)(using linearVars = linearVars ++ s.syms) |> merge
          case l: Label if l.loop =>
            rec(l.body)(using linearVars = Set.empty) |> merge
            applySubBlock(l.rest)
          case Assign(lhs, rhs, rest) =>
            applyResult(rhs)
            lhs match
            case NoSymbol => ()
            case lhs: ScopedOrInnerSymbol =>
              if hasReader.contains(lhs) || hasMutator.contains(lhs) then reqCapture += lhs
              if !linearValueVars.contains(lhs) then mutated += lhs
            applySubBlock(rest)
          case Define(c @ ClsLikeDefn(k = syntax.Obj), rest) =>
            handleCalledScope(c.isym)
            applySubBlock(rest)
          case Define(v: ValDefn, rest) =>
            applyPath(v.rhs)
            applySubBlock(rest)
          case Match(scrut, arms, dflt, rest) =>
            applyPath(scrut)
            val infos = arms.map:
              case (_, arm) => rec(arm)
            val dfltInfo = dflt.map:
              case arm => rec(arm)
            
            infos.foreach(merge) // IMPORTANT: rec all first, then merge, since each branch is mutually exclusive
            dfltInfo.foreach(merge)
            applySubBlock(rest)
          case Begin(sub, rest) =>
            rec(sub) |> merge
            applySubBlock(rest)
          case TryBlock(sub, finallyDo, rest) =>
            // sub and finallyDo could be executed sequentially, so we must merge
            rec(sub) |> merge
            rec(finallyDo) |> merge
            applySubBlock(rest)
          case Return(res) =>
            applyResult(res)
            hasReader = Set.empty
            hasMutator = Set.empty
          case _ => super.applyBlock(b)

        def handleCalledScope(called: ScopedInfo): Unit = scopeInfos.get(called) match
          case None => ()
          case Some(node) =>
            node.obj match
              // ignore method calls to class or object methods
              case ScopedObject.Func(_, S(MethodKind.ClsMethod | MethodKind.ObjMethod)) => return
              case _ => ()
            
            val AccessInfo(accessed, muted, refd) = accessMapWithIgnored(called)
            val muts = muted.intersect(thisVars)
            val reads = accessed.intersect(thisVars) -- muts
            val refdExcl = refd.filter: sym =>
              scopeData.getNode(sym).obj match
                case s: ScopedObject.ScopedBlock => false
                case ScopedObject.Func(_, S(MethodKind.ClsMethod | MethodKind.ObjMethod)) => false
                case _ => true
            
            // This not a naked reference. If it's a ref to a class, this can only ever create once instance
            // so the "one writer" rule applies.
            // However, if the control flow is not linear, we are forced to add all the mutated variables
            for l <- muts do
              if hasReader.contains(l) || hasMutator.contains(l) || !linearValueVars.contains(l) then
                reqCapture += l
              hasReader += l
              hasMutator += l
              mutated += l
            for l <- reads do
              if hasMutator.contains(l) then
                reqCapture += l
              if mutated.contains(l) && !linearValueVars.contains(l) then
                reqCapture += l
              hasReader += l
            // if this defn calls another defn that creates a class or has a naked reference to a
            // function, we must capture the latter's mutated variables in a capture, as arbitrarily
            // many mutators could be created from it
            for
              sym <- refdExcl
              l <- accessMapWithIgnored(sym).mutated
            do
              reqCapture += l
              hasMutator += l
        
        def handleScopeRef(s: ScopedInfo) = scopeInfos.get(s) match
          case None => // super.applyPath(p)
          case Some(defn) =>
            val isModOrObj = defn.obj match
              case c: ScopedObject.Companion => true
              case c: ScopedObject.Class => c.isObj
              case _ => false
            if isModOrObj then () //super.applyPath(p)
            else
              val AccessInfo(accessed, muted, refd) = accessMapWithIgnored(s)
              val muts = muted.intersect(thisVars)
              val reads = accessed.intersect(thisVars) -- muts
              // this is a naked reference, we assume things it mutates always needs a capture
              for l <- muts do
                reqCapture += l
                hasMutator += l
              for l <- reads do
                if hasMutator.contains(l) then
                  reqCapture += l
                if mutated.contains(l) && !linearValueVars.contains(l) then
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
          case Call(Value.RefLike(sym), argss) if sym === State.superSymbol =>
            argss.foreach(_.foreach(super.applyArg(_)))
            superClass.foreach: d =>
              handleCalledScope(d)
          case Call(RefOfDefn(SDSym(d), _), argss) =>
            argss.foreach(_.foreach(super.applyArg(_)))
            val numArgLists = scopeData.getNode(d).obj match
              case ScopedObject.Func(fun, _) => fun.params.size.min(1)
              case ScopedObject.Class(c, false) => c.paramsOpt.map(_.params.size).getOrElse(0).min(1)
              case ScopedObject.ClassCtor(c) => c.paramsOpt.map(_.params.size).getOrElse(0).min(1)
              case _: ScopedObject.ValDef => return
              case _ => die
            
            // Partial call; the resulting object requiring access to the scope may linger
            if numArgLists != argss.size then handleScopeRef(d)
             // Fully applied, we can treat it as a call
            else handleCalledScope(d)
          case Instantiate(mut, RefOfDefn(SDSym(d), _), argss) =>
            argss.foreach(_.foreach(super.applyArg(_)))
            handleCalledScope(d)
          case _ => super.applyResult(r)
        
        override def applyPath(p: Path): Unit = p match
          case RefOfDefn(SDSym(d), _) => handleScopeRef(d)
          case Value.RefLike(sym: ScopedOrInnerSymbol) =>
            if hasMutator.contains(sym) then reqCapture += sym
          case _ => super.applyPath(p)
        
        override def applyDefn(defn: Defn): Unit = defn match
          case c: ClsLikeDefn if modOrObj(c) =>
            handleCalledScope(c.isym)
            super.applyDefn(defn)
          case _ => super.applyDefn(defn)

      CaptureInfo(reqCapture, hasReader, hasMutator, mutated)
    
    val reqCapture = go(b, Set.empty, Set.empty, Set.empty, Set.empty)(using linearVars = startingVars).reqCapture
    reqCapture.intersect(thisVars)
  
  // entry point
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
        val par = scopeData.getNode(d).ancestor.get.obj.toInfo
        d -> edges.exists:
          case a -> b => a =/= par
    .collect:
      case d -> true => d
    .toSet
  
  // Searching from the root makes no sense. We instead start searching from each scope nested in the top-level
  private val (m1, m2) = scopeData.scopeTree.root.children.map(findAccesses).unzip
  val accessMapWithIgnored = m1.foldLeft[Map[ScopedInfo, AccessInfo]](Map.empty)(_ ++ _)
  val accessMap = m2.foldLeft[Map[ScopedInfo, AccessInfo]](Map.empty)(_ ++ _)
  
  // We make these lazy, because not all users of UsedVarAnalyzer need this analysis. For now, only the lifter needs it.
  
  lazy val reqdCaptures: Map[ScopedInfo, Set[ScopedOrInnerSymbol]] = scopeData.root.children.foldLeft(Map.empty):
    case (acc, node) => acc ++ reqdCaptureLocals(node)
  
  // For local inside a capture, finds the node to which this local belongs.
  lazy val capturesMap =
    for
      case (info -> reqCap) <- reqdCaptures
      s <- reqCap
    yield s -> info
