package hkmc2

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.ScopeData.*
import hkmc2.semantics.Elaborator.State

import hkmc2.syntax.Tree
import java.util.IdentityHashMap
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet


object ScopeData:
  opaque type ScopeUID = Int
  class FreshUID:
    private val underlying = new Uid.Symbol.State
    def make: ScopeUID = underlying.nextUid.asInt
  
  class ScopeFinder(fresh: FreshUID, ignoredClasses: Set[DefinitionSymbol[?] & InnerSymbol]) extends BlockTraverserShallow:
    var objs: List[ScopedObject] = Nil
    override def applyBlock(b: Block): Unit = b match
      case s: Scoped =>
        val id = fresh.make
        objs ::= ScopedObject.ScopedBlock(id, s)
      case l: Label if l.loop =>
        objs ::= ScopedObject.Loop(l.label, l.body)
        applySubBlock(l.rest)
      case _ => super.applyBlock(b)
    override def applyFunDefn(fun: FunDefn): Unit =
      objs ::= ScopedObject.Func(fun, N)
    override def applyDefn(defn: Defn): Unit = defn match
      case f: FunDefn => applyFunDefn(f)
      case c: ClsLikeDefn =>
        if !ignoredClasses.contains(c.isym) then
          objs ::= ScopedObject.Class(c, c.k === syntax.Obj)
          c.ctorSym match
            case Some(value) => objs ::= ScopedObject.ClassCtor(c)
            case None => ()
          c.companion.map: comp =>
            objs ::= ScopedObject.Companion(comp, c)
      case v: ValDefn if !v.owner.isDefined => objs ::= ScopedObject.ValDef(v)
      case _ => super.applyDefn(defn)
  type ScopedInfo = DefinitionSymbol[?] | LabelSymbol | ScopeUID | Unit

  given Ordering[ScopedInfo] with
    def compare(x: ScopedInfo, y: ScopedInfo): Int = (x, y) match
      case (a: Symbol, b: Symbol) => Ordering[Uid[Symbol]].compare(a.uid, b.uid)
      case (_: Symbol, _) => -1
      case (_, _: Symbol) => 1
      case ((), ()) => 0
      case ((), _) => -1
      case (_, ()) => 1
      case (a: Int, b: Int) => a compare b // ScopeUID is Int inside ScopeData

  // ScopeData requires the set of ignored scopes to compute certain things, but
  // the lifter requires the scope tree to generate the metadata. To solve this,
  // we generate the scope tree then populate the metadata later.
  case class IgnoredScopes(var ignored: Opt[Set[ScopedInfo]])
  
  type ScopedObject = ScopedObject.ScopedObject[?]
  type TScopedObject[T] = ScopedObject.ScopedObject[T]
  
  type LiftedSym = DefinitionSymbol[?]
  
  extension (d: DefinitionSymbol[?])
    def asBmsRef = d.asBlkMember.get.asMemberRef(d)
  
  enum MethodKind:
    case ClsMethod
    case ObjMethod
    case ModMethod
  
  // These cannot be hashed
  object ScopedObject:
    // T: The actual contents of the scoped object
    sealed abstract class ScopedObject[T]:
      var node: Opt[TScopeNode[T]] = N
      lazy val toInfo: ScopedInfo = this match
        case Top(_) => ()
        case Class(cls, _) => cls.isym
        case Companion(clsBody, compDefn) => clsBody.isym
        case ClassCtor(cls) => cls.ctorSym.get
        case Func(fun, _) => fun.dSym
        case ScopedBlock(uid, block) => uid
        case Loop(sym, _) => sym
        case ValDef(v) => v.tsym
      
      // note: not unique
      lazy val nme = this match
        case Top(b) => "top"
        case Class(cls, _) => cls.isym.nme
        case Companion(clsBody, compDefn) => clsBody.isym.nme + "_mod"
        case ClassCtor(cls) => cls.isym.nme // should be unused
        case Func(fun, isMethod) => fun.dSym.nme
        case Loop(sym, block) => "loop$" + sym.uid.toString()
        case ScopedBlock(uid, block) => "scope" + uid
        case ValDef(v) => v.tsym.nme
      
      // Locals defined by a scoped object.
      lazy val definedLocals: Set[ScopedOrInnerSymbol] = this match
        // we want definedLocals for the top level scope to be empty, because otherwise,
        // the lifter may try to capture those locals.
        case Top(b) => Set.empty
        case Class(cls, _) =>
          // Public/private fields are not included, as they are accessed using
          // a field selection rather than directly using the symbol.
          val paramsSet: Set[ScopedOrInnerSymbol] = cls.paramsOpt match
            case Some(value) => value.params.map(_.sym).toSet
            case None => Set.empty
          val auxSet: Set[ScopedOrInnerSymbol] = cls.auxParams.flatMap: p =>
              p.params.map(_.sym)
            .toSet
          paramsSet ++ auxSet + cls.isym
        case Companion(clsBody, compDefn) => Set(clsBody.isym)
        case _: ClassCtor => Set.empty
        case Func(fun, _) => fun.params.flatMap: p =>
            p.restParam.map(_.sym) ++ p.params.map(_.sym)
          .toSet
        case ScopedBlock(_, block) => block.syms.toSet
        case _: Loop => Set.empty
        case ValDef(_) => Set.empty
    
      def contents: T = this match
        case Top(b) => b
        case Class(cls, _) => cls
        case Companion(clsBody, compDefn) => clsBody
        case ClassCtor(cls) => ()
        case Func(fun, _) => fun
        case ScopedBlock(_, block) => block
        case Loop(_, blk) => blk
        case ValDef(v) => v
    
    // Scoped nodes which may be referenced using a symbol.
    sealed abstract class Referencable[T] extends TScopedObject[T]:
      def sym: LiftedSym = this match
        case Class(cls, _) => cls.isym
        case Companion(clsBody, compDefn) => clsBody.isym
        case Func(fun, isMethod) => fun.dSym
        case ClassCtor(cls) => cls.ctorSym.get
        case ValDef(v) => v.tsym
      def bsym: BlockMemberSymbol = this match
        case Class(cls, _) => cls.sym
        case Companion(clsBody, compDefn) => compDefn.sym
        case Func(fun, isMethod) => fun.sym
        case ClassCtor(cls) => cls.sym
        case ValDef(v) => v.sym
      def owner: Opt[InnerSymbol] = this match
        case Class(cls, _) => cls.owner
        case Companion(clsBody, compDefn) => compDefn.owner
        case ClassCtor(cls) => cls.owner
        case Func(fun, isMethod) => fun.owner
        case ValDef(v) => v.owner
      
    
    // Scoped nodes which could possibly be lifted to the top level.
    sealed abstract class Liftable[T <: Defn] extends Referencable[T]:
      val defn: T
    
    // The top-level scope.
    case class Top(b: Block) extends ScopedObject[Block] // b may be a scoped block, in which case, its variables represent the top-level variables.
    case class Class(cls: ClsLikeDefn, isObj: Bool) extends Liftable[ClsLikeDefn]:
      val defn = cls
    case class Companion(clsBody: ClsLikeBody, compDefn: ClsLikeDefn) extends Referencable[ClsLikeBody]
    // We model it like this: the ctor is just another function in the same scope as the class and initializes the corresponding class
    case class ClassCtor(cls: ClsLikeDefn) extends Referencable[Unit]
    // isMethod:
    // N = not a method
    // S(false) = module method
    // S(true) = class or object method
    case class Func(fun: FunDefn, isMethod: Opt[MethodKind]) extends Liftable[FunDefn]:
      val defn = fun
    // The purpose of `Loop` is to enforce the rule that the control flow remains linear when we enter
    // a scoped block.
    case class Loop(sym: LabelSymbol, body: Block) extends ScopedObject[Block]
    case class ScopedBlock(uid: ScopeUID, block: Scoped) extends ScopedObject[Block]
    case class ValDef(defn: ValDefn) extends Referencable[ValDefn]
  
  extension (traverser: BlockTraverser)
    def applyScopedObject(obj: ScopedObject) = 
      extension (s: Symbol) def traverse =
        traverser.applySymbol(s)
      obj match
      case ScopedObject.Top(b) => traverser.applyBlock(b)
      case ScopedObject.Class(ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
          privateFields, publicFields, preCtor, ctor, mod, bufferable), _)
      =>
        // do not traverse the companion -- it is a separate kind of scoped object
        // and will therefore be traversed separately
        own.foreach(_.traverse)
        isym.traverse
        sym.traverse
        ctorSym.foreach(_.traverse)
        paramsOpt.foreach(traverser.applyParamList)
        auxParams.foreach(traverser.applyParamList)
        parentPath.foreach(traverser.applyPath)
        methods.foreach(traverser.applyFunDefn)
        privateFields.foreach(_.traverse)
        publicFields.foreach: f =>
          f._1.traverse; f._2.traverse
        traverser.applySubBlock(preCtor)
        traverser.applySubBlock(ctor)
      case ScopedObject.Companion(comp, cls) => traverser.applyCompanionModule(comp)
      case ScopedObject.Func(fun, isMethod) => traverser.applyFunDefn(fun)
      case ScopedObject.ScopedBlock(uid, block) => traverser.applyBlock(block)
      case ScopedObject.ClassCtor(c) => ()
      case ScopedObject.Loop(_, b) => traverser.applyBlock(b)
      case ScopedObject.ValDef(v) => traverser.applyDefn(v)
    
  // A simple tree data structure representing the nesting relation of definitions and scopes.
  class NestedScopeTree(val root: TScopeNode[Block]):
    val nodesMap: Map[ScopedInfo, ScopeNode] = root.allChildNodes.map(n => n.obj.toInfo -> n).toMap
  
  type ScopeNode = ScopeNode.ScopeNode[?]
  type TScopeNode[T] = ScopeNode.ScopeNode[T]
  object ScopeNode:
    case class ScopeNode[T](obj: TScopedObject[T], var ancestor: Opt[ScopeNode[?]], children: List[ScopeNode[?]])(using ignoredScopes: IgnoredScopes):
      
      lazy val allAncestors: List[ScopeNode[?]] = ancestor match
        case Some(value) => this :: value.allAncestors
        case None => this :: Nil
      
      lazy val parentsSet = allAncestors.map(_.obj.toInfo).toSet
      
      def inSubtree(root: ScopedInfo) = parentsSet.contains(root)
      
      // note: includes itself
      lazy val allChildNodes: List[ScopeNode[?]] = this :: children.flatMap(_.allChildNodes)
      lazy val allChildren: List[ScopedObject] = allChildNodes.map(_.obj)
      
      // does not include variables introduced by itself
      lazy val existingVars: Set[ScopedOrInnerSymbol] = ancestor match
        case Some(value) => value.existingVars ++ value.obj.definedLocals ++ value.nestedModObjSyms
        case None => Set.empty
      
      lazy val inModOrTopLevel: Bool = ancestor match
        case Some(par) => par.obj match
          case _: ScopedObject.Companion => true
          case _: ScopedObject.Top => true
          case _ => false
        case None => true
      
      // Scoped blocks include the BlockMemberSymbols of their nested definitions. This removes them.
      lazy val localsWithoutBms: Set[ScopedOrInnerSymbol] = obj match
        case s: ScopedObject.ScopedBlock =>
          val rmv = children.collect:
            case c @ ScopeNode(obj = s: ScopedObject.Referencable[?]) => s.bsym
          obj.definedLocals -- rmv
        case _ => obj.definedLocals
      
      lazy val nestedModObjSyms: Set[InnerSymbol] = children.collect:
          case ScopeNode(obj = c: ScopedObject.Class) if c.isObj => c.cls.isym
          case ScopeNode(obj = c: ScopedObject.Companion) => c.clsBody.isym
        .toSet
      
      lazy val liftedObjSyms: Set[InnerSymbol] = children.collect:
          case n @ ScopeNode(obj = c: ScopedObject.Class) if c.isObj && n.isLifted => c.cls.isym
        .toSet
      
      lazy val inScopeISyms: Set[InnerSymbol] =
        val parVals = ancestor match
          case Some(value) => value.inScopeISyms
          case None => Set.empty
        
        obj match
        case c: ScopedObject.Class => parVals + c.cls.isym
        case c: ScopedObject.Companion => parVals + c.clsBody.isym
        case _ => parVals
      
      /**
        * Partitions the nodes of the scope tree into two lists `as` and `bs`, where:
        * - `bs` contains the the highest children of the curent node such that `f(b)` is `true` for `b` in `bs`, and
        * - `as` contains the parents of all nodes in `bs`.
        * 
        * @param f The predicicate used to partition the tree.
        * @return The partitioned tree.
        */
      def partitionTree(f: ScopeNode[?] => Bool): (List[ScopeNode[?]], List[ScopeNode[?]]) =
        val (as, bs) = children.foldLeft((List.empty[ScopeNode[?]], List.empty[ScopeNode[?]])):
          case ((l1, l2), child) =>
            if f(child) then (l1, child :: l2)
            else 
              val (l1_, l2_) = child.partitionTree(f)
              (l1_ ::: l1, l2_ ::: l2)
        (this :: as, bs)
      
      /**
        * Partitions the nodes of the scope tree into two lists `as` and `bs`, where:
        * - `bs` contains the the highest children of the curent node such that `f(b.obj)` is `true` for `b` in `bs`, and
        * - `as` contains the parents of all nodes in `bs`.
        * 
        * @param f The predicicate used to partition the tree.
        * @return The partitioned tree.
        */
      def partitionTree2(f: ScopedObject => Bool): (List[ScopeNode[?]], List[ScopeNode[?]]) = partitionTree(x => f(x.obj))
      
      // All of the following must not be called until ignoredScopes is populated with the relevant data.
      
      lazy val isLifted: Bool =
        def impl: Bool =
          val ignored = ignoredScopes.ignored match
            case Some(value) => value
            case None => lastWords("isLifted accessed before the set of ignored scopes was set")
          
          // check if the owner is a module
          obj match
            case r: ScopedObject.Referencable[?] => r.owner match
              case Some(value) => if value.asMod.isDefined then return false
              case _ => ()
            case _ => ()
          
          ancestor.map(_.obj) match
          case Some(_: ScopedObject.Companion) => false // there is no need to lift objects nested inside a module
          case _ =>
            obj match
            case _ if ignored.contains(obj.toInfo) => false
            case _ if inModOrTopLevel => false
            case ScopedObject.Func(isMethod = S(_)) => false
            case c: ScopedObject.Class if c.isObj => false
            case _: ScopedObject.Loop | _: ScopedObject.ClassCtor | _: ScopedObject.ScopedBlock | _: ScopedObject.Companion | _: ScopedObject.ValDef => false
            case _ => true
        impl
      
      // Finds the first ancestor that is a lifted object, i.e. a non-ignored definition, or the top level
      lazy val firstLiftedAncestor: ScopedObject =
        if !isLifted then
          ancestor match
          case Some(value) => value.firstLiftedAncestor
          case None => obj match
            case _: ScopedObject.Top => obj
            case _ => lastWords("unreachable")
        else obj
      
      // When a node is lifted, some neighbouring ignored definitions may become out of scope. This computes
      // the list of these definitions, and they could be passed to this node as a parameter once lifted.
      private lazy val reqCaptureObjsImpl: List[ScopedObject.Referencable[?]] = obj match
        case _: ScopedObject.Top => List.empty
        case _ =>
          // All unlifted neighbour nodes ::: ancestor's reqCaptureObjsImpl
          val initial = ancestor.get.children
            .filter:
              case ScopeNode(obj = f: ScopedObject.Func) if f.isMethod.isDefined => false
              case _ => true
            .collect:
              case c @ ScopeNode(obj = t: ScopedObject.Referencable[?]) if !c.isLifted && !inModOrTopLevel && !(t is obj) => t
          initial ::: ancestor.get.reqCaptureObjsImpl
      
      lazy val reqCaptureObjs: List[ScopedObject.Referencable[?]] = obj match
        case _: ScopedObject.Top => List.empty
        case _ =>
          if isLifted then reqCaptureObjsImpl
          else ancestor.get.reqCaptureObjsImpl
    
  
  def dSymUnapply(data: ScopeData, v: DefinitionSymbol[?] | Option[DefinitionSymbol[?]]) = v match
    case Some(d) if data.contains(d) => S(d)
    case d: DefinitionSymbol[?] if data.contains(d) => S(d)
    case _ => None
    
class ScopeData(b: Block)(using State, IgnoredScopes):
  import ScopeData.*
  
  def contains(s: ScopedInfo) = scopeTree.nodesMap.contains(s)
  
  def getNode(x: ScopedInfo): ScopeNode = scopeTree.nodesMap(x)
  def getNode(defn: ClsLikeDefn): ScopeNode = getNode(defn.isym)
  def getNode(companion: ClsLikeBody): ScopeNode = getNode(companion.isym)
  def getNode(defn: FunDefn): ScopeNode = getNode(defn.dSym)
  def getUID(blk: Scoped): ScopeUID =
    if scopedMap.containsKey(blk) then scopedMap.get(blk)
    else lastWords("getUID: key not found")
  def getNode(blk: Scoped): ScopeNode = getNode(getUID(blk))
  // From the input block or definition, traverses until a function, class or new scoped block is found and appends them.
  
  // Classes with owners are ignored, as they could be defined within a scoped block within the constructor.
  // We instead add all these classes when we encounter them.
  def scopeFinder = new ScopeFinder(fresh, classesWithOwner.keySet)
  
  // entry point
  private val fresh = FreshUID()
  
  private val (classesWithOwner, classesMap) =
    val mp1: MutMap[DefinitionSymbol[?] & InnerSymbol, InnerSymbol] = MutMap.empty
    val mp2: MutMap[InnerSymbol, ClsLikeDefn] = MutMap.empty
    new BlockTraverser:
      applyBlock(b)
      override def applyDefn(defn: Defn): Unit = defn match
        case c @ ClsLikeDefn(owner = S(own)) =>
          mp1.put(c.isym, own)
          mp2.put(c.isym, c)
          c.companion.foreach: comp =>
            mp1.put(comp.isym, own)
          super.applyDefn(c)
        case _ => super.applyDefn(defn)
    (mp1.toMap, mp2.toMap)
  
  private val ownersInv: Map[InnerSymbol, List[DefinitionSymbol[?] & InnerSymbol]] = classesWithOwner
    .toList.groupBy(_._2)
    .map:
      case k -> v => k -> v.map(_._1)
    .toMap
  
  val scopeTree = NestedScopeTree(makeScopeTreeRec(ScopedObject.Top(b)))
  val root = scopeTree.root
  val allBms = root.allChildren.collect:
    case s: ScopedObject.Referencable[?] => s.bsym
  private val scopedMap: IdentityHashMap[Scoped, ScopeUID] = new IdentityHashMap
  for
    case ScopeNode(obj = ScopedObject.ScopedBlock(uid, blk)) <- scopeTree.root.allChildNodes
  do
    scopedMap.put(blk, uid)
  
  def makeScopeTreeRec[T](obj: TScopedObject[T]): TScopeNode[T] =
    // An annoying thing with class ctors:
    // Sometimes, nested classes/objects appear inside the top-level scoped block of class/module ctor,
    // despite being a child of the class, but we want these to be a direct child of the class/module.
    val finder = scopeFinder
    obj match
      case ScopedObject.Top(s: Scoped) => finder.applyBlock(s.body)
      case ScopedObject.Top(b) => finder.applyBlock(b)
      case ScopedObject.Class(cls, _) =>
        finder.applyBlock(cls.preCtor)
        finder.applyBlock(cls.ctor)
      case ScopedObject.Companion(comp, cls) =>
        finder.applyBlock(comp.ctor)
      case ScopedObject.Func(fun, _) =>
        finder.applyBlock(fun.body)
      case ScopedObject.ScopedBlock(_, block) =>
        finder.applyBlock(block.body)
      case ScopedObject.ClassCtor(c) => ()
      case ScopedObject.Loop(_, b) => finder.applyBlock(b)
      case ScopedObject.ValDef(_) => ()
    val mtdObjs = obj match
      case ScopedObject.Class(cls, _) =>
        val k = if cls.k is syntax.Obj then MethodKind.ObjMethod else MethodKind.ClsMethod
        cls.methods.map(ScopedObject.Func(_, S(k)))
      case ScopedObject.Companion(comp, cls) => comp.methods.map(ScopedObject.Func(_, S(MethodKind.ModMethod)))
      case _ => Nil
    
    val isym = obj match
      case c: ScopedObject.Class => S(c.cls.isym)
      case c: ScopedObject.Companion => S(c.clsBody.isym)
      case _ => N
    val ownedClasses = isym.flatMap(ownersInv.get(_)) match
      case S(syms) => syms.map(d => classesMap.get(d)).collect:
        case S(c) => c
      case N => Nil
    val ownedClassObjs = ownedClasses.flatMap: c =>
      var objs: List[ScopedObject] = List.empty
      objs ::= ScopedObject.Class(c, c.k === syntax.Obj)
      c.ctorSym match
        case Some(value) => objs ::= ScopedObject.ClassCtor(c)
        case None => ()
      c.companion.map: comp =>
        objs ::= ScopedObject.Companion(comp, c)
      objs
    
    val children = (ownedClassObjs ::: mtdObjs ::: finder.objs).map(makeScopeTreeRec)
    val retNode = ScopeNode.ScopeNode(obj, N, children)
    obj.node = S(retNode)
    for c <- children do c.ancestor = S(retNode)
    retNode
