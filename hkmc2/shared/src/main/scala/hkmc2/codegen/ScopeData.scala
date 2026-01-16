package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.ScopeData.*
import hkmc2.semantics.Elaborator.State

import hkmc2.syntax.Tree
import hkmc2.codegen.llir.FreshInt
import java.util.IdentityHashMap
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet

object ScopeData:
  opaque type ScopeUID = BigInt
  val dummyUID: ScopeUID = 0
  class FreshUID:
    private val underlying = FreshInt()
    def make: ScopeUID = underlying.make
  
  type ScopedInfo = DefinitionSymbol[?] | LabelSymbol | ScopeUID | Unit

  // ScopeData requires the set of ignored scopes to compute certain things, but
  // the lifter requires the scope tree to generate the metadata. To solve this,
  // we generate the scope tree then populate the metadata later.
  case class IgnoredScopes(var ignored: Opt[Set[ScopedInfo]])
  
  type ScopedObject = ScopedObject.ScopedObject[?]
  type TScopedObject[T] = ScopedObject.ScopedObject[T]
  
  type LiftedSym = DefinitionSymbol[?]
  
  extension (d: DefinitionSymbol[?])
    def asBmsRef = Value.Ref(d.asBlkMember.get, S(d))
  
  // These cannot be hashed
  object ScopedObject:
    // T: The actual contents of the scoped object
    sealed abstract class ScopedObject[T]:
      var node: Opt[TScopeNode[T]] = N
      lazy val toInfo: ScopedInfo = this match
        case Top(_) => ()
        case Class(cls) => cls.isym
        case Companion(comp, par) => comp.isym
        case ClassCtor(cls) => cls.ctorSym.get
        case Func(fun, _) => fun.dSym
        case ScopedBlock(uid, block) => uid
        case Loop(sym, _) => sym
      
      // note: not unique
      lazy val nme = this match
        case Top(b) => "top"
        case Class(cls) => cls.isym.nme
        case Companion(comp, par) => comp.isym.nme + "_mod"
        case ClassCtor(cls) => cls.isym.nme // should be unused
        case Func(fun, isMethod) => fun.dSym.nme
        case Loop(sym, block) => "loop$" + sym.uid.toString()
        case ScopedBlock(uid, block) => "scope" + uid
      
      // Locals defined by a scoped object.
      lazy val definedLocals: Set[Local] = this match
        case Top(b) => b match
          case Scoped(syms, _) => syms.toSet
          case _ => Set.empty
        case Class(cls) =>
          // Public fields are not included, as they are accessed using
          // a field selection rather than directly using the BlockMemberSymbol.
          val paramsSet: Set[Local] = cls.paramsOpt match
            case Some(value) => value.params.map(_.sym).toSet
            case None => Set.empty
          val auxSet: Set[Local] = cls.auxParams.flatMap: p =>
              p.params.map(_.sym)
            .toSet
          paramsSet ++ auxSet ++ cls.privateFields + cls.isym
        case Companion(comp, par) =>
          comp.privateFields.toSet + comp.isym
        case _: ClassCtor => Set.empty
        case Func(fun, _) => fun.params.flatMap: p =>
            p.params.map(_.sym)
          .toSet
        case ScopedBlock(_, block) => block.syms.toSet
        case _: Loop => Set.empty
    
      def contents: T = this match
        case Top(b) => b
        case Class(cls) => cls
        case Companion(comp, par) => comp
        case ClassCtor(cls) => ()
        case Func(fun, _) => fun
        case ScopedBlock(_, block) => block
        case Loop(_, blk) => blk
    
    // Scoped nodes which may be referenced using a symbol.
    sealed abstract class Referencable[T] extends TScopedObject[T]:
      def sym: LiftedSym = this match
        case Class(cls) => cls.isym
        case Companion(comp, par) => comp.isym
        case Func(fun, isMethod) => fun.dSym
      def bsym: BlockMemberSymbol = this match
        case Class(cls) => cls.sym
        case Companion(comp, par) => par.sym
        case Func(fun, isMethod) => fun.sym
      
    
    // Scoped nodes which could possibly be lifted to the top level.
    sealed abstract class Liftable[T <: Defn] extends Referencable[T]:
      val defn: T
    
    // The top-level scope.
    case class Top(b: Block) extends ScopedObject[Block] // b may be a scoped block, in which case, its variables represent the top-level variables.
    case class Class(cls: ClsLikeDefn) extends Liftable[ClsLikeDefn]:
      val defn = cls
    case class Companion(comp: ClsLikeBody, par: ClsLikeDefn) extends Referencable[ClsLikeBody]
    // We model it like this: the ctor is just another function in the same scope as the class and initializes the corresponding class
    case class ClassCtor(cls: ClsLikeDefn) extends ScopedObject[Unit]
    case class Func(fun: FunDefn, isMethod: Bool) extends Liftable[FunDefn]:
      val defn = fun
    // The purpose of `Loop` is to enforce the rule that the control flow remains linear when we enter
    // a scoped block.
    case class Loop(sym: LabelSymbol, body: Block) extends ScopedObject[Block]
    case class ScopedBlock(uid: ScopeUID, block: Scoped) extends ScopedObject[Block]
  
  extension (traverser: BlockTraverser)
    def applyScopedObject(obj: ScopedObject) = 
      extension (s: Symbol) def traverse =
        traverser.applySymbol(s)
      obj match
      case ScopedObject.Top(b) => traverser.applyBlock(b)
      case ScopedObject.Class(ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
          privateFields, publicFields, preCtor, ctor, mod, bufferable))
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
      case ScopedObject.Companion(comp, par) => traverser.applyClsLikeBody(comp)
      case ScopedObject.Func(fun, isMethod) => traverser.applyFunDefn(fun)
      case ScopedObject.ScopedBlock(uid, block) => traverser.applyBlock(block)
      case ScopedObject.ClassCtor(c) => ()
      case ScopedObject.Loop(_, b) => traverser.applyBlock(b)
    
  // A simple tree data structure representing the nesting relation of definitions and scopes.
  class NestedScopeTree(val root: TScopeNode[Block]):
    val nodesMap: Map[ScopedInfo, ScopeNode] = root.allChildNodes.map(n => n.obj.toInfo -> n).toMap
  
  type ScopeNode = ScopeNode.ScopeNode[?]
  type TScopeNode[T] = ScopeNode.ScopeNode[T]
  object ScopeNode:
    case class ScopeNode[T](obj: TScopedObject[T], var parent: Opt[ScopeNode[?]], children: List[ScopeNode[?]])(using ignoredScopes: IgnoredScopes):
      
      lazy val allParents: List[ScopeNode[?]] = parent match
        case Some(value) => this :: value.allParents
        case None => this :: Nil
      
      lazy val parentsSet = allParents.map(_.obj.toInfo).toSet
      
      def inSubtree(root: ScopedInfo) = parentsSet.contains(root)
      
      // note: includes itself
      lazy val allChildNodes: List[ScopeNode[?]] = this :: children.flatMap(_.allChildNodes)
      lazy val allChildren: List[ScopedObject] = allChildNodes.map(_.obj)
      
      // does not include variables introduced by itself
      lazy val existingVars: Set[Local] = parent match
        case Some(value) => value.existingVars ++ value.obj.definedLocals
        case None => Set.empty
      
      // The following must not be called until ignoredScopes is populated with the relevant data.
      
      lazy val isLifted: Bool =
        val ignored = ignoredScopes.ignored match
          case Some(value) => value
          case None => lastWords("isLifted accessed before the set of ignored scopes was set")
        
        parent.map(_.obj) match
        case Some(_: ScopedObject.Companion) => false // there is no need to lift objects nested inside a module
        case _ =>
          obj match
          // case _: ScopedObject.Companion => false
          // case c: ScopedObject.Class if c.cls.companion.isDefined => false
          case _ if ignored.contains(obj.toInfo) => false
          case ScopedObject.Func(isMethod = true) => false
          case _: ScopedObject.Loop | _: ScopedObject.ClassCtor | _: ScopedObject.ScopedBlock | _: ScopedObject.Companion => false
          case _ => true
      
      lazy val isTopLevel: Bool = parent match
        case Some(ScopeNode(obj = _: ScopedObject.Top)) => true
        case _ => false
      
      lazy val liftedChildNodes: List[ScopeNode[?]] =
        if isLifted then this :: Nil
        else children.flatMap(_.liftedChildNodes)
      
      // Finds the first parent that is a lifted object, i.e. a non-ignored definition, or the top level
      lazy val firstLiftedParent: ScopedObject =
        if !isLifted then
          parent match
          case Some(value) => value.firstLiftedParent
          case None => obj // unreachable
        else obj
      
      // When a node is lifted, some neighbouring ignored definitions may become out of scope. This computes
      // the list of these definitions, and they could be passed to this node as a parameter once lifted.
      private lazy val reqCaptureObjsImpl: List[ScopedObject.Referencable[?]] = obj match
        case _: ScopedObject.Top => List.empty
        case _ =>
          // All unlifted neighbour nodes ::: parent's reqCaptureObjsImpl
          val initial = parent.get.allChildNodes.collect:
            case c @ ScopeNode(obj = t: ScopedObject.Referencable[?]) if !c.isLifted => t
          initial ::: parent.get.reqCaptureObjsImpl
      
      lazy val reqCaptureObjs: List[ScopedObject.Referencable[?]] = obj match
        case _: ScopedObject.Top => List.empty
        case _ =>
          if isLifted then reqCaptureObjsImpl
          else parent.get.reqCaptureObjsImpl
      
      // Scoped blocks include the BlockMemberSymbols of their nested definitions. This removes the ones
      // belonging to objects that are lifted.
      lazy val localsWithoutLifted: Set[Local] = obj match
        case s: ScopedObject.ScopedBlock =>
          val rmv = children.collect:
            case c @ ScopeNode(obj = s: ScopedObject.Liftable[?]) if c.isLifted => s.defn.sym
          obj.definedLocals -- rmv
        case _ => obj.definedLocals
    
  def dSymUnapply(data: ScopeData, v: DefinitionSymbol[?] | Option[DefinitionSymbol[?]]) = v match
    case Some(d) if data.contains(d) => S(d)
    case d: DefinitionSymbol[?] if data.contains(d) => S(d)
    case _ => None
    
class ScopeData(b: Block)(using State, IgnoredScopes):
  import ScopeData.*
  
  private val fresh = FreshUID()
  
  val scopeTree = NestedScopeTree(makeScopeTreeRec(ScopedObject.Top(b)))
  val root = scopeTree.root
  
  def contains(s: ScopedInfo) = scopeTree.nodesMap.contains(s)
    
  private val scopedMap: IdentityHashMap[Scoped, ScopeUID] = new IdentityHashMap
  for
    case ScopeNode(obj = ScopedObject.ScopedBlock(uid, blk)) <- scopeTree.root.allChildNodes
  do
    scopedMap.put(blk, uid)
  def getNode(x: ScopedInfo): ScopeNode = scopeTree.nodesMap(x)
  def getNode(defn: ClsLikeDefn): ScopeNode = getNode(defn.isym)
  def getNode(companion: ClsLikeBody): ScopeNode = getNode(companion.isym)
  def getNode(defn: FunDefn): ScopeNode = getNode(defn.dSym)
  def getUID(blk: Scoped): ScopeUID =
    if scopedMap.containsKey(blk) then scopedMap.get(blk)
    else lastWords("getUID: key not found")
  def getNode(blk: Scoped): ScopeNode = getNode(getUID(blk))
  // From the input block or definition, traverses until a function, class or new scoped block is found and appends them.
  class ScopeFinder extends BlockTraverserShallow:
    var objs: List[ScopedObject] = Nil
    override def applyBlock(b: Block): Unit = b match
      case s: Scoped =>
        val id = fresh.make
        objs ::= ScopedObject.ScopedBlock(id, s)
      case l: Label if l.loop =>
        objs ::= ScopedObject.Loop(l.label, l.body)
      case _ => super.applyBlock(b)
    override def applyFunDefn(fun: FunDefn): Unit =
      objs ::= ScopedObject.Func(fun, false)
    override def applyDefn(defn: Defn): Unit = defn match
      case f: FunDefn => applyFunDefn(f)
      case c: ClsLikeDefn =>
        objs ::= ScopedObject.Class(c)
        c.ctorSym match
          case Some(value) => objs ::= ScopedObject.ClassCtor(c)
          case None => ()
        c.companion.map: comp =>
          objs ::= ScopedObject.Companion(comp, c)
        
      case _ => super.applyDefn(defn)
  
  
  def scopeFinder = new ScopeFinder()
  
  def makeScopeTreeRec[T](obj: TScopedObject[T]): TScopeNode[T] =
    val finder = scopeFinder
    obj match
      case ScopedObject.Top(s: Scoped) => finder.applyBlock(s.body)
      case ScopedObject.Top(b) => finder.applyBlock(b)
      case ScopedObject.Class(cls) =>
        finder.applyBlock(cls.preCtor)
        finder.applyBlock(cls.ctor)
      case ScopedObject.Companion(comp, par) =>
        finder.applyBlock(comp.ctor)
      case ScopedObject.Func(fun, _) =>
        finder.applyBlock(fun.body)
      case ScopedObject.ScopedBlock(_, block) =>
        finder.applyBlock(block.body)
      case ScopedObject.ClassCtor(c) => ()
      case ScopedObject.Loop(_, b) => finder.applyBlock(b)
    val mtdObjs = obj match
      case ScopedObject.Class(cls) => cls.methods.map(ScopedObject.Func(_, true))
      case ScopedObject.Companion(comp, par) => comp.methods.map(ScopedObject.Func(_, true))
      case _ => Nil
    val children = (mtdObjs ::: finder.objs).map(makeScopeTreeRec)
    val retNode = ScopeNode.ScopeNode(obj, N, children)
    obj.node = S(retNode)
    for c <- children do c.parent = S(retNode)
    retNode
