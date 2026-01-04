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
  class FreshUID:
    private val underlying = FreshInt()
    def make: ScopeUID = underlying.make
  
  type ScopedInfo = DefinitionSymbol[?] | ScopeUID | Unit

  // ScopeData requires the set of ignored scopes to compute certain things, but
  // the lifter requires the scope tree to generate the metadata. To solve this,
  // we generate the scope tree then populate the metadata later.
  case class IgnoredScopes(var ignored: Opt[Set[ScopedInfo]])
  
  // These cannot be hashed
  enum ScopedObject:
    case Top(b: Block) // b may be a scoped block, in which case, its variables represent the top-level variables.
    case Class(cls: ClsLikeDefn)
    case Companion(comp: ClsLikeBody, par: ClsLikeDefn)
    case Func(fun: FunDefn, isMethod: Bool)
    case Loop(body: Block)
    case ScopedBlock(uid: ScopeUID, block: Scoped)
    
    def toInfo: ScopedInfo = this match
      case Top(_) => ()
      case Class(cls) => cls.isym
      case Companion(comp, par) => comp.isym
      case Func(fun, _) => fun.dSym
      case ScopedBlock(uid, block) => uid
    
    // Locals defined by a scoped object.
    def definedLocals: Set[Local] = this match
      case Top(b) => b match
        case Scoped(syms, _) => syms.toSet
        case _ => Set.empty
      case Class(cls) =>
        // public fields are not included, as they are accessed using
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
      case Func(fun, _) => fun.params.flatMap: p =>
          p.params.map(_.sym)
        .toSet
      case ScopedBlock(_, block) => block.syms.toSet
    
  extension (traverser: BlockTraverser)
    def applyScopedObject(obj: ScopedObject) = 
      extension (s: Symbol) def traverse =
        traverser.applySymbol(s)
      obj match
      case ScopedObject.Top(b) => traverser.applyBlock(b)
      case ScopedObject.Class(ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
          privateFields, publicFields, preCtor, ctor, mod, bufferable))
      =>
        // do not traverse the companion
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
    
  // A simple tree data structure representing the nesting relation of definitions and scopes.
  class NestedScopeTree(val root: ScopeNode):
    val nodesMap: Map[ScopedInfo, ScopeNode] = root.allChildNodes.map(n => n.obj.toInfo -> n).toMap
  
  case class ScopeNode(obj: ScopedObject, var parent: Opt[ScopeNode], children: List[ScopeNode])(using ignoredScopes: IgnoredScopes):
    
    lazy val allParents: List[ScopedObject] = parent match
      case Some(value) => this.obj :: value.allParents
      case None => this.obj :: Nil
    
    // note: includes itself
    lazy val allChildNodes: List[ScopeNode] = this :: children.flatMap(_.allChildNodes)
    lazy val allChildren: List[ScopedObject] = allChildNodes.map(_.obj)
    
    // does not include variables introduced by itself
    lazy val existingVars: Set[Local] = parent match
      case Some(value) => value.existingVars ++ value.obj.definedLocals
      case None => Set.empty
    
    def isLifted: Bool =
      val ignored = ignoredScopes.ignored match
        case Some(value) => value
        case None => lastWords("isLifted accessed before the set of ignored scopes was set")
      
      parent.map(_.obj) match
      case Some(_: ScopedObject.Companion) => false // there is no need to lift objects nested inside a module
      case _ =>
        obj match
        case _: ScopedObject.ScopedBlock => false
        // case _: ScopedObject.Companion => false
        // case c: ScopedObject.Class if c.cls.companion.isDefined => false
        case ScopedObject.Func(isMethod = true) => false
        case _ if ignored.contains(obj.toInfo) => false
        case _ => true

    // finds the first parent that is a lifted object, i.e. a non-ignored definition, or the top level
    lazy val firstLiftedParent: ScopedObject =
      if !isLifted then
        parent match
        case Some(value) => value.firstLiftedParent
        case None => obj // unreachable
      else obj
    
class ScopeData(b: Block)(using State, IgnoredScopes):
  import ScopeData.*
  
  private val fresh = FreshUID()
  
  val scopeTree = NestedScopeTree(makeScopeTreeRec(ScopedObject.Top(b)))
  val root = scopeTree.root
  
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
  class ScopeFinder extends BlockTraverser:
    var objs: List[ScopedObject] = Nil
    override def applyBlock(b: Block): Unit = b match
      case s: Scoped =>
        objs ::= ScopedObject.ScopedBlock(fresh.make, s)
      case _ => super.applyBlock(b)
    override def applyFunDefn(fun: FunDefn): Unit =
      objs ::= ScopedObject.Func(fun, false)
    override def applyDefn(defn: Defn): Unit = defn match
      case f: FunDefn => applyFunDefn(f)
      case c: ClsLikeDefn =>
        objs ::= ScopedObject.Class(c)
        c.companion.map: comp =>
          objs ::= ScopedObject.Companion(comp, c)
        
      case _ => super.applyDefn(defn)
  
  
  def scopeFinder = new ScopeFinder()
  
  def makeScopeTreeRec(obj: ScopedObject): ScopeNode =
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
    val mtdObjs = obj match
      case ScopedObject.Class(cls) => cls.methods.map(ScopedObject.Func(_, true))
      case ScopedObject.Companion(comp, par) => comp.methods.map(ScopedObject.Func(_, true))
      case _ => Nil
    val children = (mtdObjs ::: finder.objs).map(makeScopeTreeRec)
    val retNode = ScopeNode(obj, N, children)
    for c <- children do c.parent = S(retNode)
    retNode
