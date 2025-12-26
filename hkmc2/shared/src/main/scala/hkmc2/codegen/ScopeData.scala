package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.semantics.Elaborator.State

import hkmc2.syntax.Tree
import hkmc2.codegen.llir.FreshInt
import java.util.IdentityHashMap
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import hkmc2.ScopeData.ScopedInfo
import hkmc2.ScopeData.LifterMetadata

object ScopeData:
  opaque type ScopeUID = BigInt
  class FreshUID:
    private val underlying = FreshInt()
    def make: ScopeUID = underlying.make
  
  type ScopedInfo = DefinitionSymbol[?] | ScopeUID | Unit

  case class LifterMetadata(ignored: Set[ScopedInfo])
  
  // These cannot be hashed
  enum ScopedObject:
    case Top(b: Block) // b may be a scoped block, in which case, its variables represent the top-level variables.
    case Class(cls: ClsLikeDefn)
    case Companion(comp: ClsLikeBody, par: ClsLikeDefn)
    case Func(fun: FunDefn, isMethod: Bool)
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
    
  
  // A simple tree data structure representing the nesting relation of definitions and scopes.
  class NestedScopeTree(val root: ScopeNode):
    val nodesMap: Map[ScopedInfo, ScopeNode] = root.allChildNodes.map(n => n.obj.toInfo -> n).toMap
  
  case class ScopeNode(obj: ScopedObject, var parent: Opt[ScopeNode], children: List[ScopeNode])(using metadata: LifterMetadata):
    
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
    
    def isLifted: Bool = obj match
      case _: ScopedObject.ScopedBlock => false
      case ScopedObject.Func(_, true) => false
      case _ if metadata.ignored.contains(obj.toInfo) => false
      case _ => true

    // finds the first parent that is a lifted object, i.e. a non-ignored definition, or the top level
    lazy val firstLiftedParent: ScopedObject =
      if !isLifted then
        parent match
        case Some(value) => value.firstLiftedParent
        case None => obj // unreachable
      else obj
    
class ScopeData(b: Block)(using State, LifterMetadata):
  import ScopeData.*
  
  private val fresh = FreshUID()
  
  val scopeTree = NestedScopeTree(makeScopeTreeRec(ScopedObject.Top(b)))
  
  private val scopedMap: IdentityHashMap[Scoped, ScopeUID] = new IdentityHashMap
  for
    case ScopeNode(obj = ScopedObject.ScopedBlock(uid, blk)) <- scopeTree.root.allChildNodes
  do
    scopedMap.put(blk, uid)
  def getNode(x: ScopedInfo): ScopeNode = scopeTree.nodesMap(x)
  def getNode(defn: ClsLikeDefn): ScopeNode = getNode(defn.isym)
  def getNode(companion: ClsLikeBody): ScopeNode = getNode(companion.isym)
  def getNode(defn: FunDefn): ScopeNode = getNode(defn.dSym)
  def getNode(blk: Scoped): ScopeNode = getNode(scopedMap.get(blk))
  def getUID(blk: Scoped): ScopeUID = scopedMap.get(blk)
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
        finder.applyBlock(block)
    val mtdObjs = obj match
      case ScopedObject.Class(cls) => cls.methods.map(ScopedObject.Func(_, true))
      case ScopedObject.Companion(comp, par) => comp.methods.map(ScopedObject.Func(_, true))
      case _ => Nil
    val children = (mtdObjs ::: finder.objs).map(makeScopeTreeRec)
    val retNode = ScopeNode(obj, N, children)
    for c <- children do c.parent = S(retNode)
    retNode
