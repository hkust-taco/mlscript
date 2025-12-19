package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.semantics.Elaborator.State

import hkmc2.syntax.Tree
import hkmc2.codegen.llir.FreshInt

class ScopeData(using State):
  
  opaque type UID = BigInt
  
  // These can be hashed. We use this to map these symbols to nodes in the tree
  enum ScopedInfo:
    case Top
    case ClassInfo(bSym: BlockMemberSymbol, clsSym: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol)
    case CompanionInfo(bSym: BlockMemberSymbol, clsSym: DefinitionSymbol[? <: ModuleOrObjectDef] & InnerSymbol)
    case FuncInfo(bSym: BlockMemberSymbol, dSym: TermSymbol)
    case ScopedBlockInfo(id: UID)
  
  // These cannot be hashed
  enum ScopedObject:
    case Top(b: Block)
    case Class(cls: ClsLikeDefn)
    case Companion(comp: ClsLikeBody, par: ClsLikeDefn)
    case Func(fun: FunDefn)
    case ScopedBlock(id: UID, block: Scoped)
    
    def toInfo: ScopedInfo = this match
      case Top(_) => ScopedInfo.Top
      case Class(cls) => ScopedInfo.ClassInfo(cls.sym, cls.isym)
      case Companion(comp, par) => ScopedInfo.CompanionInfo(par.sym, comp.isym)
      case Func(fun) => ScopedInfo.FuncInfo(fun.sym, fun.dSym)
      case ScopedBlock(id, block) => ScopedInfo.ScopedBlockInfo(id)
  
  // A simple tree data structure representing the nesting relation of definitions and scopes.
  class NestedScopeTree(val root: ScopeNode):
    val nodesMap = root.allChildNodes.map(x => x.obj.toInfo -> x).toMap
    def getNode(defn: ClsLikeDefn) = nodesMap.get(ScopedInfo.ClassInfo(defn.sym, defn.isym))
    def getNode(defn: FunDefn) = nodesMap.get(ScopedInfo.FuncInfo(defn.sym, defn.dSym))
    def getNode(scopeId: UID) = nodesMap.get(ScopedInfo.ScopedBlockInfo(scopeId))
  case class ScopeNode(obj: ScopedObject, var parent: Opt[ScopeNode], children: List[ScopeNode]):
    lazy val allParents: List[ScopedObject] = parent match
      case Some(value) => this.obj :: value.allParents
      case None => this.obj :: Nil
    // note: includes itself
    lazy val allChildNodes : List[ScopeNode] = this :: children.flatMap(_.allChildNodes)
    lazy val allChildren: List[ScopedObject] = allChildNodes.map(_.obj)
  
  private val fresh = FreshInt()
  
  private val scopedWithIdSym = TempSymbol(N, "scopedWithIdSym")

  // Used to associate IDs with scoped blocks.
  object ScopedWithId:
    def apply(id: UID, b: Scoped): Block = Begin(
      Assign(scopedWithIdSym, Value.Lit(Tree.IntLit(id)), End()),
      b)
    def unapply(b: Block): Opt[(UID, Scoped)] = b match
      case Begin(
        Assign(`scopedWithIdSym`, Value.Lit(Tree.IntLit(id)), End(_)),
        b: Scoped) => S((id, b))
      case _ => N
  
  // Add UIDs to scopes.
  object ScopeUidAdder extends BlockTransformer(SymbolSubst()):
    override def applyScopedBlock(b: Block): Block = b match
      case s: Scoped => ScopedWithId(fresh.make, s)
      case _ => super.applyBlock(b)
  
  def makeScopeTree(b: Block) =
    makeScopeTreeRec(ScopedObject.Top(ScopeUidAdder.applyBlock(b)))
  
  // From the input block or definition, traverses until a function, class or new scoped block is found and appends them.
  class ScopeFinder extends BlockTraverser:
    var objs: List[ScopedObject] = Nil
    override def applyBlock(b: Block): Unit = b match
      case ScopedWithId(id, b) =>
        objs ::= ScopedObject.ScopedBlock(id, b)
      case _ => super.applyBlock(b)
    override def applyFunDefn(fun: FunDefn): Unit =
      objs ::= ScopedObject.Func(fun)
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
      case ScopedObject.Top(b) => finder.applyBlock(b)
      case ScopedObject.Class(cls) =>
        cls.methods.map(f => finder.applyBlock(f.body))
      case ScopedObject.Companion(comp, par) =>
        comp.methods.map(f => finder.applyBlock(f.body))
      case ScopedObject.Func(fun) =>
        finder.applyBlock(fun.body)
      case ScopedObject.ScopedBlock(id, block) =>
        finder.applyBlock(block)
    val children = finder.objs.map(makeScopeTreeRec)
    val retNode = ScopeNode(obj, N, children)
    for c <- children do c.parent = S(retNode)
    retNode
