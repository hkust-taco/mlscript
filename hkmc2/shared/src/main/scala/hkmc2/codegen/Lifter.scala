package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.ScopeData.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.Tree
import hkmc2.codegen.llir.FreshInt

import scala.collection.mutable.LinkedHashMap
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.ListBuffer

object Lifter:
  
  /**
    * Describes the free variables of a function that have been accessed by its nested definitions.
    * @param vars The free variables that are accessed by nested classes/functions.
    * @param reqCapture The free variables that must be captured using a heap-allocated object.
    */
  case class FreeVars(vars: Set[Local], reqCapture: Set[Local]):
    def ++(that: FreeVars) = FreeVars(vars ++ that.vars, reqCapture ++ that.reqCapture)
  object FreeVars:
    val empty = FreeVars(Set.empty, Set.empty)

  /**
    * Describes the free variables of functions that have been accessed by their nested definitions.
    * @param mp The map from functions' `BlockMemberSymbol`s to their accessed variables.
    */
  class UsedLocalsMap(val mp: Map[BlockMemberSymbol, FreeVars]):
    def apply(f: BlockMemberSymbol) = mp(f)
    private lazy val inverse = mp.flatMap:
      case fn -> vars => vars.vars.map(v => v -> fn)
    // gets the function to which a local belongs
    def lookup(l: Local) = inverse.get(l)
  
  /**
    * Describes previously defined locals and definitions which could possibly be accessed or mutated by particular definition.
    * Here, a "previously defined" local or definition means it is accessible to the particular definition (which we call `d`), 
    * but is not defined *by* `d`.
    *
    * @param accessed Previously defined locals which could possibly be accessed or mutated.
    * @param mutated Such locals which could also be mutated by this definition.
    * @param refdDefns Previously defined definitions which could possibly be used by this definition.
    */
  case class AccessInfo(
      accessed: Set[Local], 
      mutated: Set[Local], 
      refdDefns: Set[ScopedInfo]
    ):
    def ++(that: AccessInfo) = AccessInfo(
        accessed ++ that.accessed,
        mutated ++ that.mutated,
        refdDefns ++ that.refdDefns
      )
    def withoutLocals(locals: Set[Local]) = AccessInfo(
        accessed -- locals,
        mutated -- locals,
        refdDefns
      )
    def intersectLocals(locals: Set[Local]) = AccessInfo(
        accessed.intersect(locals),
        mutated.intersect(locals),
        refdDefns
      )
    def addAccess(l: Local) = copy(accessed = accessed + l)
    def addMutated(l: Local) = copy(accessed = accessed + l, mutated = mutated + l)
    def addRefdScopedObj(l: ScopedInfo) = copy(refdDefns = refdDefns + l)
    
  object AccessInfo:
    val empty = AccessInfo(Set.empty, Set.empty, Set.empty)

  type LocalVarSymbol = VarSymbol | TempSymbol
  
  def getVars(d: Defn): Set[Local] = d match
    case f: FunDefn =>
      (f.body.definedVars ++ f.params.flatMap(_.paramSyms)).collect:
        case s: LocalVarSymbol => s
    case c: ClsLikeDefn =>      
      val companionVars = c.companion.fold(Set.empty)(_.ctor.definedVars)
      (companionVars ++ c.preCtor.definedVars ++ c.ctor.definedVars).collect:
        case s: LocalVarSymbol => s
      
    case _ => Set.empty

  object RefOfBms:
    def unapply(p: Path): Opt[(BlockMemberSymbol, Opt[DefinitionSymbol[?]])] = p match
      case Value.Ref(l: BlockMemberSymbol, disamb) => S((l, disamb))
      case s @ Select(_, _) => s.symbol match
        case Some(value) => value.asBlkMember.map((_, S(value)))
        case _ => N
      case _ => N
  
  object InstSel:
    def unapply(p: Path) = p match
      case Value.Ref(l: BlockMemberSymbol, d) => S((l, d))
      case s @ Select(Value.Ref(l: BlockMemberSymbol, _), Tree.Ident("class")) => S((l, s.symbol))
      case _ => N
  
  def modOrObj(d: Defn) = d match
    case c: ClsLikeDefn => (c.companion.isDefined) || (c.k is syntax.Obj) // TODO: refine handling of companions
    case _ => false

/**
  * Lifts classes and functions to the top-level. Also automatically rewrites lambdas.
  * Assumes the input block does not have any `HandleBlock`s.
  */
class Lifter(topLevelBlk: Block)(using State, Raise):
  import Lifter.*

  /**
    * The context of the class lifter. One can create an empty context using `LifterCtx.empty`.
    * 
    * @param defns A map from all BlockMemberSymbols to their definitions.
    * @param defnsCur All definitions that are nested in the current top level definition.
    * @param nestedDefns Definitions which are nested in a given definition (shallow).
    * @param usedLocals Describes the locals belonging to each function that are accessed/mutated by nested definitions.
    * @param accessInfo Which previously defined variables/definitions could be accessed/modified by a particular definition, 
    * possibly through calls to other functions or by constructing a class.
    * @param ignoredDefns The definitions which must not be lifted.
    * @param inScopeDefns Definitions which are in scope to another definition (excluding itself and its nested definitions).
    * @param modObjLocals A map from the modules and objects to the local to which it is instantiated after lifting.
    * @param localCaptureSyms The symbols in a capture corresponding to a particular local. 
    * The `VarSymbol` is the parameter in the capture class.
    *   We used to also store along with it a `BlockMemberSymbol`, the field in the class, but it wasn't used.
    * @param prevFnLocals Locals belonging to function definitions that have already been traversed
    * @param prevClsDefns Class definitions that have already been traversed, excluding modules
    * @param inScopeISyms Inner symbols that are currently in scope (and therefore don't need to be rewritten).
    * @param curModules Modules that that we are currently nested in (cleared if we are lifted out)
    * @param capturePaths The path to access a particular function's capture in the local scope
    * @param bmsReqdInfo The (mutable) captures and (immutable) local variables each function requires
    * @param ignoredBmsPaths The path to access a particular BlockMemberSymbol (for definitions which could not be lifted)
    * @param localPaths The path to access a particular local (possibly belonging to a previous function) in the current scope
    * @param iSymPaths The path to access a particular `innerSymbol` (possibly belonging to a previous class) in the current scope
    * @param replacedDefns Ignored (unlifted) definitions that have been rewritten and need to be replaced at the definition site.
    * @param firstClsFns Nested functions which are used as first-class functions.
    * @param companionMap Map from companion object symbols to the corresponding regular class symbol.
    */
  case class LifterCtx private (
    val defns: Map[BlockMemberSymbol, Defn] = Map.empty,
    val defnsCur: Set[BlockMemberSymbol] = Set.empty,
    val nestedDefns: Map[BlockMemberSymbol, List[Defn]] = Map.empty,
    val usedLocals: UsedLocalsMap = UsedLocalsMap(Map.empty),
    val accessInfo: Map[BlockMemberSymbol, AccessInfo] = Map.empty,
    val ignoredDefns: Set[BlockMemberSymbol] = Set.empty,
    val inScopeDefns: Map[BlockMemberSymbol, Set[BlockMemberSymbol]] = Map.empty,
    val modObjLocals: Map[BlockMemberSymbol, Local] = Map.empty,
    val localCaptureSyms: Map[Local, VarSymbol] = Map.empty,
    val prevFnLocals: FreeVars = FreeVars.empty,
    val prevClsDefns: List[ClsLikeDefn] = Nil,
    val inScopeISyms: Set[InnerSymbol] = Set.empty,
    val curModules: List[ClsLikeDefn] = Nil,
    val capturePaths: Map[BlockMemberSymbol, LocalPath] = Map.empty,
    val bmsReqdInfo: Map[BlockMemberSymbol, LiftedInfo] = Map.empty, // required captures
    val ignoredBmsPaths: Map[BlockMemberSymbol, LocalPath] = Map.empty,
    val localPaths: Map[Local, LocalPath] = Map.empty,
    val isymPaths: Map[InnerSymbol, LocalPath] = Map.empty,
    val replacedDefns: Map[BlockMemberSymbol, Defn] = Map.empty,
    val firstClsFns: Set[BlockMemberSymbol] = Set.empty,
    val companionMap: Map[InnerSymbol, InnerSymbol] = Map.empty,
  ):
    // gets the function to which a local belongs
    def lookup(l: Local) = usedLocals.lookup(l)

    def getCapturePath(b: BlockMemberSymbol) = capturePaths.get(b)
    def getLocalClosPath(l: Local) = lookup(l).flatMap(capturePaths.get(_))
    def getLocalCaptureSym(l: Local) = localCaptureSyms.get(l)
    def getLocalPath(l: Local) = localPaths.get(l)
    def resolveIsymPath(l: InnerSymbol) = getIsymPath(companionMap.getOrElse(l, l))
    def getIsymPath(l: InnerSymbol) = isymPaths.get(l)
    def getIgnoredBmsPath(b: BlockMemberSymbol) = ignoredBmsPaths.get(b)
    def ignored(b: BlockMemberSymbol) = ignoredDefns.contains(b)
    def isModOrObj(b: BlockMemberSymbol) = modObjLocals.contains(b)
    def getAccesses(sym: BlockMemberSymbol) = accessInfo(sym)
    def isRelevant(sym: BlockMemberSymbol) = defnsCur.contains(sym)
    
    def addIgnored(defns: Set[BlockMemberSymbol]) = copy(ignoredDefns = ignoredDefns ++ defns)
    def withModObjLocals(mp: Map[BlockMemberSymbol, Local]) = copy(modObjLocals = modObjLocals ++ mp)
    def withDefns(mp: Map[BlockMemberSymbol, Defn]) = copy(defns = mp)
    def withDefnsCur(defns: Set[BlockMemberSymbol]) = copy(defnsCur = defns)
    def withNestedDefns(mp: Map[BlockMemberSymbol, List[Defn]]) = copy(nestedDefns = mp)
    def withAccesses(mp: Map[BlockMemberSymbol, AccessInfo]) = copy(accessInfo = mp)
    def withInScopes(mp: Map[BlockMemberSymbol, Set[BlockMemberSymbol]]) = copy(inScopeDefns = mp)
    def withFirstClsFns(fns: Set[BlockMemberSymbol]) = copy(firstClsFns = fns)
    def withCompanionMap(mp: Map[InnerSymbol, InnerSymbol]) = copy(companionMap = mp)
    def addFnLocals(f: FreeVars) = copy(prevFnLocals = prevFnLocals ++ f)
    def addClsDefn(c: ClsLikeDefn) = copy(prevClsDefns = c :: prevClsDefns)
    def addLocalCaptureSyms(m: Map[Local, VarSymbol]) = copy(localCaptureSyms = localCaptureSyms ++ m)
    def getBmsReqdInfo(sym: BlockMemberSymbol) = bmsReqdInfo.get(sym)
    def replCapturePaths(paths: Map[BlockMemberSymbol, LocalPath]) = copy(capturePaths = paths)
    def addCapturePath(src: BlockMemberSymbol, path: LocalPath) = copy(capturePaths = capturePaths + (src -> path))
    def addBmsReqdInfo(mp: Map[BlockMemberSymbol, LiftedInfo]) = copy(bmsReqdInfo = bmsReqdInfo ++ mp)
    def replLocalPaths(m: Map[Local, LocalPath]) = copy(localPaths = m)
    def replIgnoredBmsPaths(m: Map[BlockMemberSymbol, LocalPath]) = copy(ignoredBmsPaths = m)
    def replIsymPaths(m: Map[InnerSymbol, LocalPath]) = copy(isymPaths = m)
    def addLocalPaths(m: Map[Local, LocalPath]) = copy(localPaths = localPaths ++ m)
    def addLocalPath(target: Local, path: LocalPath) = copy(localPaths = localPaths + (target -> path))
    def addIgnoredBmsPaths(m: Map[BlockMemberSymbol, LocalPath]) = copy(ignoredBmsPaths = ignoredBmsPaths ++ m)
    def addIsymPath(isym: InnerSymbol, l: LocalPath) = copy(isymPaths = isymPaths + (isym -> l))
    def addIsymPaths(mp: Map[InnerSymbol, LocalPath]) = copy(isymPaths = isymPaths ++ mp)
    def addreplacedDefns(mp: Map[BlockMemberSymbol, Defn]) = copy(replacedDefns = replacedDefns ++ mp)
    def inModule(defn: ClsLikeDefn) = copy(curModules = defn :: curModules)
    def inISym(sym: InnerSymbol) = copy(inScopeISyms = inScopeISyms + sym)
    def resetScope = copy(inScopeISyms = Set.empty)
    def flushModules = 
      // called when we are lifted out while in some module, so we need to add the modules' isym paths
      copy(curModules = Nil).addIsymPaths(curModules.map(d => d.isym -> LocalPath.Sym(d.sym)).toMap)
  
  object LifterCtx:
    def empty = LifterCtx()
    def withLocals(u: UsedLocalsMap) = empty.copy(usedLocals = u)
  
  extension (l: Local)
    def asLocalPath: LocalPath = LocalPath.Sym(l)
  
  enum LocalPath:
    case Sym(l: Local)
    case BmsRef(l: BlockMemberSymbol, d: DefinitionSymbol[?])
    case InCapture(capturePath: Path, field: TermSymbol)
    case PubField(isym: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol, sym: BlockMemberSymbol)
    
    def read = this match
      case Sym(l) => l.asPath
      case BmsRef(l, d) => Value.Ref(l, S(d))
      case InCapture(path, field) => Select(path, field.id)(S(field))
      case PubField(isym, sym) => Select(isym.asPath, Tree.Ident(sym.nme))(N)
      
    def asArg = read.asArg
    
    def assign(value: Result, rest: Block) = this match
      case Sym(l) => Assign(l, value, rest)
      case BmsRef(l, d) => lastWords("Tried to assign to a BlockMemberSymbol")
      case InCapture(path, field) => AssignField(path, field.id, value, rest)(S(field))
      case PubField(isym, sym) => AssignField(isym.asPath, Tree.Ident(sym.nme), value, rest)(S(sym))
  
  case class FunSyms[T <: DefinitionSymbol[?]](b: BlockMemberSymbol, d: T):
    def asPath = Value.Ref(b, S(d))
  object FunSyms:
    def fromFun(b: BlockMemberSymbol, owner: Opt[InnerSymbol] = N) =
      FunSyms(b, TermSymbol.fromFunBms(b, owner))
  
  // Info required for lifting a definition.
  case class LiftedInfo(
    val reqdCaptures: List[BlockMemberSymbol], // The mutable captures a lifted definition must take.
    val reqdVars: List[Local], // The (passed by value) variables a lifted definition must take.
    val reqdInnerSyms: List[InnerSymbol], // The inner symbols a lifted definition must take.
    val reqdBms: List[BlockMemberSymbol], // BMS's belonging to unlifted definitions that this definition references.
    val fakeCtorBms: Option[FunSyms[TermSymbol]], // only for classes
    val singleCallBms: FunSyms[TermSymbol], // optimization
  )

  case class Lifted[+T <: Defn](
    val liftedDefn: T,
    val extraDefns: List[Defn],
  )
  
  type ClsLikeSym = DefinitionSymbol[? <: ClassDef | ModuleOrObjectDef]
  type ClsSym = DefinitionSymbol[? <: ClassLikeDef]
  type ModuleOrObjSym = DefinitionSymbol[? <: ModuleOrObjectDef]
  
  case class LifterMetadata(
    unliftable: Set[ClsSym | ModuleOrObjSym],
    modules: Set[ModuleOrObjSym],
    firstClsFns: Set[TermSymbol]
  ):
    def ++(that: LifterMetadata) =
      LifterMetadata(unliftable ++ that.unliftable, modules ++ that.modules, firstClsFns ++ that.firstClsFns)
  object LifterMetadata:
    def empty = LifterMetadata(Set.empty, Set.empty, Set.empty)
  
  // d is a top-level definition
  // returns (ignored classes, modules, objects)
  private def createMetadata(s: ScopeNode): LifterMetadata =
    var ignored: Set[ClsSym | ModuleOrObjSym] = Set.empty
    var firstClsFns: Set[TermSymbol] = Set.empty
    val nestedScopeNodes: List[ScopeNode] = s.allChildNodes
    val nestedScopes: Set[ScopedInfo] = nestedScopeNodes.map(_.obj.toInfo).toSet - s.obj.toInfo
    
    // hack: ClassLikeSymbol does not extend DefinitionSymbol directly, so we must
    // use a map to convert 
    
    val moduleObjs = nestedScopeNodes.collect:
      case ScopeNode(obj = o: ScopedObject.Companion) => o
    
    // TODO: refine handling of companions
    for m <- moduleObjs do
      ignored += m.par.isym
      ignored += m.comp.isym
      raise(WarningReport(
        msg"Modules are not yet lifted." -> m.comp.isym.toLoc :: Nil,
        N, Diagnostic.Source.Compilation
      ))
    
    val modules: Set[ModuleOrObjSym] = moduleObjs.map(_.comp.isym).toSet
    var extendsGraph: Set[(ClsSym, ClsSym)] = Set.empty
    
    // search for unliftable classes and build the extends graph
    new BlockTraverser:
      this.applyScopedObject(s.obj)
      override def applyCase(cse: Case): Unit =
        cse match
          case Case.Cls(cls: (ClassSymbol | ModuleOrObjectSymbol), _) =>
            if nestedScopes.contains(cls) && !ignored.contains(cls) then // don't generate a warning if it's already ignored
              raise(WarningReport(
                msg"Cannot yet lift class/module `${cls.nme}` as it is used in an instance check." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
              ignored += cls
          case _ => ()
      
      override def applyResult(r: Result): Unit = r match
        case Call(Value.Ref(_: BlockMemberSymbol, _), args) =>
          args.foreach(applyArg)
        case Instantiate(mut, InstSel(_), args) =>
          args.foreach(applyArg)
        case _ => super.applyResult(r)
      
      override def applyDefn(defn: Defn): Unit = defn match
        case defn: FunDefn => applyFunDefn(defn)
        case ValDefn(tsym, sym, rhs) =>
          tsym.owner.foreach(_.traverse)
          sym.traverse
          applyPath(rhs)
        case ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentPath, methods,
            privateFields, publicFields, preCtor, ctor, mod, bufferable)
        =>
          own.foreach(_.traverse)
          isym.traverse
          sym.traverse
          // Check if `extends` is a complex expression, i.e. not just extending a class.
          // If it's just a class, add it to an graph where edges are class extensions.
          // If B extends A, then A -> B is an edge
          parentPath match
            case None => ()
            case Some(RefOfBms(_, S(s: ClassSymbol))) =>
              if nestedScopes.contains(s) then extendsGraph += (s -> isym)
            case _ if !ignored.contains(isym) =>
              raise(WarningReport(
                msg"Cannot yet lift definition `${sym.nme}` as it extends an expression." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
              ignored += isym
            case _ => ()
          paramsOpt.foreach(applyParamList)
          auxParams.foreach(applyParamList)
          methods.foreach(applyFunDefn)
          privateFields.foreach(_.traverse)
          publicFields.foreach: f =>
            f._1.traverse; f._2.traverse
          applyBlock(preCtor)
          applyBlock(ctor)
          mod.foreach(applyClsLikeBody)
      
      def isFun(d: Defn) = d match
        case _: FunDefn => true
        case _ => false
      
      override def applyValue(v: Value): Unit = v match
        case RefOfBms(_, S(l: ClassSymbol)) if nestedScopes.contains(l) =>
          raise(WarningReport(
            msg"Cannot yet lift class `${l.nme}` as it is used as a first-class class." -> N :: Nil,
            N, Diagnostic.Source.Compilation
          ))
          ignored += l
        case RefOfBms(_, S(t: TermSymbol)) =>
          // naked reference to a function definition
          firstClsFns += t
        case _ => super.applyValue(v)
    
    // analyze the extends graph
    val extendsEdges = extendsGraph.groupBy(_._1).map:
        case (a, bs) => a -> bs.map(_._2)
      .toMap
    var newUnliftable: Set[ClsSym] = Set.empty
    // dfs starting from unliftable classes
    def dfs(s: ClsSym): Unit =
      for 
        edges <- extendsEdges.get(s)
        b <- edges if !newUnliftable.contains(b) && !ignored.contains(b) 
      do 
        raise(WarningReport(
          msg"Cannot yet lift definition `${b.nme}` as it extends an unliftable class." -> N :: Nil,
          N, Diagnostic.Source.Compilation
        ))
        newUnliftable += b
        dfs(b)
    for case s: ClsLikeSym <- ignored do
      dfs(s)
    
    LifterMetadata(ignored ++ newUnliftable, modules, firstClsFns)
  
  extension (b: Block)
    private def floatOut(ctx: LifterCtx) =
      b.extractDefns(preserve = defn => ctx.isModOrObj(defn.sym) || ctx.ignored(defn.sym))
    private def gather(ctx: LifterCtx) =
      b.gatherDefns(preserve = defn => ctx.isModOrObj(defn.sym) || ctx.ignored(defn.sym))
  
  
  def createLiftInfoCont(d: Defn, parentCls: Opt[ClsLikeDefn], ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    ???
    /*
    val AccessInfo(accessed, _, refdDefns) = ctx.getAccesses(d.sym)
    
    val inScopeRefs = refdDefns.intersect(ctx.inScopeDefns(d.sym))
    
    val includedCaptures = ctx.prevFnLocals.reqCapture
      .intersect(accessed)
      .map(sym => ctx.lookup(sym).get)
      .toList.sortBy(_.uid)
    
    val refMod = inScopeRefs.intersect(ctx.modObjLocals.keySet)
    val includedLocals = ((accessed -- ctx.prevFnLocals.reqCapture) ++ refMod).toList.sortBy(_.uid)
    val clsCaptures: List[InnerSymbol] = ctx.prevClsDefns.map(_.isym)
    val refBms = inScopeRefs.intersect(ctx.ignoredDefns).toList.sortBy(_.uid)
    
    val isModLocal = d match
      case c: ClsLikeDefn if modOrObj(c) && !ctx.ignored(c.sym) => true
      case _ => false
    
    if ctx.ignored(d.sym) ||
      (includedCaptures.isEmpty && includedLocals.isEmpty && clsCaptures.isEmpty && refBms.isEmpty) then
      d match
        case f: FunDefn =>
          createLiftInfoFn(f, ctx)
        case c: ClsLikeDefn =>
          createLiftInfoCls(c, ctx)
        case _ => Map.empty
    else
      val fakeCtorBms = d match
        case c: ClsLikeDefn if !isModLocal => S(BlockMemberSymbol(d.sym.nme + "$ctor", Nil))
        case _ => N
      
      val singleCallBms = BlockMemberSymbol(d.sym.nme + "$", Nil)
      
      val info = LiftedInfo(
        includedCaptures, includedLocals, clsCaptures,
        refBms, fakeCtorBms.map(FunSyms.fromFun(_)), FunSyms.fromFun(singleCallBms)
      )
      
      d match
        case f: FunDefn =>
          createLiftInfoFn(f, ctx) + (d.sym -> info)
        case c: ClsLikeDefn =>
          createLiftInfoCls(c, ctx) + (d.sym -> info)
        case _ => Map.empty
    */
  
  def createLiftInfoFn(f: FunDefn, ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val defns = ctx.nestedDefns(f.sym)
    defns.flatMap(createLiftInfoCont(_, N, ctx.addFnLocals(ctx.usedLocals(f.sym)))).toMap

  def createLiftInfoCls(c: ClsLikeDefn, ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val defns = c.preCtor.gather(ctx) ++ c.ctor.gather(ctx) ++ c.companion.fold(Nil)(_.ctor.gather(ctx))
    val newCtx = if (c.companion.isDefined) && !ctx.ignored(c.sym) then ctx else ctx.addClsDefn(c)
    val staticMtdInfo = c.companion.fold(Map.empty):
      case value => value.methods.flatMap(f => createLiftInfoFn(f, newCtx))
    
    defns.flatMap(f => createLiftInfoCont(f, S(c), newCtx)).toMap
      ++ c.methods.flatMap(f => createLiftInfoFn(f, newCtx))
      ++ staticMtdInfo
  
  // This rewrites code so that it's valid when lifted to the top level.
  // This way, no piece of code must be traversed by a BlockRewriter more than once.
  // Remark: This is why so much prior analysis is needed and is the main source of complexity in the lifter.
  class BlockRewriter(using ctx: LifterCtxNew) extends ScopeRewriter:
    // Closure symbols that point to an initialized closure in this scope
    var activeClosures: Set[Local] = Set.empty
    // Map from block member symbols to initialized closures
    val closureMap: MutMap[BlockMemberSymbol, Local] = MutMap.empty
    val extraLocals: MutSet[Local] = MutSet.empty
    
    def rewrite(b: Block) =
      val ret = applyBlock(b)
      Scoped(extraLocals, ret)
    
    // Replaces references to BlockMemberSymbols as needed with fresh variables, and
    // returns the mapping from the symbol to the required variable. When possible,
    // it also directly rewrites Results (Calls and Instantiates).
    // Since first-class classes can't be lifted, this is where class
    // instantiations are rewritten.
    //
    // Does *not* rewrite references to non-lifted BMS symbols.
    def rewriteBms(b: Block) =
      // BMS's that need to be created
      val syms: LinkedHashMap[FunSyms[?], Local] = LinkedHashMap.empty
      val extraLocals: MutSet[Local] = MutSet.empty

      val walker = new BlockDataTransformer(SymbolSubst()):
        // only scan within the block. don't traverse
        
        override def applyResult(r: Result)(k: Result => Block): Block = r match
          // if possible, directly rewrite the call using the efficient version
          case c @ Call(RefOfBms(l, S(d)), args) => ctx.liftedScopes.get(d) match
            case None => super.applyResult(r)(k)
            case Some(value) => value match
              case f: LiftedFunc => k(f.rewriteCall(c, ctx.capturesMap, ctx.symbolsMap))
          case c @ Instantiate(mut, InstSel(l, S(d)), args) => ???
          // LEGACY CODE: We previously directly created the closure and assigned it to the
          // variable here. But, since this closure may be re-used later, this doesn't work
          // in general, so we will always create a TempSymbol for it.
          // case RefOfBms(l) if ctx.bmsReqdInfo.contains(l) && !ctx.isModOrObj(l) =>
          //   createCall(l, ctx)
          case _ => super.applyResult(r)(k)
        
        // extract the call
        override def applyPath(p: Path)(k: Path => Block): Block = p match
          case r @ RefOfBms(l, S(d)) => ctx.liftedScopes.get(d) match
            case S(f: LiftedFunc) =>
              if f.isTrivial then k(r)
              else
                val newSym = closureMap.get(l) match
                  case None =>
                    val newSym = TempSymbol(N, l.nme + "$here")
                    extraLocals.add(newSym)
                    syms.addOne(FunSyms(l, d) -> newSym) // add to `syms`: this closure will be initialized in `applyBlock`
                    closureMap.addOne(l -> newSym) // add to `closureMap`: `newSym` refers to the closure and can be used later
                    newSym

                  // symbol exists, and is initialized
                  case Some(value) if activeClosures.contains(value) => value
                  // symbol exists, needs initialization
                  case Some(value) =>
                    syms.addOne(FunSyms(l, d) -> value)
                    value
                k(Value.Ref(newSym, N))
            
            // Other naked references to BlockMemberSymbols.
            case N => ctx.symbolsMap.get(d) match
              case Some(value) => k(value.read)
              case None => super.applyPath(p)(k)
          
          case _ => super.applyPath(p)(k)
      (walker.applyBlock(b), syms.toList, extraLocals)
    end rewriteBms
    
    def applySubBlockAndReset(b: Block): Block =
      val curActive = activeClosures
      val ret = applySubBlock(b)
      activeClosures = curActive
      ret
    
    override def applyBlock(b: Block): Block =
      // extract references to BlockMemberSymbols in the block which now may
      // need to be enriched with aux parameters
      val (rewritten, syms, extras) = rewriteBms(b)
      extraLocals.addAll(extras)
      val pre = syms.foldLeft(blockBuilder):
        case (blk, (funSym, local)) =>
          ctx.liftedScopes(funSym.d) match
            case l: LiftedFunc => blk.assign(local, l.rewriteRef(ctx.capturesMap, ctx.symbolsMap))
      
      // Rewrite the rest
      val remaining = rewritten match
        
        // We create closures once the first time we see them, then re-use them later.
        // We store already-created closures in a set in the BlockRewriter class.
        // This set needs to be reset after processing an if-else branch or while loop,
        // since closures nested inside each branch may not be re-used elsewhere.
        case Match(scrut, arms, dflt, rst) =>
          applyPath(scrut): scrut2 =>
            applyListOf(
              arms,
              (tup, k) =>
                val (cse, blk) = tup
                val blk2 = applySubBlockAndReset(blk)
                applyCase(cse): cse2 =>
                  if (cse2 is cse) && (blk is blk2) then k(tup) else k(cse2 -> blk2)
            ): arms2 =>
                val dflt2 = dflt.mapConserve(applySubBlockAndReset)
                val rst2 = applySubBlock(rst)
                if (scrut2 is scrut) &&
                    (arms2 is arms) &&
                    (dflt2 is dflt) && (rst2 is rst)
                  then rewritten else Match(scrut2, arms2, dflt2, rst2)
            
        case Label(lbl, false, bod, rst) =>
          val lbl2 = lbl.subst
          val bod2 = applySubBlockAndReset(bod)
          val rst2 = applySubBlock(rst)
          if (lbl2 is lbl) && (bod2 is bod) && (rst2 is rst) then rewritten else Label(lbl2, false, bod2, rst2)
        case TryBlock(sub, fin, rst) =>
          val sub2 = applySubBlockAndReset(sub)
          val fin2 = applySubBlockAndReset(fin)
          val rst2 = applySubBlock(rst)
          if (sub2 is sub) && (fin2 is fin) && (rst2 is rst) then rewritten else TryBlock(sub2, fin2, rst2)
        
        // Assignment to variables
        case Assign(lhs, rhs, rest) => ctx.symbolsMap.get(lhs) match
          case Some(path) => applyResult(rhs): rhs2 =>
            path.assign(rhs2, applySubBlock(rest))
          case _ => super.applyBlock(rewritten)
        
        // rewrite ValDefns (in ctors)
        case define @ Define(d: ValDefn, rest: Block) if d.owner.isDefined => super.applyBlock(rewritten) // TODO
          /*
          ctx.getIsymPath(d.owner.get) match
            case Some(value) if !iSymInScope(d.owner.get) =>
              applyResult(d.rhs): newRhs =>
                AssignField(value.read, Tree.Ident(d.sym.nme), newRhs, applyBlock(rest))(S(d.sym))
            case _ => super.applyBlock(rewritten)
          */
        // rewrite object definitions, assigning to the given symbol in modObjLocals
        case Define(d: ClsLikeDefn, rest: Block) => super.applyBlock(rewritten) // TODO
          /*
          ctx.modObjLocals.get(d.sym) match
          case Some(sym) if !ctx.ignored(d.sym) => ctx.getBmsReqdInfo(d.sym) match
            case Some(_) => // has args
              extraLocals.add(sym)
              blockBuilder
                .assign(sym, Instantiate(mut = false, d.sym.asPath, getCallArgs(FunSyms(d.sym, d.isym), ctx)))
                .rest(applyBlock(rest))
            case None => // has no args
              // Objects with no parameters are instantiated statically
              blockBuilder
                .assign(sym, d.sym.asPath)
                .rest(applyBlock(rest))
          case _ => ctx.replacedDefns.get(d.sym) match
            case Some(value) => Define(value, applyBlock(rest))
            case None => super.applyBlock(rewritten)
          */
        case _ => super.applyBlock(rewritten)
      
      pre.rest(remaining)
    
    override def applyPath(p: Path)(k: Path => Block): Block = 
      p match
      // For objects inside classes: When an object is nested inside a class, its defn will be
      // replaced by a symbol, to which the object instance is assigned. This rewrites references
      // from the objects BlockMemberSymbol to that new symbol.
      // case s @ Select(qual, ident) => ??? 
        /*
        s.symbol.flatMap(ctx.getLocalPath) match
        case Some(LocalPath.Sym(value: DefinitionSymbol[?])) =>
          k(Select(qual, Tree.Ident(value.nme))(S(value)))
        case _ => super.applyPath(p)(k)
        */
      
      // This rewrites naked references to locals,
      case Value.Ref(l, _) => ctx.symbolsMap.get(l) match
        case Some(value) => k(value.read)
        case _ => super.applyPath(p)(k)
      
      case _ => super.applyPath(p)(k)
  
  /* 
   * Explanation of liftOutDefnCont, liftDefnsInCls, liftDefnsInFn:
   * 
   * The initial call is to liftDefnsInFn or liftDefnsInCls:
   * - liftDefnsInFn rewrites a function's body so that it references variables correctly, and calls liftOutDefnCont
   *   on its nested definitions and lifts them (if they're not ignored).
   * - liftDefnsInCls does the same but for classes by rewriting their constructors and methods. Notably, it directly
   *   calls liftDefnsInFn on its member functions.
   * 
   * liftOutDefnCont's purpose is to rewrite definitions' signatures so that they make sense after being lifted. This 
   * includes adding the parameter lists which take in variables, captures, references to inner symbols etc. If a
   * definition has been marked as "ignored" (not lifted), or if the definition is so simple that it doesn't need,
   * extra parameter lists, it will directly call liftDefnsInFn or liftDefnsInCls on that definition.
   */
  def liftOutDefnCont(base: Defn, d: Defn, ctx: LifterCtx): Lifted[Defn] = ctx.getBmsReqdInfo(d.sym) match
    case N => d match
      case f: FunDefn => ???
      case c: ClsLikeDefn => ???
      case _ => Lifted(d, Nil)
    case S(LiftedInfo(includedCaptures, includedLocals, clsCaptures, reqdBms, fakeCtorBms, singleCallBms)) =>
      
      def createSymbolsUpdateCtx[T <: LocalPath](createSym: String => (VarSymbol, T))
      : (List[Param], LifterCtx, List[(Local, (VarSymbol, T))])
      =
        ???

      d match
        case f: FunDefn =>
          ???
        case c: ClsLikeDefn =>
          val fresh = FreshInt()
          def createSym(nme: String): (VarSymbol, LocalPath.PubField) = 
            (
              VarSymbol(Tree.Ident(nme)),
              LocalPath.PubField(c.isym, BlockMemberSymbol(nme, Nil, true))
            )
          val (extraParams, newCtx, flds) = createSymbolsUpdateCtx(createSym)
          
          // add aux params, private fields, update preCtor
          val newAuxParams = c.auxParams.appended(PlainParamList(extraParams))
          
          val pubFieldsPairs = flds.map:
            case (_, (vs, LocalPath.PubField(isym, sym))) => vs -> sym
          
          val newPubFields = c.publicFields ::: pubFieldsPairs.map(_._2).map(bsym => bsym ->
            TermSymbol(syntax.MutVal, S(c.isym), Tree.Ident(bsym.nme)))
          
          val newCtor = pubFieldsPairs.foldRight(c.ctor):
            case ((sym, bms), blk) => Define(ValDefn.mk(S(c.isym), syntax.MutVal, bms, sym.asPath), blk)
          
          if modOrObj(c) then // module or object
            // force it to be a class
            val newK = c.k match
              case syntax.Obj => syntax.Cls
              case _ => wat("unreachable", c.k)
            
            val newDef = c.copy(
              k = newK, paramsOpt = N,
              owner = N, auxParams = PlainParamList(extraParams) :: Nil,
              publicFields = newPubFields,
              ctor = newCtor
            )
            ???
          else // normal class
            
            val newDef = c.copy(
              owner = N, 
              auxParams = newAuxParams,
              publicFields = newPubFields,
              ctor = newCtor
            )
            
            val Lifted(lifted, extras) = ???
            
            val bms = fakeCtorBms.get
            
            // create the fake ctor here
            inline def mapParams(ps: ParamList) = ps.params.map(p => VarSymbol(p.sym.id))
            
            val paramSyms = c.paramsOpt.map(mapParams) // what is defined in paramsOpt
            val auxSyms = c.auxParams.map(mapParams) // the original class's aux params
            val extraSyms = extraParams.map(p => VarSymbol(p.sym.id)) // these will be added to the aux params
            
            // pop one list fromm auxSyms if paramsOpt is empty
            // these are for creating the body only
            val (newParamSyms, newAuxSyms) = paramSyms match
              case None => auxSyms match
                case head :: next => (S(head), next.appended(extraSyms))
                case Nil => (S(extraSyms), Nil)
              case Some(value) => (paramSyms, auxSyms.appended(extraSyms))
            
            val paramArgs = newParamSyms.getOrElse(Nil).map(_.asPath.asArg)
            
            inline def toPaths(l: List[Local]) = l.map(_.asPath)
            
            val isMutSym = VarSymbol(Tree.Ident("isMut"))
            
            val curSyms: MutSet[Local] = MutSet.empty
            var curSym = TempSymbol(None, "tmp")
            curSyms.add(curSym)
            def instInner(isMut: Bool) =
              Instantiate(mut = isMut, Value.Ref(c.sym, S(c.isym)), paramArgs)
            
            val initSym = curSym
            
            var acc: Block => Block = blk => Match(
              isMutSym.asPath,
              Case.Lit(Tree.BoolLit(true)) -> Assign(initSym, instInner(true), End()) :: Nil,
              S(Assign(initSym, instInner(false), End())),
              blk
            )
            
            for ps <- newAuxSyms do
              val call = Call(curSym.asPath, ps.map(_.asPath.asArg))(true, false, false)
              curSym = TempSymbol(None, "tmp")
              curSyms.add(curSym)
              val thisSym = curSym
              acc = acc.assign(thisSym, call)
              // acc = blk => acc(Assign(curSym, call, blk))
            val bod = Scoped(curSyms, acc.ret(curSym.asPath))
            
            inline def toPlist(ls: List[VarSymbol]) =
              PlainParamList(ls.map(s => Param(FldFlags.empty, s, N, Modulefulness.none)))
            
            val paramPlist = paramSyms.map(toPlist)
            val auxPlist = auxSyms.map(toPlist)
            // isMut determines whether the instantiation is `new` or `new mut`
            val extraPlist = toPlist(isMutSym :: extraSyms)
            
            // NOTE: The fake ctor was to support first-class classes.
            // These are currently unused.
            
            /*
            val plist = paramPlist match
              case None => extraPlist :: PlainParamList(Nil) :: auxPlist
              case Some(value) => extraPlist :: value :: auxPlist
            
            val fakeCtorDefn = FunDefn(
              None, bms, plist, bod
            )
            */
            
            val paramSym2 = paramSyms.getOrElse(Nil)
            val auxSym2 = auxSyms.flatMap(l => l)
            val allSymsMp = (paramSym2 ++ auxSym2 ++ extraSyms).map(s => s -> VarSymbol(s.id)).toMap
            val subst = new SymbolSubst():
              override def mapVarSym(s: VarSymbol): VarSymbol = allSymsMp.get(s) match
                case None => s
                case Some(value) => value
            
            val (headParams, newAuxPlist) = paramPlist match
              case None => auxPlist match
                case head :: next => (ParamList(head.flags, extraPlist.params ++ head.params, head.restParam), next)
                case Nil => (extraPlist, auxPlist)
              
              case Some(value) => (ParamList(value.flags, extraPlist.params ++ value.params, value.restParam), auxPlist)
            
            val auxCtorDefn_ = FunDefn(None, singleCallBms.b, singleCallBms.d, headParams :: newAuxPlist, bod)(false)
            val auxCtorDefn = BlockTransformer(subst).applyFunDefn(auxCtorDefn_)
            
            // Lifted(lifted, extras ::: (fakeCtorDefn :: auxCtorDefn :: Nil))
            Lifted(lifted, extras ::: (auxCtorDefn :: Nil))
        case _ => Lifted(d, Nil)
  
  end liftOutDefnCont
  
  given ignoredScopes: IgnoredScopes = IgnoredScopes(N)
  val data = ScopeData(topLevelBlk)
  val metadata = data.root.children.foldLeft(LifterMetadata.empty)(_ ++ createMetadata(_))
  
  def asDSym(s: ClsSym | ModuleOrObjSym): DefinitionSymbol[?] = s
  val ignored: Set[ScopedInfo] = metadata.unliftable.map(asDSym)
  ignoredScopes.ignored = S(ignored)
    
  val usedVars = UsedVarAnalyzer(topLevelBlk, data)
  
  // for debugging
  def printMap[T, V](m: Map[T, V]) =
    println("Map(")
    for case (k, v) <- m do
      print("  ")
      print(k)
      print(" -> ")
      println(v)
    println(")")
  
  /*
  
  println("accessesShallow")
  printMap(usedVars.shallowAccesses)
  println("accesses")
  printMap(usedVars.accessMap)
  printMap(usedVars.accessMapWithIgnored)
  println("usedVars")
  printMap(usedVars.reqdCaptures)
  
  */
  
  def isIgnored(d: Defn) = d match
    case f: FunDefn => ignored.contains(f.dSym)
    case v: ValDefn => true
    case c: ClsLikeDefn => ignored.contains(c.isym)
  
  case class LifterResult[+T](liftedDefn: T, extraDefns: List[Defn])
  case class LifterCtxNew(
    liftedScopes: MutMap[LiftedSym, LiftedScope[?]] = MutMap.empty,
    rewrittenScopes: MutMap[ScopedInfo, RewrittenScope[?]] = MutMap.empty,
    var symbolsMap: Map[Local, LocalPath] = Map.empty,
    var capturesMap: Map[ScopedInfo, Path] = Map.empty
  )
  
  /**
    * Creates a capture class for a function consisting of its mutable (and possibly immutable) local variables.
    * @param f The function to create the capture class for.
    * @param ctx The lifter context. Determines which variables will be captured.
    * @return The tuple (defn, varsMap), where `defn` is the capture class's definition, and
    * `varsMap` maps the function's locals to the corresponding `VarSymbol` (for the class parameters) in the correct order. 
    */
  def createCaptureCls(s: ScopedObject)
      : (ClsLikeDefn, List[(Local, TermSymbol)]) =
    val nme = "Capture$" + s.nme

    val clsSym = ClassSymbol(
      Tree.DummyTypeDef(syntax.Cls),
      Tree.Ident(nme)
    )

    val cap = usedVars.reqdCaptures(s.toInfo)

    val fresh = FreshInt()
    
    val sortedVars = cap.toArray.sortBy(_.uid).map: sym =>
      val id = fresh.make
      val nme = sym.nme + "$" + id
      
      val ident = new Tree.Ident(nme)
      val varSym = VarSymbol(ident)
      val fldSym = BlockMemberSymbol(nme, Nil)
      val tSym = TermSymbol(syntax.MutVal, S(clsSym), ident)
      
      val p = Param(FldFlags.empty.copy(isVal = true), varSym, N, Modulefulness.none)
      varSym.decl = S(p) // * Currently this is only accessed to create the class' toString method
      
      val vd = ValDefn(
        tSym,
        fldSym,
        Value.Ref(varSym)
      )
      
      (sym -> varSym, p, vd)
    
    val defn = ClsLikeDefn(
      None, clsSym, BlockMemberSymbol(nme, Nil),
      S(TermSymbol(syntax.Fun, S(clsSym), clsSym.id)),
      syntax.Cls,
      N,
      PlainParamList(sortedVars.iterator.map(_._2).toList) :: Nil, None, Nil, Nil, 
      Nil,
      End(),
      sortedVars.iterator.foldLeft[Block](End()):
        case (acc, (_, _, vd)) => Define(vd, acc),
      N,
      N,
    )
    
    (defn, sortedVars.iterator.map(x => x._1._1 -> x._3.tsym).toList)
  
  class ScopeRewriter(using ctx: LifterCtxNew) extends BlockTransformerShallow(SymbolSubst()):
    
    val extraDefns: ListBuffer[Defn] = ListBuffer.empty
    
    def applyRewrittenScope[T](r: RewrittenScope[T]): T =
      val LifterResult(rewritten, defns) = liftNestedScopes(r)
      extraDefns ++= defns
      rewritten
    
    override def applyBlock(b: Block): Block = b match
      case s: Scoped =>
        val uid = data.getUID(s)
        applyRewrittenScope(ctx.rewrittenScopes(uid)) match
          case b: Block => b
          case _ => die
      case l: Label if l.loop =>
        val node = data.getNode(l.label)
        val blk = applyRewrittenScope(ctx.rewrittenScopes(l.label)) match
          case b: Block => b
          case _ => die
        l.copy(body = blk)
      case Define(defn, rest) =>
        val dsym = defn match
          case f: FunDefn => f.dSym
          case v: ValDefn => v.tsym
          case c: ClsLikeDefn => c.isym
        ctx.liftedScopes.get(dsym) match
          case Some(_) => applySubBlock(rest)
          case None => super.applyBlock(b)
      case _ => super.applyBlock(b)
    override def applyFunDefn(fun: FunDefn) =
      applyRewrittenScope(ctx.rewrittenScopes(fun.dSym)) match
        case f: FunDefn => f
        case _ => die
    override def applyDefn(defn: Defn)(k: Defn => Block) = defn match
      case f: FunDefn => k(applyFunDefn(f))
      case c: ClsLikeDefn =>
        val newCls = applyRewrittenScope(ctx.rewrittenScopes(c.isym)) match
          case c: ClsLikeDefn => c
          case _ => die
        val newComp = c.companion.map: comp =>
          applyRewrittenScope(ctx.rewrittenScopes(comp.isym)) match
            case c: ClsLikeBody => c
            case _ => die
        k(newCls.copy(companion = newComp))
      case _ => super.applyDefn(defn)(k)

  /**
    * Represents a scoped object that will be rewritten to reference the lifted version of objects and variables.
    */
  sealed abstract class RewrittenScope[T](val obj: TScopedObject[T]):
    val node = obj.node.get
    
    protected val thisCapturedLocals = usedVars.reqdCaptures(obj.toInfo)
    val hasCapture = !thisCapturedLocals.isEmpty
    
    // These are lazy, because we don't necessarily need a captrue 
    private lazy val captureInfo: (ClsLikeDefn, List[(Local, TermSymbol)]) = createCaptureCls(obj)
    
    lazy val captureClass = captureInfo._1
    lazy val captureMap = captureInfo._2.toMap
    
    lazy val capturePath: Path

    protected def rewriteImpl: LifterResult[T]
    
    protected def addCaptureSym(b: Block, captureSym: Local, define: Bool): Block =
      if hasCapture then
        val undef = Value.Lit(Tree.UnitLit(false)).asArg
        val inst = Instantiate(
          true,
          Value.Ref(captureClass.sym, S(captureClass.isym)),
          List.fill(thisCapturedLocals.size)(undef)
        )
        val assign = Assign(captureSym, inst, b)
        if define then
          Scoped(
            Set(captureSym),
            assign
          )
        else assign
      else
        b
    
    /**
      * Rewrites the contents of this scoped object to reference the lifted versions of variables.
      *
      * @return The rewritten scoped object, plus any extra scoped definitions arising from lifting the nested scoped objects.
      */
    def rewrite =
      if hasCapture then
        val LifterResult(defn, extra) = rewriteImpl
        LifterResult(defn, captureClass :: extra)
      else rewriteImpl
    
    /** The path to access locals defined by this object. The primary purpose of this is to rewrite accesses
      * to locals that have been moved to a capture.
      */
    protected def pathsFromThisObj: Map[Local, LocalPath] =
      // Locals introduced by this object
      val fromThisObj = data.getNode(obj.toInfo).localsWithoutLifted
        .map: s =>
          s -> s.asLocalPath
        .toMap
      // Locals introduced by this object that are inside this object's capture
      val fromCap = thisCapturedLocals
        .map: s =>
          val vSym = captureMap(s)
          s -> LocalPath.InCapture(capturePath, vSym)
        .toMap
      // BMS refs from ignored defns
      // Note that we map the DefinitionSymbol to the disambiguated BMS.
      val fromIgnored = node.children.collect:
        case s @ ScopeNode(obj = r: ScopedObject.Referencable[?]) if !s.isLifted =>
          r.sym -> LocalPath.BmsRef(r.bsym, r.sym)
      // Note: the order here is important, as fromCap must override keys from
      // fromThisObj.
      fromThisObj ++ fromCap ++ fromIgnored
    
    lazy val capturePaths =
      if thisCapturedLocals.isEmpty then Map.empty
      else Map(obj.toInfo -> capturePath)
    
    lazy val symbolsMap: Map[Local, LocalPath] = pathsFromThisObj.toMap
  
  /** Represents a scoped object that is to be rewritten and lifted. */
  sealed abstract class LiftedScope[T <: Defn](override val obj: ScopedObject.Liftable[T])(using ctx: LifterCtxNew) extends RewrittenScope[T](obj):
    private val AccessInfo(accessed, _, refdScopes) = usedVars.accessMap(obj.toInfo)
    private val refdDSyms = refdScopes.collect:
        case d: LiftedSym => d
      .toSet
    
    /** Symbols that this object will lose access to once lifted, and therefore must receive
      * as a parameter. Includes neighbouring objects that this definition may lose access to
      * once lifted.
      */
    val reqSymbols = accessed ++ node.reqCaptureObjs.map(_.sym).toSet.intersect(refdDSyms)
    
    private val (reqPassedSymbols, captures) = reqSymbols
      .partitionMap: s =>
        usedVars.capturesMap.get(s) match
          case Some(info) => R((s, info))
          case None => L(s)
    
    /** Locals that are directly passed to this object, i.e. not via a capture. */
    val passedSyms: Set[Local] = reqPassedSymbols
    /** Maps locals to the scope where they were defined. */
    val capturesOrigin: Map[Local, ScopedInfo] = captures.toMap
    /** Locals that are inside captures. */
    val inCaptureSyms: Set[Local] = captures.map(_._1)
    /** Scopes whose captures this object requires. */
    val reqCaptures: Set[ScopedInfo] = captures.map(_._2)
    
    /** Maps directly passed locals to the path representing that local within this object. */
    protected val passedSymsMap: Map[Local, LocalPath]
    /** Maps scopes to the path to the path representing their captures within this object. */
    protected val capSymsMap: Map[ScopedInfo, Path]
    
    protected lazy val capturesOrdered: List[ScopedInfo]
    protected lazy val passedSymsOrdered: List[Local]
    
    override lazy val capturePaths =
      if thisCapturedLocals.isEmpty then capSymsMap
      else capSymsMap + (obj.toInfo -> capturePath)
    
    // Note: we have to make this lazy because Scala's type system is unsound and
    // lets you access the above two fields before they are initialized
    // (since this constructor runs before the child classes' constructors)
    
    /** Maps symbols to the path representing that local within this object.
      * Includes locals defined by this object's parents, and this object's own defined locals.
      */
    override lazy val symbolsMap: Map[Local, LocalPath] = 
      val fromParents = reqSymbols
        .map: s =>
          passedSymsMap.get(s) match
            // The symbol is passed directly
            case Some(value) => s -> value
            // The symbol is passed in a capture
            case None =>
              val fromScope = capturesOrigin(s)
              val capSym = capSymsMap(fromScope)
              val tSym = ctx.rewrittenScopes(fromScope).captureMap(s)
              s -> LocalPath.InCapture(capSym, tSym)
        .toMap
      fromParents ++ pathsFromThisObj
    
    def formatArgs(captures: Map[ScopedInfo, Path], locals: Map[Local, LocalPath]): List[Arg] =
      val captureArgs = capturesOrdered.map(c => captures(c).asArg)
      val localArgs = passedSymsOrdered.map(l => locals(l).asArg)
      captureArgs ::: localArgs
  
  /**
    * A rewritten scope with a generic VarSymbol capture symbol.
    */
  sealed trait GenericRewrittenScope[T] extends RewrittenScope[T]:
    lazy val captureSym = VarSymbol(Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath = captureSym.asPath
    
    protected def addCaptureSym(b: Block): Block = addCaptureSym(b, captureSym, true)
  
  // some helpers
  private def dupParam(p: Param): Param = p.copy(sym = VarSymbol(Tree.Ident(p.sym.nme)))
  private def dupParams(plist: List[Param]): List[Param] = plist.map(dupParam)
  private def dupParamList(plist: ParamList): ParamList =
    plist.copy(params = dupParams(plist.params), restParam = plist.restParam.map(dupParam))
  
  class RewrittenScopedBlock(override val obj: ScopedObject.ScopedBlock)(using ctx: LifterCtxNew) extends RewrittenScope[Block](obj) with GenericRewrittenScope[Block]:
    override def rewriteImpl: LifterResult[Block] =
      val rewriter = new BlockRewriter
      
      // Remove symbols belonging to lifted scopes
      val liftedChildSyms = node.children.collect:
        case s @ ScopeNode(obj = l: ScopedObject.Liftable[?]) if s.isLifted => l.defn.sym
      
      val (syms, rewritten) = (obj.block.syms.toSet -- liftedChildSyms, rewriter.rewrite(obj.block.body))
      val withCapture = addCaptureSym(rewritten)
      LifterResult(Scoped(syms, withCapture), rewriter.extraDefns.toList)
  
  class RewrittenLoop(override val obj: ScopedObject.Loop)(using ctx: LifterCtxNew) extends RewrittenScope[Block](obj) with GenericRewrittenScope[Block]:
    override def rewriteImpl: LifterResult[Block] =
      val rewriter = new BlockRewriter
      
      val rewritten = rewriter.rewrite(obj.body)
      val withCapture = addCaptureSym(rewritten)
      LifterResult(withCapture, rewriter.extraDefns.toList)
  
  class RewrittenFunc(override val obj: ScopedObject.Func)(using ctx: LifterCtxNew) extends RewrittenScope[FunDefn](obj) with GenericRewrittenScope[FunDefn]:
    override def rewriteImpl: LifterResult[FunDefn] =
      val rewriter = new BlockRewriter
      
      val rewritten = rewriter.rewrite(obj.fun.body)
      val withCapture = addCaptureSym(rewritten)
      LifterResult(obj.fun.copy(body = withCapture)(obj.fun.forceTailRec), rewriter.extraDefns.toList)

  class RewrittenClass(override val obj: ScopedObject.Class)(using ctx: LifterCtxNew) extends RewrittenScope[ClsLikeDefn](obj):
    
    private val captureSym = TermSymbol(syntax.ImmutVal, S(obj.cls.isym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath: Path = captureSym.asPath
    
    protected def rewriteMethods =
      val mtds = node.children
        .map: c =>
          ctx.rewrittenScopes(c.obj.toInfo)
        .collect:
          case r: RewrittenFunc if r.obj.isMethod => r 
      val (liftedMtds, extras) = mtds.map(liftNestedScopes).unzip(using l => (l.liftedDefn, l.extraDefns))
      LifterResult(liftedMtds, extras.flatten)
      
    override def rewriteImpl: LifterResult[ClsLikeDefn] =
      val rewriterCtor = new BlockRewriter
      val rewriterPreCtor = new BlockRewriter
      val rewrittenCtor = rewriterCtor.rewrite(obj.cls.ctor)
      val rewrittenPrector = rewriterPreCtor.rewrite(obj.cls.preCtor)
      val preCtorWithCap = addCaptureSym(rewrittenPrector, captureSym, false)
      val LifterResult(newMtds, extras) = rewriteMethods
      val newCls = obj.cls.copy(
        ctor = rewrittenCtor,
        preCtor = preCtorWithCap,
        privateFields = captureSym :: obj.cls.privateFields,
        methods = newMtds
      )
      LifterResult(newCls, rewriterCtor.extraDefns.toList ::: rewriterPreCtor.extraDefns.toList ::: extras)
   
  class LiftedFunc(override val obj: ScopedObject.Func)(using ctx: LifterCtxNew) extends LiftedScope[FunDefn](obj) with GenericRewrittenScope[FunDefn]:
    private val passedSymsMap_ : Map[Local, VarSymbol] = passedSyms.map: s =>
        s -> VarSymbol(Tree.Ident(s.nme))
      .toMap
    private val capSymsMap_ : Map[ScopedInfo, VarSymbol] = reqCaptures.map: i =>
        val nme = data.getNode(i).obj.nme
        i -> VarSymbol(Tree.Ident(nme + "$cap"))
      .toMap
    
    override lazy val capturesOrdered: List[ScopedInfo] = reqCaptures.toList.sortBy(c => capSymsMap_(c).uid)
    override lazy val passedSymsOrdered: List[Local] = passedSyms.toList.sortBy(_.uid)
    
    override protected val passedSymsMap = passedSymsMap_.view.mapValues(_.asLocalPath).toMap
    override protected val capSymsMap = capSymsMap_.view.mapValues(_.asPath).toMap
    
    val auxParams: List[Param] =
      (capSymsMap_.values.toList.sortBy(_.uid) ::: passedSymsMap_.values.toList.sortBy(_.uid))
      .map(Param.simple(_))
    
    // Whether this can be lifted without the need to pass extra parameters.
    val isTrivial = auxParams.isEmpty
    
    val fun = obj.fun
    
    val (mainSym, mainDsym) = (fun.sym, fun.dSym)
    val auxSym = BlockMemberSymbol(fun.sym.nme + "$", Nil, fun.sym.nameIsMeaningful)
    val auxDsym = TermSymbol.fromFunBms(auxSym, fun.owner)
    
    // Definition with the auxiliary parameters merged into the first parameter list.
    private def mkFlattenedDefn: LifterResult[FunDefn] =  
      val newPlists = fun.params match
        case head :: next => head.copy(params = auxParams ::: head.params) :: next
        case Nil => PlainParamList(auxParams) :: Nil
      val rewriter = new BlockRewriter
      val newBod = rewriter.rewrite(fun.body)
      val withCapture = addCaptureSym(newBod)
      val newDefn = fun.copy(sym = mainSym, dSym = mainDsym, params = newPlists, body = withCapture)(fun.forceTailRec)
      LifterResult(newDefn, rewriter.extraDefns.toList)
    
    // Definition with the auxiliary parameters merged into the second parameter list.
    private def mkAuxDefn: FunDefn =
      val newPList = PlainParamList(dupParams(auxParams))
      val (newPlists, syms, restSym) = fun.params match
        case head :: _ =>
          val duped = dupParamList(head)
          (
            newPList :: duped :: Nil,
            newPList.params.map(_.sym) ::: duped.params.map(_.sym),
            duped.restParam.map(_.sym))
        // we need to append an empty param list so calling this function returns a lambda
        case Nil => 
          (
            newPList :: PlainParamList(Nil) :: Nil,
            newPList.params.map(_.sym),
            N
          )
      val args = restSym match
        case Some(value) =>
          val tail = Arg(S(true), value.asPath) :: Nil
          syms.foldLeft(tail):
            case (acc, sym) => Arg(N, sym.asPath) :: acc
        case None => syms.map(s => Arg(N, s.asPath))
      
      val call = Call(Value.Ref(fun.sym, S(fun.dSym)), args)(true, true, false)
      val bod = Return(call, false)
      
      FunDefn(
        fun.owner,
        auxSym,
        auxDsym,
        newPlists,
        bod
      )(false)
    
    def rewriteCall(c: Call, captures: Map[ScopedInfo, Path], locals: Map[Local, LocalPath]): Call =
      if isTrivial then c
      else
        Call(
          Value.Ref(mainSym, S(mainDsym)),
          formatArgs(captures, locals) ::: c.args
        )(
          isMlsFun = true,
          mayRaiseEffects = c.mayRaiseEffects,
          explicitTailCall = c.explicitTailCall
        )
    
    def rewriteRef(captures: Map[ScopedInfo, Path], locals: Map[Local, LocalPath]): Call =
      Call(
        Value.Ref(auxSym, S(auxDsym)),
        formatArgs(captures, locals)
      )(
        isMlsFun = true,
        mayRaiseEffects = false,
        explicitTailCall = false
      )
    
    def rewriteImpl: LifterResult[FunDefn] =
      val LifterResult(lifted, extra) = mkFlattenedDefn
      LifterResult(lifted, mkAuxDefn :: extra)
  
  private def createRewritten[T](s: TScopeNode[T])(using ctx: LifterCtxNew): RewrittenScope[T] = s.obj match
    case _: ScopedObject.Top => lastWords("tried to rewrite the top-level scope")
    case o: ScopedObject.Class =>
      if s.isLifted && !s.isTopLevel then ???
      else RewrittenClass(o)
    case o: ScopedObject.Companion => ???
    case o: ScopedObject.ClassCtor => ???
    case o: ScopedObject.Func =>
      if s.isLifted && !s.isTopLevel then LiftedFunc(o)
      else RewrittenFunc(o)
    case o: ScopedObject.Loop => RewrittenLoop(o)
    case o: ScopedObject.ScopedBlock =>
      RewrittenScopedBlock(o)
  
  // Note: we must write this as a definition here to have tighter types
  private def rewriteScope[T <: Defn](l: LiftedScope[T])(using ctx: LifterCtxNew) =
    val LifterResult[T](d1, d2) = liftNestedScopes[T](l)
    (d1, d2)
  
  /**
    * Lifts scopes nested within `s`, and then rewrites `s`.
    *
    * @param s The scope to be rewritten.
    * @param r The rewritten scope associated with `s`.
    * @param ctx The lifter context.
    * @return The rewritten scope with the additional definitions.
    */
  private def liftNestedScopesImpl[T](scope: RewrittenScope[T])(using ctx: LifterCtxNew): LifterResult[T] =
    val node = scope.node
    
    // Add the symbols map of the current scope
    // Note: this will be reset to the original value in liftNestedScopes
    ctx.symbolsMap ++= scope.symbolsMap
    ctx.capturesMap ++= scope.capturePaths
    
    val rewrittenScopes = node.children.map(createRewritten)
    // The scopes in `lifted` will be rewritten right now
    // The scopes in `ignored` will be rewritten in-place when traversing the block
    val (lifted, ignored) = rewrittenScopes.partitionMap:
      case s: LiftedScope[?] => L(s)
      case s => R(s)
    for r <- rewrittenScopes do
      ctx.rewrittenScopes.put(r.obj.toInfo, r)
    for l <- lifted do
      ctx.liftedScopes.put(l.obj.sym, l)
    
    val LifterResult(rewrittenObj, extraDefns) = scope.rewrite
    val (res1, res2) = lifted.map(rewriteScope).unzip
    val defns = res1 ++ res2.flatten ++ extraDefns
    LifterResult(rewrittenObj, defns)
    
  
  def liftNestedScopes[T](r: RewrittenScope[T])(using ctx: LifterCtxNew): LifterResult[T] =
    val curSyms = ctx.symbolsMap
    val curCaptures = ctx.capturesMap
    val ret = liftNestedScopesImpl(r)
    ctx.symbolsMap = curSyms
    ctx.capturesMap = curCaptures
    ret
  
  def transform =
    given ctx: LifterCtxNew = new LifterCtxNew
    val root = data.root
    
    val children = root.children
    children.foreach: c =>
      ctx.rewrittenScopes.put(c.obj.toInfo, createRewritten(c))
    
    val topLevelRewriter = new ScopeRewriter
    
    val (syms, top) = root.obj.contents match
      case Scoped(syms, body) =>
        (syms.toSet, body)
      case b => (Set.empty, b)
    
    val transformed = topLevelRewriter.applyBlock(top)
    val newSyms = syms ++ topLevelRewriter.extraDefns.map(_.sym)
    val withDefns = topLevelRewriter.extraDefns.foldLeft(transformed):
      case (acc, d) => Define(d, acc)
    Scoped(newSyms, withDefns)
    
    