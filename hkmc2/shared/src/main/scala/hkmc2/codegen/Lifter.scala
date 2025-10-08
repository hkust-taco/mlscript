package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.Tree
import hkmc2.codegen.llir.FreshInt

import scala.collection.mutable.LinkedHashMap
import scala.collection.mutable.Map as MutMap

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
      refdDefns: Set[BlockMemberSymbol]
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
    def withoutBms(locals: Set[BlockMemberSymbol]) = AccessInfo(
        accessed,
        mutated,
        refdDefns -- locals
      )
    def intersectBms(locals: Set[BlockMemberSymbol]) = AccessInfo(
        accessed,
        mutated,
        refdDefns.intersect(locals)
      )
    def addAccess(l: Local) = copy(accessed = accessed + l)
    def addMutated(l: Local) = copy(accessed = accessed + l, mutated = mutated + l)
    def addRefdDefn(l: BlockMemberSymbol) = copy(refdDefns = refdDefns + l)
    
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

  def getVarsBlk(b: Block): Set[Local] =
    b.definedVars.collect:
      case s: LocalVarSymbol => s

  object RefOfBms:
    def unapply(p: Path) = p match
      case Value.Ref(l: BlockMemberSymbol) => S(l)
      case s @ Select(_, _) => s.symbol match
        case Some(value: BlockMemberSymbol) => S(value)
        case _ => N
      case _ => N
  
  object InstSel:
    def unapply(p: Path) = p match
      case Value.Ref(l: BlockMemberSymbol) => S(l)
      case s @ Select(Value.Ref(l: BlockMemberSymbol), Tree.Ident("class")) => S(l)
      case _ => N
  
  def modOrObj(d: Defn) = d match
    case c: ClsLikeDefn => (c.companion.isDefined) || (c.k is syntax.Obj) // TODO: refine handling of companions
    case _ => false


/**
  * Lifts classes and functions to the top-level. Also automatically rewrites lambdas.
  * Assumes the input block does not have any `HandleBlock`s.
  */
class Lifter(handlerPaths: Opt[HandlerPaths])(using State, Raise):
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
    val companionMap: Map[InnerSymbol, InnerSymbol] = Map.empty
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
    
  enum LocalPath:
    case Sym(l: Local)
    case PubField(isym: MemberSymbol[? <: ClassLikeDef] & InnerSymbol, sym: BlockMemberSymbol)
    
    def read = this match
      case Sym(l) => l.asPath
      case PubField(isym, sym) => Select(isym.asPath, Tree.Ident(sym.nme))(S(sym))
      
    def asArg = read.asArg
    
    def assign(value: Result, rest: Block) = this match
      case Sym(l) => Assign(l, value, rest)
      case PubField(isym, sym) => AssignField(isym.asPath, Tree.Ident(sym.nme), value, rest)(S(sym))
    
    
  def isHandlerClsPath(p: Path) = handlerPaths match
    case None => false
    case Some(paths) => paths.isHandlerClsPath(p)
  
  /**
    * Creates a capture class for a function consisting of its mutable (and possibly immutable) local variables.
    * @param f The function to create the capture class for.
    * @param ctx The lifter context. Determines which variables will be captured.
    * @return The triple (defn, varsMap, varsList), where `defn` is the capture class's definition,
    * `varsMap` maps the function's locals to the corresponding `VarSymbol` (for the class parameters), and
    * `varsList` specifies the order of these variables in the class's constructor. 
    */
  def createCaptureCls(f: FunDefn, ctx: LifterCtx)
      : (ClsLikeDefn, Map[Local, VarSymbol], List[Local]) =
    val nme = f.sym.nme + "$capture"

    val clsSym = ClassSymbol(
      Tree.DummyTypeDef(syntax.Cls),
      Tree.Ident(nme)
    )

    val FreeVars(_, cap) = ctx.usedLocals(f.sym)

    val fresh = FreshInt()
    
    val sortedVars = cap.toArray.sortBy(_.uid).map: sym =>
      val id = fresh.make
      val nme = sym.nme + id + "$"
      
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
      syntax.Cls,
      N,
      PlainParamList(sortedVars.iterator.map(_._2).toList) :: Nil, None, Nil, Nil, 
      Nil,
      End(),
      sortedVars.iterator.foldLeft[Block](End()):
        case (acc, (_, _, vd)) => Define(vd, acc),
      N,
    )
    
    (defn, sortedVars.iterator.map(_._1).toMap, sortedVars.iterator.map(_._1._1).toList)

  private val innerSymCache: MutMap[Local, Set[Local]] = MutMap.empty
  
  /**
    * Gets the inner symbols referenced within a class (including those within a member symbol).
    * @param c The class from which to get the inner symbols.
    * @return The inner symbols reference within a class.
    */
  def getInnerSymbols(c: Defn) =
    val sym = c match
      case f: FunDefn => f.sym
      case c: ClsLikeDefn => c.isym
      case _ => wat("unreachable", c.sym)
      
    def create: Set[Local] = c.freeVars.collect:
      case s: InnerSymbol => s
      case t: TermSymbol if t.owner.isDefined => t.owner.get

    innerSymCache.getOrElseUpdate(sym, create)

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
    val captureFnVars = ctx.usedLocals(captureFn.sym).reqCapture.toSet
    !candVars.intersect(captureFnVars).isEmpty
  
  /**
    * Gets the immutable local variables of a function that need to be captured by a definition being lifted.
    * @param captureFn The function in question whose local variables need to be captured.
    * @param liftDefn The definition being lifted.
    * @return The local variables that need to be captured.
    */
  private def neededImutLocals(captureFn: FunDefn, liftDefn: Defn, ctx: LifterCtx) =
    val candVars = liftDefn.freeVars
    val captureFnVars = ctx.usedLocals(captureFn.sym)
    val mutVars = captureFnVars.reqCapture.toSet
    val imutVars = captureFnVars.vars
    imutVars.filter: s =>
      !mutVars.contains(s) && candVars.contains(s)

  // Info required for lifting a definition.
  case class LiftedInfo(
    val reqdCaptures: List[BlockMemberSymbol], // The mutable captures a lifted definition must take.
    val reqdVars: List[Local], // The (passed by value) variables a lifted definition must take.
    val reqdInnerSyms: List[InnerSymbol], // The inner symbols a lifted definition must take.
    val reqdBms: List[BlockMemberSymbol], // BMS's belonging to unlifted definitions that this definition references.
    val fakeCtorBms: Option[BlockMemberSymbol], // only for classes
    val singleCallBms: BlockMemberSymbol, // optimization
  )

  case class Lifted[+T <: Defn](
    val liftedDefn: T,
    val extraDefns: List[Defn],
  )

  // d is a top-level definition
  // returns (ignored classes, modules, objects)
  def createMetadata(d: Defn, ctx: LifterCtx): (Set[BlockMemberSymbol], List[ClsLikeDefn], List[ClsLikeDefn]) =
    var ignored: Set[BlockMemberSymbol] = Set.empty
    var unliftable: Set[BlockMemberSymbol] = Set.empty
    var clsSymToBms: Map[Local, BlockMemberSymbol] = Map.empty
    var modules: List[ClsLikeDefn] = Nil
    var objects: List[ClsLikeDefn] = Nil
    var extendsGraph: Set[(BlockMemberSymbol, BlockMemberSymbol)] = Set.empty
    
    d match
      case c @ ClsLikeDefn(k = syntax.Mod) => modules ::= c
      case c @ ClsLikeDefn(k = syntax.Obj) => objects ::= c
      case _ => ()
    
    // search for modules
    new BlockTraverser:
      applyDefn(d)
      override def applyDefn(defn: Defn): Unit =
        if defn === d then 
          super.applyDefn(defn)
        else 
          defn match
            case c: ClsLikeDefn =>
              clsSymToBms += c.isym -> c.sym
              
              if c.companion.isDefined then // TODO: refine handling of companions
                raise(WarningReport(
                  msg"Modules are not yet lifted." -> N :: Nil,
                  N, Diagnostic.Source.Compilation
                ))
                modules ::= c
                ignored += c.sym
              else if c.k is syntax.Obj then
                objects ::= c
            case _ => ()
          super.applyDefn(defn)
    
    // search for defns nested within a top-level module, which are unnecessary to lift
    def inModuleDefns(d: Defn): Set[BlockMemberSymbol] =
      val nested = ctx.nestedDefns(d.sym)
      nested.map(_.sym).toSet ++ nested.flatMap: nested =>
        if modules.contains(nested.sym) then inModuleDefns(nested) else Set.empty
    
    val isMod = d match
      case c: ClsLikeDefn => c.companion.isDefined // TODO: refine handling of companions
      case _ => false
    
    val inModTopLevel = if isMod then inModuleDefns(d) else Set.empty
    ignored ++= inModTopLevel
    
    // search for unliftable classes and build the extends graph
    val clsSyms = clsSymToBms.values.toSet
    new BlockTraverser:
      applyDefn(d)
      override def applyCase(cse: Case): Unit =
        cse match
          case Case.Cls(cls, path) =>
            clsSymToBms.get(cls) match
            case Some(value) if !ignored.contains(value) => // don't generate a warning if it's already ignored
              raise(WarningReport(
                msg"Cannot yet lift class/module `${value.nme}` as it is used in an instance check." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
              ignored += value
              unliftable += value
            case _ => ()
          case _ => ()
      
      override def applyResult(r: Result): Unit = r match
        case Call(Value.Ref(_: BlockMemberSymbol), args) =>
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
        case ClsLikeDefn(own, isym, sym, k, paramsOpt, auxParams, parentPath, methods,
            privateFields, publicFields, preCtor, ctor, mod)
        =>
          own.foreach(_.traverse)
          isym.traverse
          sym.traverse
          // Check if `extends` is a complex expression, i.e. not just extending a class.
          // If it's just a class, add it to an graph where edges are class extensions.
          // If B extends A, then A -> B is an edge
          parentPath match
            case None => ()
            case Some(path) if isHandlerClsPath(path) => ()
            case Some(Select(RefOfBms(s), Tree.Ident("class"))) =>
              if clsSyms.contains(s) then extendsGraph += (s -> defn.sym)
            case Some(RefOfBms(s)) =>
              if clsSyms.contains(s) then extendsGraph += (s -> defn.sym)
            case _ if !ignored.contains(defn.sym) =>
              raise(WarningReport(
                msg"Cannot yet lift definition `${sym.nme}` as it extends an expression." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
              ignored += defn.sym
              unliftable += defn.sym
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
      
      override def applyValue(v: Value): Unit = v match
        case RefOfBms(l) if clsSyms.contains(l) && !modOrObj(ctx.defns(l)) =>
          raise(WarningReport(
            msg"Cannot yet lift class `${l.nme}` as it is used as a first-class class." -> N :: Nil,
            N, Diagnostic.Source.Compilation
          ))
          ignored += l
          unliftable += l
        case _ => super.applyValue(v)
    
    // analyze the extends graph
    val extendsEdges = extendsGraph.groupBy(_._1).map:
        case (a, bs) => a -> bs.map(_._2)
      .toMap
    var newUnliftable: Set[BlockMemberSymbol] = Set.empty
    // dfs starting from unliftable classes
    def dfs(s: BlockMemberSymbol): Unit =
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
    for s <- ignored do
      dfs(s)
  
    (ignored ++ newUnliftable, modules.toList, objects.toList)
  
  extension (b: Block)
    private def floatOut(ctx: LifterCtx) =
      b.floatOutDefns(preserve = defn => ctx.isModOrObj(defn.sym) || ctx.ignored(defn.sym))
      
  
  def createLiftInfoCont(d: Defn, parentCls: Opt[ClsLikeDefn], ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
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
    
    val modLocal = d match
      case c: ClsLikeDefn if modOrObj(c) && !ctx.ignored(c.sym) => parentCls match
        case None => S(VarSymbol(Tree.Ident(c.sym.nme + "$")))
        case Some(value) => S(TermSymbol(syntax.ImmutVal, S(value.isym), Tree.Ident(c.sym.nme + "$")))
      case _ => N
    
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
        case c: ClsLikeDefn if !modLocal.isDefined => S(BlockMemberSymbol(d.sym.nme + "$ctor", Nil))
        case _ => N
      
      val singleCallBms = BlockMemberSymbol(d.sym.nme + "$", Nil)
      
      val info = LiftedInfo(
        includedCaptures, includedLocals, clsCaptures,
        refBms, fakeCtorBms, singleCallBms
      )
      
      d match
        case f: FunDefn =>
          createLiftInfoFn(f, ctx) + (d.sym -> info)
        case c: ClsLikeDefn =>
          createLiftInfoCls(c, ctx) + (d.sym -> info)
        case _ => Map.empty
  
  def createLiftInfoFn(f: FunDefn, ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val defns = ctx.nestedDefns(f.sym)
    defns.flatMap(createLiftInfoCont(_, N, ctx.addFnLocals(ctx.usedLocals(f.sym)))).toMap

  def createLiftInfoCls(c: ClsLikeDefn, ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val defns = c.preCtor.floatOut(ctx)._2 ++ c.ctor.floatOut(ctx)._2 ++ c.companion.fold(Nil)(_.ctor.floatOut(ctx)._2)
    val newCtx = if (c.companion.isDefined) && !ctx.ignored(c.sym) then ctx else ctx.addClsDefn(c)
    val staticMtdInfo = c.companion.fold(Map.empty):
      case value => value.methods.flatMap(f => createLiftInfoFn(f, newCtx))
    
    defns.flatMap(f => createLiftInfoCont(f, S(c), newCtx)).toMap
      ++ c.methods.flatMap(f => createLiftInfoFn(f, newCtx))
      ++ staticMtdInfo
  
  // This rewrites code so that it's valid when lifted to the top level.
  // This way, no piece of code must be traversed by a BlockRewriter more than once.
  // Remark: This is why so much prior analysis is needed and is the main source of complexity in the lifter.
  class BlockRewriter(inScopeIsyms: Set[InnerSymbol], ctx: LifterCtx) extends BlockTransformerShallow(SymbolSubst()):
    def iSymInScope(l: InnerSymbol) = inScopeIsyms.contains(l)
    
    // Closure symbols that point to an initialized closure in this scope
    var activeClosures: Set[Local] = Set.empty
    // Map from block member symbols to initialized closures
    val closureMap: MutMap[BlockMemberSymbol, Local] = MutMap.empty
    
    
    // Replaces references to BlockMemberSymbols as needed with fresh variables, and
    // returns the mapping from the symbol to the required variable. When possible,
    // it also directly rewrites Results (Calls and Instantiates).
    // Since first-class classes can't be lifted, this is where class
    // instantiations are rewritten.
    //
    // Does *not* rewrite references to non-lifted BMS symbols.
    def rewriteBms(b: Block) =
      // BMS's that need to be created
      val syms: LinkedHashMap[BlockMemberSymbol, Local] = LinkedHashMap.empty

      val walker = new BlockDataTransformer(SymbolSubst()):
        // only scan within the block. don't traverse
        
        override def applyResult(r: Result)(k: Result => Block): Block = r match
          // if possible, directly rewrite the call using the efficient version
          case c @ Call(RefOfBms(l), args) => ctx.bmsReqdInfo.get(l) match
            case Some(info) if !ctx.isModOrObj(l) =>
              val extraArgs = ctx.defns.get(l) match
                // If it's a class, we need to add the isMut parameter.
                // Instantiation without `new mut` is always immutable 
                case Some(c: ClsLikeDefn) => Value.Lit(Tree.BoolLit(false)).asArg :: getCallArgs(l, ctx)
                case _ => getCallArgs(l, ctx)
              applyListOf(args, applyArg(_)(_)): newArgs =>
                k(Call(info.singleCallBms.asPath, extraArgs ++ newArgs)(c.isMlsFun, false))
            case _ => super.applyResult(r)(k)
          case c @ Instantiate(mut, InstSel(l), args) =>
            ctx.bmsReqdInfo.get(l) match
            case Some(info) if !ctx.isModOrObj(l) =>
              val extraArgs = Value.Lit(Tree.BoolLit(mut)).asArg :: getCallArgs(l, ctx)
              applyListOf(args, applyArg(_)(_)): newArgs =>
                k(Call(info.singleCallBms.asPath, extraArgs ++ newArgs)(true, false))
            case _ => super.applyResult(r)(k)
          // LEGACY CODE: We previously directly created the closure and assigned it to the
          // variable here. But, since this closure may be re-used later, this doesn't work
          // in general, so we will always create a TempSymbol for it.
          // case RefOfBms(l) if ctx.bmsReqdInfo.contains(l) && !ctx.isModOrObj(l) =>
          //   createCall(l, ctx)
          case _ => super.applyResult(r)(k)
        
        // extract the call
        override def applyPath(p: Path)(k: Path => Block): Block = 
          p match
          case RefOfBms(l) if ctx.bmsReqdInfo.contains(l) && !ctx.isModOrObj(l) =>
            val newSym = closureMap.get(l) match
              case None =>
                // $this was previously used, but it may be confused with the `this` keyword
                // let's use $here instead
                val newSym = TempSymbol(N, l.nme + "$here")
                syms.addOne(l -> newSym) // add to `syms`: this closure will be initialized in `applyBlock`
                closureMap.addOne(l -> newSym) // add to `closureMap`: `newSym` refers to the closure and can be used later
                newSym

              // symbol exists, and is initialized
              case Some(value) if activeClosures.contains(value) => value
              // symbol exists, needs initialization
              case Some(value) =>
                syms.addOne(l -> value)
                value
            k(Value.Ref(newSym))
          case _ => super.applyPath(p)(k)
      (walker.applyBlock(b), syms.toList)
    end rewriteBms
    
    def applySubBlockAndReset(b: Block): Block =
      val curActive = activeClosures
      val ret = applySubBlock(b)
      activeClosures = curActive
      ret
    
    override def applyBlock(b: Block): Block = 
      // extract references to BlockMemberSymbols in the block which now may
      // need to be enriched with aux parameters
      val (rewritten, syms) = rewriteBms(b)
      val pre = syms.foldLeft(blockBuilder):
        case (blk, (bms, local)) =>
          val initial = blk.assign(local, createCall(bms, ctx))
          ctx.defns(bms) match
            case c: ClsLikeDefn => initial.assignFieldN(local.asPath, Tree.Ident("class"), bms.asPath)
            case _ => initial
      
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
                  then b else Match(scrut2, arms2, dflt2, rst2)
            
        case Label(lbl, bod, rst) =>
          val lbl2 = applyLocal(lbl)
          val bod2 = applySubBlockAndReset(bod)
          val rst2 = applySubBlock(rst)
          if (lbl2 is lbl) && (bod2 is bod) && (rst2 is rst) then b else Label(lbl2, bod2, rst2)
        case TryBlock(sub, fin, rst) =>
          val sub2 = applySubBlockAndReset(sub)
          val fin2 = applySubBlockAndReset(fin)
          val rst2 = applySubBlock(rst)
          if (sub2 is sub) && (fin2 is fin) && (rst2 is rst) then b else TryBlock(sub2, fin2, rst2)
        
        // Detect private field usages
        case Assign(t: TermSymbol, rhs, rest) if t.owner.isDefined =>
          ctx.resolveIsymPath(t.owner.get) match
            case Some(value) if !iSymInScope(t.owner.get) =>
              if (t.k is syntax.LetBind) && !t.owner.forall(_.isInstanceOf[semantics.TopLevelSymbol]) then
                // TODO: improve the error message
                raise(ErrorReport(
                  msg"Uses of private fields cannot yet be lifted." -> N :: Nil,
                  N, Diagnostic.Source.Compilation
                ))
              applyResult(rhs): newRhs =>
                AssignField(value.read, t.id, newRhs, applyBlock(rest))(N)
            case _ => super.applyBlock(rewritten)
        
        // Assignment to variables
        case Assign(lhs, rhs, rest) => ctx.getLocalCaptureSym(lhs) match
          case Some(captureSym) => 
            applyResult(rhs): newRhs =>
              AssignField(ctx.getLocalClosPath(lhs).get.read, captureSym.id, newRhs, applyBlock(rest))(N)
          case None => ctx.getLocalPath(lhs) match
            case None => super.applyBlock(rewritten)
            case Some(value) =>
              applyResult(rhs): newRhs =>
                value.assign(newRhs, applyBlock(rest))
        
        // rewrite ValDefns (in ctors)
        case Define(d: ValDefn, rest: Block) if d.owner.isDefined =>
          ctx.getIsymPath(d.owner.get) match
            case Some(value) if !iSymInScope(d.owner.get) =>
              applyResult(d.rhs): newRhs =>
                AssignField(value.read, Tree.Ident(d.sym.nme), newRhs, applyBlock(rest))(S(d.sym))
            case _ => super.applyBlock(rewritten)
        
        // rewrite object definitions, assigning to the given symbol in modObjLocals
        case Define(d: Defn, rest: Block) => ctx.modObjLocals.get(d.sym) match 
          case Some(sym) if !ctx.ignored(d.sym) => ctx.getBmsReqdInfo(d.sym) match
            case Some(_) => // has args
              blockBuilder
                .assign(sym, Instantiate(mut = false, d.sym.asPath, getCallArgs(d.sym, ctx)))
                .rest(applyBlock(rest))
            case None => // has no args
              blockBuilder
                .assign(sym, Instantiate(mut = false, d.sym.asPath, Nil))
                .rest(applyBlock(rest))
          case _ => ctx.replacedDefns.get(d.sym) match
            case Some(value) => Define(value, applyBlock(rest))
            case None => super.applyBlock(rewritten)
          
        case _ => super.applyBlock(rewritten)
      
      pre.rest(remaining)
    
    override def applyPath(p: Path)(k: Path => Block): Block = 
      p match
      // These two cases rewrites `this.whatever` when referencing an outer class's fields.
      case Value.Ref(l: InnerSymbol) =>
        ctx.resolveIsymPath(l) match
        case Some(value) if !iSymInScope(l) => k(value.read)
        case _ => super.applyPath(p)(k)
      case Value.Ref(t: TermSymbol) if t.owner.isDefined =>
        ctx.resolveIsymPath(t.owner.get) match
          case Some(value) if !iSymInScope(t.owner.get) =>
            if (t.k is syntax.LetBind) && !t.owner.forall(_.isInstanceOf[semantics.TopLevelSymbol]) then
              // TODO: improve the error message
              raise(ErrorReport(
                msg"Uses of private fields cannot yet be lifted." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
            k(Select(value.read, t.id)(N))
          case _ => super.applyPath(p)(k)
      
      // Rewrites this.className.class to reference the top-level definition
      case s @ Select(RefOfBms(l), Tree.Ident("class")) if !ctx.ignored(l) && ctx.isRelevant(l) =>
        // this class will be lifted, rewrite the ref to strip it of `Select`
        k(Select(Value.Ref(l), Tree.Ident("class"))(s.symbol))

      // For objects inside classes: When an object is nested inside a class, its defn will be
      // replaced by a symbol, to which the object instance is assigned. This rewrites references
      // from the objects BlockMemberSymbol to that new symbol.
      case s @ Select(qual, ident) => 
        s.symbol.flatMap(ctx.getLocalPath) match
        case Some(LocalPath.Sym(value: MemberSymbol[?])) =>
          k(Select(qual, Tree.Ident(value.nme))(S(value)))
        case _ => super.applyPath(p)(k)

      // This is to rewrite references to classes that are not lifted (when their BlockMemberSymbol
      // reference is passed as function parameters).
      case RefOfBms(l) if ctx.ignored(l) && ctx.isRelevant(l) => ctx.getIgnoredBmsPath(l) match
        case Some(value) => k(value.read)
        case None => super.applyPath(p)(k)
      
      // This rewrites naked references to locals. If a function is in a capture, then we select that value
      // from the capture; otherwise, we see if that local is passed directly as a parameter to this defn.
      case Value.Ref(l) => ctx.getLocalCaptureSym(l) match
        case Some(captureSym) => 
          k(Select(ctx.getLocalClosPath(l).get.read, captureSym.id)(N))
        case None => ctx.getLocalPath(l) match
          case Some(value) => k(value.read)
          case None => super.applyPath(p)(k)
      case _ => super.applyPath(p)(k)

  // When calling a lifted function or constructor, we need to pass, as arguments, the local variables,
  // inner symbols, etc that it needs to access. This function creates those arguments for that in
  // the correct order.
  def getCallArgs(sym: BlockMemberSymbol, ctx: LifterCtx) =
    val info = ctx.getBmsReqdInfo(sym).get
    val localsArgs = info.reqdVars.map(s => ctx.getLocalPath(s).get.asArg)
    val capturesArgs = info.reqdCaptures.map(ctx.getCapturePath(_).get.asArg)
    val iSymArgs = info.reqdInnerSyms.map(ctx.getIsymPath(_).get.asArg)
    val bmsArgs = info.reqdBms.map(ctx.getIgnoredBmsPath(_).get.asArg)
    bmsArgs ++ iSymArgs ++ localsArgs ++ capturesArgs
  
  // This creates a call to a lifted function or constructor.
  def createCall(sym: BlockMemberSymbol, ctx: LifterCtx): Call =
    val info = ctx.getBmsReqdInfo(sym).get
    val callSym = info.fakeCtorBms match
      case Some(v) => v
      case None => sym
    Call(callSym.asPath, getCallArgs(sym, ctx))(false, false)

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
      case f: FunDefn => liftDefnsInFn(f, ctx)
      case c: ClsLikeDefn => liftDefnsInCls(c, ctx)
      case _ => Lifted(d, Nil)
    case S(LiftedInfo(includedCaptures, includedLocals, clsCaptures, reqdBms, fakeCtorBms, singleCallBms)) =>
      
      def createSymbolsUpdateCtx[T <: LocalPath](createSym: String => (VarSymbol, T))
      : (List[Param], LifterCtx, List[(Local, (VarSymbol, T))])
      =
        val capturesSymbols = includedCaptures.map: sym =>
          (sym, createSym(sym.nme + "$capture"))

        val localsSymbols = includedLocals.map: sym =>
          (sym, createSym(sym.nme))

        val isymSymbols = clsCaptures.map: sym =>
          (sym, createSym(sym.nme + "$instance"))

        val bmsSymbols = reqdBms.map: sym =>
          (sym, createSym(sym.nme + "$member"))

        val extraParamsCaptures = capturesSymbols.map: // parameter list
          case (d, (sym, _)) => Param(FldFlags.empty, sym, N, Modulefulness.none)
        val newCapturePaths = capturesSymbols.map: // mapping from sym to param symbol
            case (d, (_, lp)) => d -> lp
          .toMap

        val extraParamsLocals = localsSymbols.map: // parameter list
          case (d, (sym, _)) => Param(FldFlags.empty, sym, N, Modulefulness.none)
        val newLocalsPaths = localsSymbols.map: // mapping from sym to param symbol
            case (d, (_, lp)) => d -> lp
          .toMap

        val extraParamsIsyms = isymSymbols.map: // parameter list
          case (d, (sym, _)) => Param(FldFlags.empty, sym, N, Modulefulness.none)
        val newIsymPaths = isymSymbols.map: // mapping from sym to param symbol
            case (d, (_, lp)) => d -> lp
          .toMap

        val extraParamsBms = bmsSymbols.map: // parameter list
          case (d, (sym, _)) => Param(FldFlags.empty, sym, N, Modulefulness.none)
        val newBmsPaths = bmsSymbols.map: // mapping from sym to param symbol
            case (d, (_, lp)) => d -> lp
          .toMap

        val extraParams = extraParamsBms ++ extraParamsIsyms ++ extraParamsLocals ++ extraParamsCaptures

        val newCtx = ctx
          .replCapturePaths(newCapturePaths)
          .replLocalPaths(newLocalsPaths)
          .addIsymPaths(newIsymPaths)
          .replIgnoredBmsPaths(newBmsPaths)
        
        (extraParams, newCtx, capturesSymbols ++ localsSymbols ++ isymSymbols ++ bmsSymbols)

      d match
        case f: FunDefn =>
          val createSym = (nme: String) =>
            val vsym = VarSymbol(Tree.Ident(nme))
            (vsym, LocalPath.Sym(vsym))
          val (extraParams, newCtx, _) = createSymbolsUpdateCtx(createSym)
          
          // create second param list with different symbols
          val extraParamsCpy = extraParams.map(p => p.copy(sym = VarSymbol(p.sym.id)))

          val headPlistCopy = f.params.headOption match
            case None => PlainParamList(Nil)
            case Some(value) => ParamList(value.flags, value.params.map(p => p.copy(sym = VarSymbol(p.sym.id))), value.restParam)
          
          val flatPlist = f.params match
            case head :: next => ParamList(head.flags, extraParams ++ head.params, head.restParam) :: next
            case Nil => PlainParamList(extraParams) :: Nil

          val newDef = FunDefn(
            base.owner, f.sym, PlainParamList(extraParams) :: f.params, f.body
          )
          val Lifted(lifted, extras) = liftDefnsInFn(newDef, newCtx)

          val args1 = extraParamsCpy.map(p => p.sym.asPath.asArg)
          val args2 = headPlistCopy.params.map(p => p.sym.asPath.asArg)

          val bdy = blockBuilder
            .ret(Call(singleCallBms.asPath, args1 ++ args2)(true, false)) // TODO: restParams not considered

          val mainDefn = FunDefn(f.owner, f.sym, PlainParamList(extraParamsCpy) :: headPlistCopy :: Nil, bdy)
          val auxDefn = FunDefn(N, singleCallBms, flatPlist, lifted.body)
          

          Lifted(mainDefn, auxDefn :: extras)
        case c: ClsLikeDefn =>
          val createSym: String => (VarSymbol, LocalPath.PubField) = 
            // due to the possibility of capturing a TempSymbol in HandlerLowering, it is necessary to generate a discriminator
            val fresh = FreshInt()
            (nme: String) =>
              val id = fresh.make
              (
                VarSymbol(Tree.Ident(nme + "$" + id)),
                LocalPath.PubField(c.isym, BlockMemberSymbol(nme + "$" + id, Nil, true))
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
            liftDefnsInCls(newDef, newCtx)
          else // normal class
            
            val newDef = c.copy(
              owner = N, 
              auxParams = newAuxParams,
              publicFields = newPubFields,
              ctor = newCtor
            )
            
            val Lifted(lifted, extras) = liftDefnsInCls(newDef, newCtx)
            
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
            
            var curSym = TempSymbol(None, "tmp")
            def instInner(isMut: Bool) = if c.paramsOpt.isDefined
              then Instantiate(mut = isMut, Select(c.sym.asPath, Tree.Ident("class"))(N), paramArgs)
              else Instantiate(mut = isMut, c.sym.asPath, paramArgs)
            
            val initSym = curSym
            
            var acc: Block => Block = blk => Match(
              isMutSym.asPath,
              Case.Lit(Tree.BoolLit(true)) -> Assign(initSym, instInner(true), End()) :: Nil,
              S(Assign(initSym, instInner(false), End())),
              blk
            )
            
            for ps <- newAuxSyms do
              val call = Call(curSym.asPath, ps.map(_.asPath.asArg))(true, false)
              curSym = TempSymbol(None, "tmp")
              val thisSym = curSym
              acc = acc.assign(thisSym, call)
              // acc = blk => acc(Assign(curSym, call, blk))
            val bod = acc.ret(curSym.asPath)
            
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
            
            val auxCtorDefn_ = FunDefn(None, singleCallBms, headParams :: newAuxPlist, bod)
            val auxCtorDefn = BlockTransformer(subst).applyFunDefn(auxCtorDefn_)
            
            // Lifted(lifted, extras ::: (fakeCtorDefn :: auxCtorDefn :: Nil))
            Lifted(lifted, extras ::: (auxCtorDefn :: Nil))
        case _ => Lifted(d, Nil)
  
  end liftOutDefnCont
  
  def liftDefnsInCls(c: ClsLikeDefn, ctx: LifterCtx): Lifted[ClsLikeDefn] =
    val ctxx = if c.companion.isDefined then ctx.inModule(c) else ctx // TODO: refine handling of companions
    
    // ===========================================================
    // STEP 1: lift out definitions nested in the ctor and prector
    //         and deal with class defns in the companion class
    
    val (preCtor, preCtorDefns) = c.preCtor.floatOut(ctxx)
    val (ctor, ctorDefns) = c.ctor.floatOut(ctxx)
    val (cCtor, cCtorDefns) = c.companion.fold((None, Nil)):
      case value =>
        val (a, b) = value.ctor.floatOut(ctxx)
        (S(a), b)

    val allCtorDefns = preCtorDefns ++ ctorDefns ++ cCtorDefns
    
    // ctorIgnored: definitions within the class (i.e. ctor) that we don't lift
    // ctorIncluded: ditto, but lifted
    val (ctorIgnored, ctorIncluded) = allCtorDefns.partition(d => ctxx.ignored(d.sym))

    // Deals with references to lifted objects defined within the class
    val nestedClsPaths: Map[Local, LocalPath] = ctorIncluded.map:
        case c: ClsLikeDefn if modOrObj(c) => ctxx.modObjLocals.get(c.sym) match
          case Some(sym) => S(c.sym -> LocalPath.Sym(sym))
          case _ => S(c.sym -> LocalPath.Sym(c.sym))
        case _ => None
      .collect:
        case Some(x) => x
      .toMap
    
    val newCtx_ = ctxx
      // references to lifted objects
      .addLocalPaths(nestedClsPaths)
      // references to variables defined in the class, including ones in the companion obj
      .addLocalPaths(getVars(c).map(s => s -> LocalPath.Sym(s)).toMap)
      // reference to unlifted BMS's
      .addIgnoredBmsPaths(ctorIgnored.map(d => d.sym -> LocalPath.Sym(d.sym)).toMap)
      .addIsymPath(c.isym, LocalPath.Sym(c.isym))
      .inISym(c.isym)
      
    // add the reference to `this` if it has a companion object
    val newCtx = c.companion match
      case None => newCtx_
      case Some(value) => newCtx_.addIsymPath(value.isym, LocalPath.Sym(c.sym)).inISym(value.isym)
    
    // lifts the liftable definitions
    // lifted defns can no longer access currently in-scope isyms, so call resetScope
    val ctorDefnsLifted = ctorIncluded.flatMap: defn =>
      val Lifted(liftedDefn, extraDefns) = liftOutDefnCont(c, defn, newCtx.flushModules.resetScope)
      liftedDefn :: extraDefns
    
    // we still need to lift out definitions within unliftable defns
    val ctorIgnoredLift = ctorIgnored.map: defn =>
      liftOutDefnCont(c, defn, newCtx)
    
    // we still need to rewrite definitions that aren't lifted
    // this map tells us how to rewrite the Defns
    val ctorIgnoredExtra = ctorIgnoredLift.flatMap(_.extraDefns)
    val ctorIgnoredRewrite = ctorIgnoredLift.map: lifted =>
        lifted.liftedDefn.sym -> lifted.liftedDefn
      .toMap
    
    val replacedDefnsCtx = newCtx.addreplacedDefns(ctorIgnoredRewrite)
    val rewriter = BlockRewriter(newCtx.inScopeISyms, replacedDefnsCtx)
    val newPreCtor = rewriter.applyBlock(preCtor)
    val newCtor = rewriter.applyBlock(ctor)
    val newCCtor = cCtor.map(rewriter.applyBlock(_))
    
    // ===========================================================
    // STEP 2: rewrite non-static class methods
    
    val fLifted = c.methods.map(liftDefnsInFn(_, newCtx))
    val methods = fLifted.collect:
      case Lifted(liftedDefn, extraDefns) => liftedDefn
    val fExtra = fLifted.flatMap:
      case Lifted(liftedDefn, extraDefns) => extraDefns
      
    // ===========================================================
    // STEP 3: rewrite companion class methods
        
    val cfLifted = c.companion.fold(Nil)(_.methods.map(liftDefnsInFn(_, newCtx)))
      
    val cMethods = cfLifted.collect:
      case Lifted(liftedDefn, extraDefns) => liftedDefn
    val cfExtra = cfLifted.flatMap:
      case Lifted(liftedDefn, extraDefns) => extraDefns
      
    val newCompanion = c.companion.fold(None):
      case value => S(value.copy(methods = cMethods, ctor = newCCtor.get))

    val extras = (ctorDefnsLifted ++ fExtra ++ cfExtra ++ ctorIgnoredExtra).map:
      case f: FunDefn => f.copy(owner = N)
      case c: ClsLikeDefn => c.copy(owner = N)
      case d => d

    def rewriteExtends(p: Path): Path = p match
      case RefOfBms(b) if !ctx.ignored(b) && ctx.isRelevant(b) => b.asPath
      case Select(RefOfBms(b), Tree.Ident("class")) if !ctx.ignored(b) && ctx.isRelevant(b) => 
        Select(b.asPath, Tree.Ident("class"))(N)
      case _ => return p
      
    // if this class extends something, rewrite
    val newPar = c.parentPath.map(rewriteExtends)

    val newDef = c.copy(
      methods = methods,
      preCtor = newPreCtor,
      parentPath = newPar,
      ctor = newCtor,
      companion = newCompanion,
    )
    
    Lifted(newDef, extras)
  
  end liftDefnsInCls

  def liftDefnsInFn(f: FunDefn, ctx: LifterCtx): Lifted[FunDefn] =
    val (captureCls, varsMap, varsList) = createCaptureCls(f, ctx)
    
    val (blk, nested) = f.body.floatOut(ctx)

    val (ignored, included) = nested.partition(d => ctx.ignored(d.sym))

    val modPaths: Map[Local, LocalPath] = nested.map:
        case c: ClsLikeDefn if modOrObj(c) => ctx.modObjLocals.get(c.sym) match
          case Some(sym) => S(c.sym -> LocalPath.Sym(sym))
          case _ => S(c.sym -> LocalPath.Sym(c.sym))
        case _ => None
      .collect:
        case Some(x) => x
      .toMap

    val thisVars = ctx.usedLocals(f.sym)
    // add the mapping from this function's locals to the capture's symbols and the capture path
    val captureSym = TempSymbol(N, "capture")
    val captureCtx = ctx
      .addLocalCaptureSyms(varsMap) // how to access locals via the capture class from now on
      .addCapturePath(f.sym, LocalPath.Sym(captureSym)) // the path to this function's capture
      .addLocalPaths((thisVars.vars.toSet -- thisVars.reqCapture).map(s => s -> LocalPath.Sym(s)).toMap)
      .addLocalPaths(modPaths)
      .addIgnoredBmsPaths(ignored.map(d => d.sym -> LocalPath.Sym(d.sym)).toMap)
    val nestedCtx = captureCtx.addFnLocals(captureCtx.usedLocals(f.sym))

    // lift out the nested defns
    // for lifted definitions, any accessible isyms go out of scope, so call resetScope
    val nestedLifted = included.map(liftOutDefnCont(f, _, nestedCtx.flushModules.resetScope))
    val ignoredLifted = ignored.map(liftOutDefnCont(f, _, nestedCtx))
    val ignoredExtra = ignoredLifted.flatMap(_.extraDefns)
    val newDefns = ignoredExtra ++ nestedLifted.flatMap:
      case Lifted(liftedDefn, extraDefns) => liftedDefn :: extraDefns
      
    val ignoredRewrite = ignoredLifted.map: lifted =>
        lifted.liftedDefn.sym -> lifted.liftedDefn
      .toMap

    val transformed = BlockRewriter(ctx.inScopeISyms, captureCtx.addreplacedDefns(ignoredRewrite)).applyBlock(blk)

    if thisVars.reqCapture.size == 0 then
      Lifted(FunDefn(f.owner, f.sym, f.params, transformed), newDefns)
    else
      // move the function's parameters to the capture
      val paramsSet = f.params.flatMap(_.paramSyms)
      val paramsList = varsList.map: s =>
        (if paramsSet.contains(s) then s.asPath else Value.Lit(Tree.UnitLit(true))).asArg
      // moved when the capture is instantiated
      val bod = blockBuilder
        .assign(captureSym, Instantiate(mut = true, // * Note: `mut` is needed for capture classes
          captureCls.sym.asPath, paramsList))
        .rest(transformed)
      Lifted(FunDefn(f.owner, f.sym, f.params, bod), captureCls :: newDefns)

  end liftDefnsInFn

  // top-level
  def transform(_blk: Block) =
    // this is already done once in the lowering, but the handler lowering adds lambdas currently
    // so we need to desugar them again
    val blk = LambdaRewriter.desugar(_blk)

    val analyzer = UsedVarAnalyzer(blk, handlerPaths)
    val ctx = LifterCtx
      .withLocals(analyzer.findUsedLocals)
      .withDefns(analyzer.defnsMap)
      .withNestedDefns(analyzer.nestedDefns)
      .withAccesses(analyzer.accessMap)
      .withInScopes(analyzer.inScopeDefns)
      .withCompanionMap(analyzer.companionMap)

    val walker1 = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(d, rest) =>
          val (unliftable, modules, objects) = createMetadata(d, ctx)

          val modObjLocals = (modules ++ objects).map: c =>
              analyzer.nestedIn.get(c.sym) match
                case Some(bms) =>
                  val nestedIn = analyzer.defnsMap(bms)
                  nestedIn match
                    case cls: ClsLikeDefn => S(c.sym -> TermSymbol(syntax.ImmutVal, S(cls.isym), Tree.Ident(c.sym.nme + "$")))
                    case _ => S(c.sym -> VarSymbol(Tree.Ident(c.sym.nme + "$")))
                case _ => N
            .collect:
              case S(v) => v
            .toMap

          val ctxx = ctx
            .addIgnored(unliftable)
            .withModObjLocals(modObjLocals)
          
          val Lifted(lifted, extra) = d match
            case f: FunDefn => 
              val ctxxx = ctxx.withDefnsCur(analyzer.nestedDeep(d.sym))
              liftDefnsInFn(f, ctxxx.addBmsReqdInfo(createLiftInfoFn(f, ctxxx)))
            case c: ClsLikeDefn => 
              val ctxxx = ctxx.withDefnsCur(analyzer.nestedDeep(d.sym))
              liftDefnsInCls(c, ctxxx.addBmsReqdInfo(createLiftInfoCls(c, ctxxx)))
            case _ => return super.applyBlock(b)
          (lifted :: extra).foldLeft(applyBlock(rest))((acc, defn) => Define(defn, acc))
        case _ => super.applyBlock(b)
    walker1.applyBlock(blk)
