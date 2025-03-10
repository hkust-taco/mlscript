package hkmc2

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

  def getVars(d: Defn)(using state: State): Set[Local] = d match
    case f: FunDefn =>
      (f.body.definedVars ++ f.params.flatMap(_.paramSyms)).collect:
        case s: FlowSymbol if !(s is state.runtimeSymbol) => s
    case c: ClsLikeDefn =>
      (c.preCtor.definedVars ++ c.ctor.definedVars).collect:
        case s: FlowSymbol if !(s is state.runtimeSymbol) => s
    case _ => Set.empty

  def getVarsBlk(b: Block)(using state: State): Set[Local] =
    b.definedVars.collect:
      case s: FlowSymbol if !(s is state.runtimeSymbol) => s

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
    case c: ClsLikeDefn => (c.k is syntax.Mod) || (c.k is syntax.Obj)
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
    * @param modLocals A map from the modules and objects to the local to which it is instantiated after lifting.
    * @param localCaptureSyms The symbols in a capture corresponding to a particular local. 
    * The `VarSymbol` is the parameter in the capture class, and the `BlockMemberSymbol` is the field in the class.
    * @param prevFnLocals Locals belonging to function definitions that have already been traversed
    * @param prevClsDefns Class definitions that have already been traversed, excluding modules
    * @param curModules Modules that that we are currently nested in (cleared if we are lifted out)
    * @param capturePaths The path to access a particular function's capture in the local scope
    * @param bmsReqdInfo The (mutable) captures and (immutable) local variables each function requires
    * @param ignoredBmsPaths The path to access a particular BlockMemberSymbol (for definitions which could not be lifted)
    * @param localPaths The path to access a particular local (possibly belonging to a previous function) in the current scope
    * @param iSymPaths The path to access a particular `innerSymbol` (possibly belonging to a previous class) in the current scope
    * @param replacedDefns Ignored (unlifted) definitions that have been rewritten and need to be replaced at the definition site.
    */
  case class LifterCtx private (
    val defns: Map[BlockMemberSymbol, Defn] = Map.empty,
    val defnsCur: Set[BlockMemberSymbol] = Set.empty,
    val nestedDefns: Map[BlockMemberSymbol, List[Defn]] = Map.empty,
    val usedLocals: UsedLocalsMap = UsedLocalsMap(Map.empty),
    val accessInfo: Map[BlockMemberSymbol, AccessInfo] = Map.empty,
    val ignoredDefns: Set[BlockMemberSymbol] = Set.empty,
    val inScopeDefns: Map[BlockMemberSymbol, Set[BlockMemberSymbol]] = Map.empty,
    val modLocals: Map[BlockMemberSymbol, Local] = Map.empty,
    val localCaptureSyms: Map[Local, (VarSymbol, BlockMemberSymbol)] = Map.empty,
    val prevFnLocals: FreeVars = FreeVars.empty,
    val prevClsDefns: List[ClsLikeDefn] = Nil,
    val curModules: List[ClsLikeDefn] = Nil,
    val capturePaths: Map[BlockMemberSymbol, Path] = Map.empty,
    val bmsReqdInfo: Map[BlockMemberSymbol, LiftedInfo] = Map.empty, // required captures
    val ignoredBmsPaths: Map[BlockMemberSymbol, Path] = Map.empty,
    val localPaths: Map[Local, Local] = Map.empty,
    val isymPaths: Map[InnerSymbol, Local] = Map.empty,
    val replacedDefns: Map[BlockMemberSymbol, Defn] = Map.empty,
  ):
    // gets the function to which a local belongs
    def lookup(l: Local) = usedLocals.lookup(l)

    def getCapturePath(b: BlockMemberSymbol) = capturePaths.get(b)
    def getLocalClosPath(l: Local) = lookup(l).flatMap(capturePaths.get(_))
    def getLocalCaptureSym(l: Local) = localCaptureSyms.get(l)
    def getLocalPath(l: Local) = localPaths.get(l)
    def getIsymPath(l: InnerSymbol) = isymPaths.get(l)
    def getIgnoredBmsPath(b: BlockMemberSymbol) = ignoredBmsPaths.get(b)
    def ignored(b: BlockMemberSymbol) = ignoredDefns.contains(b)
    def isModOrObj(b: BlockMemberSymbol) = modLocals.contains(b)
    def getAccesses(sym: BlockMemberSymbol) = accessInfo(sym)
    def isRelevant(sym: BlockMemberSymbol) = defnsCur.contains(sym)
    
    def addIgnored(defns: Set[BlockMemberSymbol]) = copy(ignoredDefns = ignoredDefns ++ defns)
    def withModLocals(mp: Map[BlockMemberSymbol, Local]) = copy(modLocals = modLocals ++ mp)
    def withDefns(mp: Map[BlockMemberSymbol, Defn]) = copy(defns = mp)
    def withDefnsCur(defns: Set[BlockMemberSymbol]) = copy(defnsCur = defns)
    def withNestedDefns(mp: Map[BlockMemberSymbol, List[Defn]]) = copy(nestedDefns = mp)
    def withAccesses(mp: Map[BlockMemberSymbol, AccessInfo]) = copy(accessInfo = mp)
    def withInScopes(mp: Map[BlockMemberSymbol, Set[BlockMemberSymbol]]) = copy(inScopeDefns = mp)
    def addFnLocals(f: FreeVars) = copy(prevFnLocals = prevFnLocals ++ f)
    def addClsDefn(c: ClsLikeDefn) = copy(prevClsDefns = c :: prevClsDefns)
    def addLocalCaptureSyms(m: Map[Local, (VarSymbol, BlockMemberSymbol)]) = copy(localCaptureSyms = localCaptureSyms ++ m)
    def getBmsReqdInfo(sym: BlockMemberSymbol) = bmsReqdInfo.get(sym)
    def replCapturePaths(paths: Map[BlockMemberSymbol, Path]) = copy(capturePaths = paths)
    def addCapturePath(src: BlockMemberSymbol, path: Path) = copy(capturePaths = capturePaths + (src -> path))
    def addBmsReqdInfo(mp: Map[BlockMemberSymbol, LiftedInfo]) = copy(bmsReqdInfo = bmsReqdInfo ++ mp)
    def replLocalPaths(m: Map[Local, Local]) = copy(localPaths = m)
    def replIgnoredBmsPaths(m: Map[BlockMemberSymbol, Path]) = copy(ignoredBmsPaths = m)
    def replIsymPaths(m: Map[InnerSymbol, Local]) = copy(isymPaths = m)
    def addLocalPaths(m: Map[Local, Local]) = copy(localPaths = localPaths ++ m)
    def addLocalPath(target: Local, path: Local) = copy(localPaths = localPaths + (target -> path))
    def addIgnoredBmsPaths(m: Map[BlockMemberSymbol, Path]) = copy(ignoredBmsPaths = ignoredBmsPaths ++ m)
    def addIsymPath(isym: InnerSymbol, l: Local) = copy(isymPaths = isymPaths + (isym -> l))
    def addIsymPaths(mp: Map[InnerSymbol, Local]) = copy(isymPaths = isymPaths ++ mp)
    def addreplacedDefns(mp: Map[BlockMemberSymbol, Defn]) = copy(replacedDefns = replacedDefns ++ mp)
    def inModule(defn: ClsLikeDefn) = copy(curModules = defn :: curModules)
    def flushModules = 
      // called when we are lifted out while in some modules, so we need to add the modules' isym paths
      copy(curModules = Nil).addIsymPaths(curModules.map(d => d.isym -> d.sym).toMap)
  
  object LifterCtx:
    def empty = LifterCtx()
    def withLocals(u: UsedLocalsMap) = empty.copy(usedLocals = u)
    
  def isHandlerClsPath(p: Path) = handlerPaths match
    case None => false
    case Some(paths) => paths.isHandlerClsPath(p)
  
  /**
    * Creates a capture class for a function consisting of its mutable (and possibly immutable) local variables.
    * @param f The function to create the capture class for.
    * @param ctx The lifter context. Determines which variables will be captured.
    * @return The triple (defn, varsMap, varsList), where `defn` is the capture class's definition,
    * `varsMap` maps the function's locals to the correpsonding `VarSymbol` (for the class parameters)
    *  and `BlockLocalSymbol` (for the class fields) in the class, and
    * `varsList` specifies the order of these variables in the class's constructor. 
    */
  def createCaptureCls(f: FunDefn, ctx: LifterCtx) =
    val nme = f.sym.nme + "$capture"

    val clsSym = ClassSymbol(
      Tree.DummyTypeDef(syntax.Cls),
      Tree.Ident(nme)
    )

    val FreeVars(_, cap) = ctx.usedLocals(f.sym)

    val fresh = FreshInt()

    val varsMap = cap.map: s =>
        val id = fresh.make
        val nme = s.nme + id + "$"
        val varSym = VarSymbol(Tree.Ident(nme))
        val fldSym = BlockMemberSymbol(nme, Nil)
        val fldDef = TermDefinition(
          S(clsSym),
          syntax.ImmutVal,
          fldSym,
          Nil, N, N,
          S(Term.Ref(s)(Tree.Ident(s.nme), 666)), // FIXME: 666 is a dummy value
          FlowSymbol("‹class-param-res›"),
          TermDefFlags.empty,
          Nil
        )
        fldSym.defn = S(fldDef)
        s -> (
          varSym,
          fldDef,
        )
      .toMap

    val varsList = cap.toList
    
    val defn = ClsLikeDefn(
      None, clsSym, BlockMemberSymbol(nme, Nil),
      syntax.Cls,
      S(PlainParamList(varsList.map: s => 
        val sym = varsMap(s)._1
        val p = Param(FldFlags.empty.copy(value = true), sym, None)
        sym.decl = S(p)
        p
      )),
      Nil, None, Nil, Nil, 
      varsList.map(varsMap(_)._2),
      varsList.map(varsMap(_)).foldLeft[Block](End()):
        case (acc, (varSym, fldDef)) =>
          AssignField(
            clsSym.asPath,
            Tree.Ident(fldDef.sym.nme),
            Value.Ref(varSym),
            acc
          )(S(fldDef.sym))
      ,
      End()
    )

    (defn, varsMap.view.mapValues(_.mapSecond(_.sym)).toMap, varsList)

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

  case class LiftedInfo(
    val reqdCaptures: List[BlockMemberSymbol],
    val reqdVars: List[Local],
    val reqdInnerSyms: List[InnerSymbol],
    val reqdBms: List[BlockMemberSymbol], // pass ignored blockmembersymbols
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
      case c @ ClsLikeDefn(k = syntax.Mod) => modules +:= c
      case c @ ClsLikeDefn(k = syntax.Obj) => objects +:= c
      case _ => ()

    // search for modules
    new BlockTraverser(SymbolSubst()):
      applyDefn(d)
      override def applyDefn(defn: Defn): Unit =
        if defn === d then 
          super.applyDefn(defn)
        else 
          defn match
            case c: ClsLikeDefn =>
              clsSymToBms += c.isym -> c.sym
              
              if c.k is syntax.Mod then
                raise(WarningReport(
                  msg"Modules are not yet lifted." -> N :: Nil,
                  N, Diagnostic.Source.Compilation
                ))
                modules +:= c
                ignored += c.sym
              else if c.k is syntax.Obj then
                objects +:= c
            case _ => ()
          super.applyDefn(defn)

    // search for defns nested within a top-level module, which are unnecessary to lift
    def inModuleDefns(d: Defn): Set[BlockMemberSymbol] =
      val nested = ctx.nestedDefns(d.sym)
      nested.map(_.sym).toSet ++ nested.flatMap: nested =>
        if modules.contains(nested.sym) then inModuleDefns(nested) else Set.empty

    val isMod = d match
      case c: ClsLikeDefn if c.k is syntax.Mod => true
      case _ => false

    val inModTopLevel = if isMod then inModuleDefns(d) else Set.empty
    ignored ++= inModTopLevel
    
    // search for unliftable classes and build the extends graph
    val clsSyms = clsSymToBms.values.toSet
    new BlockTraverser(SymbolSubst()):
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
          args.map(applyArg)
        case Instantiate(InstSel(_), args) =>
          args.map(applyPath)

        case _ => super.applyResult(r)

      override def applyDefn(defn: Defn): Unit = defn match
        case defn: FunDefn => applyFunDefn(defn)
        case ValDefn(owner, k, sym, rhs) =>
          owner.mapConserve(_.subst)
          sym.subst
          applyPath(rhs)
        case ClsLikeDefn(own, isym, sym, k, paramsOpt, auxParams, parentPath, methods,
          privateFields, publicFields, preCtor, ctor) =>
          own.mapConserve(_.subst)
          isym.subst
          sym.subst
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
                msg"Cannot yet lift class/module `${sym.nme}` as it extends an expression." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
              ignored += defn.sym
              unliftable += defn.sym
            case _ => ()
          paramsOpt.map(applyParamList)
          auxParams.map(applyParamList)
          methods.map(applyFunDefn)
          privateFields.map(_.subst)
          publicFields.map(applyTermDefinition)
          applyBlock(preCtor)
          applyBlock(ctor)

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
          msg"Cannot yet lift class/module `${b.nme}` as it extends an unliftable class." -> N :: Nil,
          N, Diagnostic.Source.Compilation
        ))
        newUnliftable += b
        dfs(b)
    for s <- ignored do
      dfs(s)
    
    (ignored ++ newUnliftable, modules, objects)

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

    val refMod = inScopeRefs.intersect(ctx.modLocals.keySet)
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
    val defns = c.preCtor.floatOut(ctx)._2 ++ c.ctor.floatOut(ctx)._2
    val newCtx = if (c.k is syntax.Mod) && !ctx.ignored(c.sym) then ctx else ctx.addClsDefn(c)
    defns.flatMap(f => createLiftInfoCont(f, S(c), newCtx)).toMap
      ++ c.methods.flatMap(f => createLiftInfoFn(f, newCtx))

  // replaces references to BlockMemberSymbols as needed with fresh variables, and
  // returns the mapping from the symbol to the required variable. When possible,
  // it also directly rewrites Results.
  def rewriteBms(b: Block, ctx: LifterCtx) =
    val syms: LinkedHashMap[BlockMemberSymbol, Local] = LinkedHashMap.empty

    val walker = new BlockDataTransformer(SymbolSubst()):
      // only scan within the block. don't traverse
      
      override def applyResult(r: Result): Result = r match
        // if possible, directly rewrite the call using the efficient version
        case c @ Call(RefOfBms(l), args) => ctx.bmsReqdInfo.get(l) match
          case Some(info) if !ctx.isModOrObj(l) =>
            val extraArgs = getCallArgs(l, ctx)
            val newArgs = args.map(applyArg(_))
            Call(info.singleCallBms.asPath, extraArgs ++ newArgs)(c.isMlsFun, false)
          case _ => super.applyResult(r)
        case c @ Instantiate(InstSel(l), args) =>
          ctx.bmsReqdInfo.get(l) match
          case Some(info) if !ctx.isModOrObj(l) =>
            val extraArgs = getCallArgs(l, ctx)
            val newArgs = args.map(applyPath(_)).map(_.asArg)
            Call(info.singleCallBms.asPath, extraArgs ++ newArgs)(true, false)
          case _ => super.applyResult(r)
        // if possible, directly create the bms and replace the result with it
        case RefOfBms(l) if ctx.bmsReqdInfo.contains(l) && !ctx.isModOrObj(l) =>
          createCall(l, ctx)
        case _ => super.applyResult(r)
      
      // otherwise, there's no choice but to create the call earlier
      override def applyPath(p: Path): Path = p match
        case RefOfBms(l) if ctx.bmsReqdInfo.contains(l) && !ctx.isModOrObj(l) =>
          val newSym = syms.get(l) match
            case None =>
              val newSym = FlowSymbol(l.nme + "$this")
              syms.addOne(l -> newSym)
              newSym
            case Some(value) => value
          Value.Ref(newSym)
        case _ => super.applyPath(p)
    (walker.applyBlock(b), syms.toList)
  end rewriteBms
  
  class BlockRewriter(ctorCls: Opt[ClsLikeDefn], ctx: LifterCtx) extends BlockTransformerShallow(SymbolSubst()):
    def belongsToCtor(l: Symbol) =
      ctorCls match
      case None => false
      case Some(value) =>
        value.isym === l
        
    override def applyBlock(b: Block): Block = 
      val (rewritten, syms) = rewriteBms(b, ctx)
      val pre = syms.foldLeft(blockBuilder):
        case (blk, (bms, local)) =>
          val initial = blk.assign(local, createCall(bms, ctx))
          ctx.defns(bms) match
            case c: ClsLikeDefn => initial.assignFieldN(local.asPath, Tree.Ident("class"), bms.asPath)
            case _ => initial
      
      val remaining = rewritten match
        case Assign(lhs: InnerSymbol, rhs, rest) => ctx.getIsymPath(lhs) match
          case Some(value) if !belongsToCtor(lhs) => 
            Assign(value, applyResult(rhs), applyBlock(rest))
          case _ => super.applyBlock(rewritten)

        case Assign(t: TermSymbol, rhs, rest) if t.owner.isDefined =>
          ctx.getIsymPath(t.owner.get) match
            case Some(value) if !belongsToCtor(t.owner.get) =>
              AssignField(value.asPath, t.id, applyResult(rhs), applyBlock(rest))(N)
            case _ => super.applyBlock(rewritten)
        
        case Assign(lhs, rhs, rest) => ctx.getLocalCaptureSym(lhs) match
          case Some((captureSym, _)) => 
            AssignField(ctx.getLocalClosPath(lhs).get, captureSym.id, applyResult(rhs), applyBlock(rest))(N)
          case None => ctx.getLocalPath(lhs) match
            case None => super.applyBlock(rewritten)
            case Some(value) => Assign(value, applyResult(rhs), applyBlock(rest))
        
        case Define(d: Defn, rest: Block) => ctx.modLocals.get(d.sym) match 
          case Some(sym) if !ctx.ignored(d.sym) => ctx.getBmsReqdInfo(d.sym) match
            case Some(_) => 
              blockBuilder
                .assign(sym, Call(d.sym.asPath, getCallArgs(d.sym, ctx))(true, false))
                .rest(applyBlock(rest))
            case None => 
              blockBuilder
                .assign(sym, Call(d.sym.asPath, Nil)(true, false))
                .rest(applyBlock(rest))
          case _ => ctx.replacedDefns.get(d.sym) match
            case Some(value) => Define(value, applyBlock(rest))
            case None => super.applyBlock(rewritten)
          
        case _ => super.applyBlock(rewritten)
      
      pre.rest(remaining)
    
    override def applyPath(p: Path): Path = 
      p match
      // These two cases rewrites `this.whatever` when referencing an outer class's fields.
      case Value.Ref(l: InnerSymbol) =>
        ctx.getIsymPath(l) match
        case Some(value) if !belongsToCtor(l) => Value.Ref(value)
        case _ => super.applyPath(p)
      case Value.Ref(t: TermSymbol) if t.owner.isDefined =>
        ctx.getIsymPath(t.owner.get) match
          case Some(value) if !belongsToCtor(t.owner.get) => Select(value.asPath, t.id)(N)
          case _ => super.applyPath(p)
      
      // Rewrites this.className.class to reference the top-level definition
      case s @ Select(RefOfBms(l), Tree.Ident("class")) if !ctx.ignored(l) && ctx.isRelevant(l) =>
        // this class will be lifted, rewrite the ref to strip it of `Select`
        Select(Value.Ref(l), Tree.Ident("class"))(s.symbol)

      // For objects inside classes: When an object is nested inside a class, its defn will be
      // replaced by a symbol, to which the object instance is assigned. This rewrites references
      // from the objects BlockMemberSymbol to that new symbol.
      case s @ Select(qual, ident) => 
        s.symbol.flatMap(ctx.getLocalPath) match
        case Some(value: MemberSymbol[?]) => Select(qual, Tree.Ident(value.nme))(S(value))
        case _ => super.applyPath(p) 

      // This is to rewrite references to classes that are not lifted (when their BlockMemberSymbol
      // reference is passed as function parameters).
      case RefOfBms(l) if ctx.ignored(l) && ctx.isRelevant(l) => ctx.getIgnoredBmsPath(l) match
        case Some(value) => value
        case None => super.applyPath(p)
      
      // This rewrites naked references to locals. If a function is in a capture, then we select that value
      // from the capture; otherwise, we see if that local is passed directly as a parameter to this defn.
      case Value.Ref(l) => ctx.getLocalCaptureSym(l) match
        case Some((captureSym, _)) => 
          Select(ctx.getLocalClosPath(l).get, captureSym.id)(N)
        case None => ctx.getLocalPath(l) match
          case Some(value) => Value.Ref(value)
          case None => super.applyPath(p)
      case _ => super.applyPath(p)

  def getCallArgs(sym: BlockMemberSymbol, ctx: LifterCtx) =
    val info = ctx.getBmsReqdInfo(sym).get
    val localsArgs = info.reqdVars.map(s => ctx.getLocalPath(s).get.asPath.asArg)
    val capturesArgs = info.reqdCaptures.map(ctx.getCapturePath(_).get.asArg)
    val iSymArgs = info.reqdInnerSyms.map(ctx.getIsymPath(_).get.asPath.asArg)
    val bmsArgs = info.reqdBms.map(ctx.getIgnoredBmsPath(_).get.asArg)
    bmsArgs ++ iSymArgs ++ localsArgs ++ capturesArgs
  
  def createCall(sym: BlockMemberSymbol, ctx: LifterCtx): Call =
    val info = ctx.getBmsReqdInfo(sym).get
    val callSym = info.fakeCtorBms match
      case Some(v) => v
      case None => sym
    Call(callSym.asPath, getCallArgs(sym, ctx))(false, false)

  // deals with creating parameter lists
  def liftOutDefnCont(base: Defn, d: Defn, ctx: LifterCtx): Lifted[Defn] = ctx.getBmsReqdInfo(d.sym) match
    case N => d match
      case f: FunDefn => liftDefnsInFn(f, ctx)
      case c: ClsLikeDefn => liftDefnsInCls(c, ctx)
      case _ => Lifted(d, Nil)
    case S(LiftedInfo(includedCaptures, includedLocals, clsCaptures, reqdBms, fakeCtorBms, singleCallBms)) =>
      val createSym = d match
        case d: ClsLikeDefn =>
          // due to the possibility of capturing a TempSymbol in HandlerLowering, it is necessary to generate a discriminator
          val fresh = FreshInt()
          (nme: String) =>
            val id = fresh.make
            (
              VarSymbol(Tree.Ident(nme + "$" + id)),
              TermSymbol(syntax.ParamBind, S(d.isym), Tree.Ident(nme + "$" + id))
            )
        case _ => (nme: String) =>
          val vsym = VarSymbol(Tree.Ident(nme))
          (vsym, vsym)
      
      val capturesSymbols = includedCaptures.map: sym =>
        (sym, createSym(sym.nme + "$capture"))

      val localsSymbols = includedLocals.map: sym =>
        (sym, createSym(sym.nme))

      val isymSymbols = clsCaptures.map: sym =>
        (sym, createSym(sym.nme + "$instance"))

      val bmsSymbols = reqdBms.map: sym =>
        (sym, createSym(sym.nme + "$member"))

      val extraParamsCaptures = capturesSymbols.map: // parameter list
        case (d, (sym, _)) => Param(FldFlags.empty, sym, None)
      val newCapturePaths = capturesSymbols.map: // mapping from sym to param symbol
          case (d, (_, sym)) => d -> sym.asPath
        .toMap

      val extraParamsLocals = localsSymbols.map: // parameter list
        case (d, (sym, _)) => Param(FldFlags.empty, sym, None)
      val newLocalsPaths = localsSymbols.map: // mapping from sym to param symbol
          case (d, (_, sym)) => d -> sym
        .toMap

      val extraParamsIsyms = isymSymbols.map: // parameter list
        case (d, (sym, _)) => Param(FldFlags.empty, sym, None)
      val newIsymPaths = isymSymbols.map: // mapping from sym to param symbol
          case (d, (_, sym)) => d -> sym
        .toMap

      val extraParamsBms = bmsSymbols.map: // parameter list
        case (d, (sym, _)) => Param(FldFlags.empty, sym, None)
      val newBmsPaths = bmsSymbols.map: // mapping from sym to param symbol
          case (d, (_, sym)) => d -> sym.asPath
        .toMap

      val extraParams = extraParamsBms ++ extraParamsIsyms ++ extraParamsLocals ++ extraParamsCaptures

      val newCtx = ctx
        .replCapturePaths(newCapturePaths)
        .replLocalPaths(newLocalsPaths)
        .addIsymPaths(newIsymPaths)
        .replIgnoredBmsPaths(newBmsPaths)

      d match
        case f: FunDefn =>
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
        case c: ClsLikeDefn if !modOrObj(c) =>
          val newDef = c.copy(
            owner = N, auxParams = c.auxParams.appended(PlainParamList(extraParams))
          )
          val Lifted(lifted, extras) = liftDefnsInCls(newDef, newCtx)

          val bms = fakeCtorBms.get

          // create the fake ctor here
          inline def mapParams(ps: ParamList) = ps.params.map(p => VarSymbol(p.sym.id))

          val paramSyms = c.paramsOpt.map(mapParams)
          val auxSyms = c.auxParams.map(mapParams)
          val extraSyms = extraParams.map(p => VarSymbol(p.sym.id))

          val paramArgs = paramSyms.getOrElse(Nil).map(_.asPath)

          inline def toPaths(l: List[Local]) = l.map(_.asPath)
          
          var curSym = TempSymbol(None, "tmp")
          val inst = Instantiate(Select(c.sym.asPath, Tree.Ident("class"))(N), paramArgs)
          var acc = blk => Assign(curSym, inst, blk)
          for ps <- auxSyms do
            val call = Call(curSym.asPath, ps.map(_.asPath.asArg))(true, false)
            curSym = TempSymbol(None, "tmp")
            acc = blk => acc(Assign(curSym, call, blk))
          val bod = acc(Return(Call(curSym.asPath, extraSyms.map(_.asPath.asArg))(true, false), false))

          inline def toPlist(ls: List[VarSymbol]) = PlainParamList(ls.map(s => Param(FldFlags.empty, s, N)))

          val paramPlist = paramSyms.map(toPlist)
          val auxPlist = auxSyms.map(toPlist)
          val extraPlist = toPlist(extraSyms)

          val plist = paramPlist match
            case None => extraPlist :: PlainParamList(Nil) :: auxPlist
            case Some(value) => extraPlist :: value :: auxPlist

          val fakeCtorDefn = FunDefn(
            None, bms, plist, bod
          )

          val paramSym2 = paramSyms.getOrElse(Nil)
          val auxSym2 = auxSyms.flatMap(l => l)
          val allSymsMp = (paramSym2 ++ auxSym2 ++ extraSyms).map(s => s -> VarSymbol(s.id)).toMap
          val subst = new SymbolSubst():
            override def mapVarSym(s: VarSymbol): VarSymbol = allSymsMp.get(s) match
              case None => s
              case Some(value) => value

          val headParams = paramPlist match
            case None => extraPlist
            case Some(value) => ParamList(value.flags, extraPlist.params ++ value.params, value.restParam)

          val auxCtorDefn_ = FunDefn(None, singleCallBms, headParams :: auxPlist, bod)
          val auxCtorDefn = BlockTransformer(subst).applyFunDefn(auxCtorDefn_)
          
          Lifted(lifted, extras ::: (fakeCtorDefn :: auxCtorDefn :: Nil))
        case c: ClsLikeDefn if modOrObj(c) => // module or object
          // force it to be a class
          val newK = c.k match
            case syntax.Mod => syntax.Mod
            case syntax.Obj => syntax.Cls
            case _ => wat("unreachable", c.k)
          
          val newDef = c.copy(
            k = newK, paramsOpt = N,
            owner = N, auxParams = PlainParamList(extraParams) :: Nil
          )
          liftDefnsInCls(newDef, newCtx)

        case _ => Lifted(d, Nil)
  
  def liftDefnsInCls(c: ClsLikeDefn, ctx: LifterCtx): Lifted[ClsLikeDefn] =
    val ctxx = if c.k is syntax.Mod then ctx.inModule(c) else ctx
    
    val (preCtor, preCtorDefns) = c.preCtor.floatOut(ctxx)
    val (ctor, ctorDefns) = c.ctor.floatOut(ctxx)

    val allCtorDefns = preCtorDefns ++ ctorDefns
    val (ctorIgnored, ctorIncluded) = allCtorDefns.partition(d => ctxx.ignored(d.sym))

    val nestedClsPaths: Map[Local, Local] = ctorIncluded.map:
        case c: ClsLikeDefn if modOrObj(c) => ctxx.modLocals.get(c.sym) match
          case Some(sym) => S(c.sym -> sym)
          case _ => S(c.sym -> c.sym)
        case _ => None
      .collect:
        case Some(x) => x
      .toMap
    
    val newCtx_ = ctxx
      .addLocalPaths(nestedClsPaths)
      .addLocalPaths(getVars(c).map(s => s -> s).toMap)
      .addIgnoredBmsPaths(ctorIgnored.map(d => d.sym -> Select(c.isym.asPath, Tree.Ident(d.sym.nme))(S(d.sym))).toMap)

    val newCtx = c.k match
      case syntax.Mod if !ctx.ignored(c.sym) => newCtx_
      case _ => newCtx_.addIsymPath(c.isym, c.isym)
    
    val ctorDefnsLifted = ctorIncluded.flatMap: defn =>
      val Lifted(liftedDefn, extraDefns) = liftOutDefnCont(c, defn, newCtx.flushModules)
      liftedDefn :: extraDefns
    
    val ctorIgnoredLift = ctorIgnored.map: defn =>
      liftOutDefnCont(c, defn, newCtx)
      
    val ctorIgnoredExtra = ctorIgnoredLift.flatMap(_.extraDefns)
    val ctorIgnoredRewrite = ctorIgnoredLift.map: lifted =>
        lifted.liftedDefn.sym -> lifted.liftedDefn
      .toMap
    
    val replacedDefnsCtx = newCtx.addreplacedDefns(ctorIgnoredRewrite)
    val rewriter = BlockRewriter(S(c), replacedDefnsCtx)
    val newPreCtor = rewriter.applyBlock(preCtor)
    val newCtor = rewriter.applyBlock(ctor)
    
    
    val fLifted = c.methods.map(liftDefnsInFn(_, newCtx))
    val methods = fLifted.collect:
      case Lifted(liftedDefn, extraDefns) => liftedDefn
    val fExtra = fLifted.flatMap:
      case Lifted(liftedDefn, extraDefns) => extraDefns

    val extras = (ctorDefnsLifted ++ fExtra ++ ctorIgnoredExtra).map:
      case f: FunDefn => f.copy(owner = N)
      case c: ClsLikeDefn => c.copy(owner = N)
      case d => d

    def rewriteExtends(p: Path): Path = p match
      case RefOfBms(b) if !ctx.ignored(b) && ctx.isRelevant(b) =>
        // we may need to add `class` in case the lifting added extra params
        if ctxx.getBmsReqdInfo(b).isDefined then Select(b.asPath, Tree.Ident("class"))(N)
        else b.asPath
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
    )
    
    Lifted(newDef, extras)

  def liftDefnsInFn(f: FunDefn, ctx: LifterCtx): Lifted[FunDefn] =
    val (captureCls, varsMap, varsList) = createCaptureCls(f, ctx)
    
    val (blk, nested) = f.body.floatOut(ctx)

    val (ignored, included) = nested.partition(d => ctx.ignored(d.sym))

    val modPaths: Map[Local, Local] = nested.map:
        case c: ClsLikeDefn if modOrObj(c) => ctx.modLocals.get(c.sym) match
          case Some(sym) => S(c.sym -> sym)
          case _ => S(c.sym -> c.sym)
        case _ => None
      .collect:
        case Some(x) => x
      .toMap

    val thisVars = ctx.usedLocals(f.sym)
    // add the mapping from this function's locals to the capture's symbols and the capture path
    val captureSym = FlowSymbol("capture")
    val captureCtx = ctx
      .addLocalCaptureSyms(varsMap) // how to access locals via. the capture class from now on
      .addCapturePath(f.sym, captureSym.asPath) // the path to this function's capture
      .addLocalPaths((thisVars.vars.toSet -- thisVars.reqCapture).map(s => s -> s).toMap)
      .addLocalPaths(modPaths)
      .addIgnoredBmsPaths(ignored.map(d => d.sym -> d.sym.asPath).toMap)
    val nestedCtx = captureCtx.addFnLocals(captureCtx.usedLocals(f.sym))

    // lift out the nested defns
    val nestedLifted = included.map(liftOutDefnCont(f, _, nestedCtx.flushModules))
    val ignoredLifted = ignored.map(liftOutDefnCont(f, _, nestedCtx))
    val ignoredExtra = ignoredLifted.flatMap(_.extraDefns)
    val newDefns = ignoredExtra ++ nestedLifted.flatMap:
      case Lifted(liftedDefn, extraDefns) => liftedDefn :: extraDefns
      
    val ignoredRewrite = ignoredLifted.map: lifted =>
        lifted.liftedDefn.sym -> lifted.liftedDefn
      .toMap

    val transformed = BlockRewriter(N, captureCtx.addreplacedDefns(ignoredRewrite)).applyBlock(blk)

    if thisVars.reqCapture.size == 0 then
      Lifted(FunDefn(f.owner, f.sym, f.params, transformed), newDefns)
    else
      // move the function's parameters to the capture
      val paramsSet = f.params.flatMap(_.paramSyms)
      val paramsList = varsList.map: s =>
        if paramsSet.contains(s) then s.asPath else Value.Lit(Tree.UnitLit(true))
      // moved when the capture is instantiated
      val bod = blockBuilder
        .assign(captureSym, Instantiate(captureCls.sym.asPath, paramsList))
        .rest(transformed)
      Lifted(FunDefn(f.owner, f.sym, f.params, bod), captureCls :: newDefns)

  end liftDefnsInFn

  // top-level
  def transform(b: Block) =
    // this is already done once in the lowering, but the handler lowering adds lambdas currently
    // so we need to desugar them again
    val blk = LambdaRewriter.desugar(b)

    val analyzer = UsedVarAnalyzer(blk, handlerPaths)
    val ctx = LifterCtx
      .withLocals(analyzer.findUsedLocals)
      .withDefns(analyzer.defnsMap)
      .withNestedDefns(analyzer.nestedDefns)
      .withAccesses(analyzer.accessMap)
      .withInScopes(analyzer.inScopeDefns)

    val walker1 = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(d, rest) =>
          val (unliftable, modules, objects) = createMetadata(d, ctx)

          val modLocals = (modules ++ objects).map: c =>
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
            .withModLocals(modLocals)
          
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
