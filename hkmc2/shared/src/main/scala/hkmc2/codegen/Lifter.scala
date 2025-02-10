package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.Tree
import hkmc2.codegen.llir.FreshInt

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.LinkedHashMap
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import hkmc2.syntax.Cls
import hkmc2.syntax.Mod
import hkmc2.syntax.Obj
import hkmc2.syntax.Pat

// TODO: modules not working

object Lifter:
  /**
    * Describes the free variables of a function that have been accessed by nested definitions.
    * @param vars The free variables that are accessed by nested classes/functions.
    * @param reqCapture The free variables that must be captured using a heap-allocated object.
    */
  case class FreeVars(vars: Set[Local], reqCapture: Set[Local]):
    def ++(that: FreeVars) = FreeVars(vars ++ that.vars, reqCapture ++ that.reqCapture)
  object FreeVars:
    val empty = FreeVars(Set.empty, Set.empty)

  /**
    * Describes the free variables of a function that have been accessed by nested definitions.
    * @param mp The map from functions' `BlockMemberSymbol`s to their accessed variables.
    */
  class UsedLocalsMap(val mp: Map[BlockMemberSymbol, FreeVars]):
    def apply(f: BlockMemberSymbol) = mp(f)
    private lazy val inverse = mp.flatMap:
      case fn -> vars => vars.vars.map(v => v -> fn)
    // gets the function to which a local belongs
    def lookup(l: Local) = inverse.get(l)

  object AccessInfo:
    val empty = AccessInfo(Set.empty, Set.empty, Set.empty)

  /**
    * Describes previously defined locals and definitions which could possibly be accessed or mutated by a definition.
    *
    * @param accessed Previously defined locals which could possibly be accessed or mutated.
    * @param mutated Such locals which could also be mutated by this definition.
    * @param refdDefns Previously defined definitions which could possibly be used by this definition.
    */
  case class AccessInfo(
    accessed: Set[Local], 
    mutated: Set[Local], 
    refdDefns: Set[BlockMemberSymbol]):
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
    def addAccess(l: Local) = this.copy(accessed = accessed + l)
    def addMutated(l: Local) = this.copy(accessed = accessed + l, mutated = mutated + l)
    def addRefdDefn(l: BlockMemberSymbol) = this.copy(refdDefns = refdDefns + l)

  def getVars(d: Defn)(using state: State): Set[Local] = d match
    case f: FunDefn =>
      (f.body.definedVars ++ f.params.flatMap(_.paramSyms)).collect:
        case s: FlowSymbol if !(s is state.runtimeSymbol) => s
    case c: ClsLikeDefn =>
      (c.preCtor.definedVars ++ c.ctor.definedVars).collect:
        case s: FlowSymbol if !(s is state.runtimeSymbol) => s
    case _ => Set.empty

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
class Lifter(using State, Raise):
  import Lifter.*

  /**
    * The context of the class lifter. One can create an empty context using `Lifter.empty`.
    * 
    * @param usedLocals Describes the locals belonging to each function that are accessed/mutated by nested definitions.
    * @param accessInfo Which previously defined variables/definitions could be accessed/modified by a particular definition, 
    * possibly through calls to other functions or by constructing a class.
    * @param ignoredDefns The definitions which must not be lifted.
    * @param inScopeDefns Definitions which are in scope to another definition (excluding itself and its nested definitions).
    * @param modules The modules in the block to be lifted.
    * @param localCaptureSyms The symbols in a capture corresponding to a particular local
    * @param prevFnLocals Locals belonging to function definitions that have already been traversed
    * @param prevClsDefns Class definitions that have already been traversed
    * @param capturePaths The path to access a particular function's capture in the local scope
    * @param bmsReqdInfo The (mutable) captures and (immutable) local variables each function requires
    * @param ignoredBmsPaths The path to access a particular BlockMemberSymbol (for definitions which could not be lifted)
    * @param localPaths The path to access a particular local (possibly belonging to a previous function) in the current scope
    * @param iSymPaths The path to access a particular `innerSymbol` (possibly belonging to a previous class) in the current scope
    */
  case class LifterCtx(
    val defns: Map[BlockMemberSymbol, Defn] = Map.empty,
    val usedLocals: UsedLocalsMap = UsedLocalsMap(Map.empty),
    val accessInfo: Map[BlockMemberSymbol, AccessInfo] = Map.empty,
    val ignoredDefns: Set[BlockMemberSymbol] = Set.empty,
    val inScopeDefns: Map[BlockMemberSymbol, Set[BlockMemberSymbol]] = Map.empty,
    val modules: Set[BlockMemberSymbol] = Set.empty,
    val localCaptureSyms: Map[Local, LocalSymbol & NamedSymbol] = Map.empty,
    val prevFnLocals: FreeVars = FreeVars.empty,
    val prevClsDefns: List[ClsLikeDefn] = Nil,
    val capturePaths: Map[BlockMemberSymbol, Path] = Map.empty,
    val bmsReqdInfo: Map[BlockMemberSymbol, LiftedInfo] = Map.empty, // required captures
    val ignoredBmsPaths: Map[BlockMemberSymbol, Local] = Map.empty,
    val localPaths: Map[Local, Local] = Map.empty,
    val isymPaths: Map[InnerSymbol, Local] = Map.empty,
  ):
    // gets the function to which a local belongs
    def lookup(l: Local) = usedLocals.lookup(l)
    // the path to access the capture of a particular function
    def getCapturePath(b: BlockMemberSymbol) = capturePaths.get(b)
    // the path to access the capture of the function that a local belongs to
    def getLocalClosPath(l: Local) = lookup(l).flatMap(capturePaths.get(_))
    // the symbol in the capture corresponding to a particular local
    def getLocalCaptureSym(l: Local) = localCaptureSyms.get(l)
    // how to access a variable in the local scope
    def getLocalPath(l: Local) = localPaths.get(l)
    def getIsymPath(l: InnerSymbol) = isymPaths.get(l)
    def getIgnoredBmsPath(b: BlockMemberSymbol) = ignoredBmsPaths.get(b)
    def ignored(b: BlockMemberSymbol) = ignoredDefns.contains(b)
    def isModOrObj(b: BlockMemberSymbol) = modules.contains(b)
    def getAccesses(sym: BlockMemberSymbol) = accessInfo(sym)
    
    def addIgnored(defns: Set[BlockMemberSymbol]) = copy(ignoredDefns = ignoredDefns ++ defns)
    def addModules(mods: Set[BlockMemberSymbol]) = copy(modules = mods ++ modules)
    def withDefns(mp: Map[BlockMemberSymbol, Defn]) = copy(defns = mp)
    def withAccesses(mp: Map[BlockMemberSymbol, AccessInfo]) = copy(accessInfo = mp)
    def withInScopes(mp: Map[BlockMemberSymbol, Set[BlockMemberSymbol]]) = copy(inScopeDefns = mp)
    def addFnLocals(f: FreeVars) = copy(prevFnLocals = prevFnLocals ++ f)
    def addClsDefn(c: ClsLikeDefn) = copy(prevClsDefns = c :: prevClsDefns)
    def addLocalCaptureSyms(m: Map[Local, LocalSymbol & NamedSymbol]) = copy(localCaptureSyms = localCaptureSyms ++ m)
    def getBmsReqdInfo(sym: BlockMemberSymbol) = bmsReqdInfo.get(sym)
    def replCapturePaths(paths: Map[BlockMemberSymbol, Path]) = copy(capturePaths = paths)
    def addCapturePath(src: BlockMemberSymbol, path: Path) = copy(capturePaths = capturePaths + (src -> path))
    def addBmsReqdInfo(mp: Map[BlockMemberSymbol, LiftedInfo]) = copy(bmsReqdInfo = bmsReqdInfo ++ mp)
    def replLocalPaths(m: Map[Local, Local]) = copy(localPaths = m)
    def replIgnoredBmsPaths(m: Map[BlockMemberSymbol, Local]) = copy(ignoredBmsPaths = m)
    def replIsymPaths(m: Map[InnerSymbol, Local]) = copy(isymPaths = m)
    def addLocalPaths(m: Map[Local, Local]) = copy(localPaths = localPaths ++ m)
    def addLocalPath(target: Local, path: Local) = copy(localPaths = localPaths + (target -> path))
    def addIgnoredBmsPaths(m: Map[BlockMemberSymbol, Local]) = copy(ignoredBmsPaths = ignoredBmsPaths ++ m)
    def addIsymPath(isym: InnerSymbol, l: Local) = copy(isymPaths = isymPaths + (isym -> l))
  
  object LifterCtx:
    def empty = LifterCtx()
    def withLocals(u: UsedLocalsMap) = empty.copy(usedLocals = u)
  
  /**
    * Creates a capture class for a function consisting of its mutable (and possibly immutable) local variables.
    * @param f The function to create the capture class for.
    * @param ctx The lifter context. Determines which variables will be captured.
    * @return The triple (defn, varsMap, varsList), where `defn` is the capture class's definition,
    * `varsMap` maps the function's locals to the correpsonding `VarSymbol` in the class, and
    * `varsList` specifies the order of these variables in the class's constructor. 
    */
  def createCaptureCls(f: FunDefn, ctx: LifterCtx) =
    val nme = f.sym.nme + "$capture"

    val clsSym = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident(nme)
    )

    val FreeVars(_, cap) = ctx.usedLocals(f.sym)

    val fresh = FreshInt()

    val varsMap: Map[Local, TermSymbol] = cap.map: s =>
      val id = fresh.make
      s -> TermSymbol(syntax.ParamBind, S(clsSym), Tree.Ident(s.nme + id + "$"))
    .toMap

    val varsList = cap.toList
    
    val defn = ClsLikeDefn(
      None, clsSym, BlockMemberSymbol(nme, Nil), 
      syntax.Cls,
      S(PlainParamList(varsList.map(s => Param(FldFlags.empty, varsMap(s), None)))),
      Nil, None, Nil, Nil, Nil, End(), End()
    )

    (defn, varsMap, varsList)

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
      case _ => c.sym // unreachable   

    innerSymCache.get(sym) match 
    case Some(value) => value
    case None =>
      val ret: Set[Local] = c.freeVars.collect:
        case s: InnerSymbol => s
        case t: TermSymbol if t.owner.isDefined => t.owner.get
      innerSymCache.addOne(sym -> ret)
      ret

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
    * Gets the immutable local variables of a function that need to captured by a definition being lifted. 
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
    val modLocal: Opt[Local] // for modules
  )

  case class Lifted[+T <: Defn](
    val liftedDefn: T,
    val extraDefns: List[Defn],
  )

  // d is a top-level definition
  // returns (unliftable classes, modules)
  def createMetadata(d: Defn, ctx: LifterCtx): (Set[BlockMemberSymbol], Set[BlockMemberSymbol]) =
    var clsSymToBms: Map[Local, BlockMemberSymbol] = Map.empty
    var modules: Set[BlockMemberSymbol] = Set.empty
    
    val walker = new BlockTransformer(SymbolSubst()):
      override def applyDefn(defn: Defn): Defn = 
        defn match
          case c: ClsLikeDefn => 
            clsSymToBms += c.isym -> c.sym
            if modOrObj(c) then modules += c.sym
            if c.k is syntax.Mod then
              raise(WarningReport(
                msg"Modules are not yet properly lifted and will break." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
          case _ => ()
        super.applyDefn(defn)
    walker.applyDefn(d)

    val clsSyms = clsSymToBms.values.toSet
    
    var unliftable: Set[BlockMemberSymbol] = Set.empty
    val walker2 = new BlockTransformer(SymbolSubst()):
      override def applyCase(cse: Case): Case = 
        cse match
          case Case.Cls(cls, path) => clsSymToBms.get(cls) match
            case None => ()
            case Some(value) =>
              raise(WarningReport(
                msg"Cannot yet lift the class/module `${value.nme}` as it is used in an instance check." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
              unliftable += value
          case _ => ()
        cse
      
      override def applyResult(r: Result): Result = r match
        case Call(Value.Ref(_: BlockMemberSymbol), args) =>
          args.map(applyArg)
          r
        case Instantiate(InstSel(_), args) =>
          args.map(applyPath)
          r
        
        case _ => super.applyResult(r)

      override def applyValue(v: Value): Value = v match
        case RefOfBms(l) if clsSyms.contains(l) && !modOrObj(ctx.defns(l)) =>
          raise(WarningReport(
            msg"Cannot yet lift the class `${l.nme}` as it is used as a first-class class." -> N :: Nil,
            N, Diagnostic.Source.Compilation
          ))
          unliftable += l
          v
        case _ => super.applyValue(v)
    walker2.applyDefn(d)
    
    (unliftable, modules)

  extension (b: Block)
    private def floatOut(ctx: LifterCtx) = 
      b.floatOutDefns(preserve = defn => ctx.isModOrObj(defn.sym) || ctx.ignored(defn.sym))
      

  def createLiftInfoCont(d: Defn, parentCls: Opt[ClsLikeDefn], ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val AccessInfo(accessed, mutated, refdDefns) = ctx.getAccesses(d.sym)

    val inScopeRefs = refdDefns.intersect(ctx.inScopeDefns(d.sym))

    val includedCaptures = ctx.prevFnLocals.reqCapture
      .intersect(accessed)
      .map(sym => ctx.lookup(sym).get)
      .toList.sortBy(_.uid)

    val refMod = inScopeRefs.intersect(ctx.modules)
    val includedLocals = ((accessed -- ctx.prevFnLocals.reqCapture) ++ refMod).toList.sortBy(_.uid)
    val clsCaptures: List[InnerSymbol] = ctx.prevClsDefns.map(_.isym)
    val refBms = inScopeRefs.intersect(ctx.ignoredDefns).toList.sortBy(_.uid)

    if ctx.ignored(d.sym) || 
      (includedCaptures.isEmpty && includedLocals.isEmpty && clsCaptures.isEmpty && refBms.isEmpty) then 
      d match
        case f: FunDefn => 
          createLiftInfoFn(f, ctx)
        case c: ClsLikeDefn => 
          createLiftInfoCls(c, ctx)
        case _ => Map.empty
    else
      val modLocal = d match
        case c: ClsLikeDefn if modOrObj(c) => parentCls match
          case None =>  S(VarSymbol(Tree.Ident(c.sym.nme + "$")))
          case Some(value) =>  S(TermSymbol(syntax.ImmutVal, S(value.isym), Tree.Ident(c.sym.nme + "$")))
        case _ => N

      val fakeCtorBms = d match
        case c: ClsLikeDefn if !modLocal.isDefined => S(BlockMemberSymbol(d.sym.nme + "$ctor", Nil))
        case _ => N

      val singleCallBms = BlockMemberSymbol(d.sym.nme + "$", Nil)

      val info = LiftedInfo(
        includedCaptures, includedLocals, clsCaptures,
        refBms, fakeCtorBms, singleCallBms, modLocal
      )
      
      d match
        case f: FunDefn => 
          createLiftInfoFn(f, ctx) + (d.sym -> info)
        case c: ClsLikeDefn => 
          createLiftInfoCls(c, ctx) + (d.sym -> info)
        case _ => Map.empty
  
  def createLiftInfoFn(f: FunDefn, ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val (_, defns) = f.body.floatOut(ctx)
    defns.flatMap(createLiftInfoCont(_, N, ctx.addFnLocals(ctx.usedLocals(f.sym)))).toMap

  def createLiftInfoCls(c: ClsLikeDefn, ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val defns = c.preCtor.floatOut(ctx)._2 ++ c.ctor.floatOut(ctx)._2
    val newCtx = ctx.addClsDefn(c)
    defns.flatMap(f => createLiftInfoCont(f, S(c), newCtx)).toMap
      ++ c.methods.flatMap(f => createLiftInfoFn(f, newCtx))  

  def rewriteBlk(b: Block, ctorCls: Opt[ClsLikeDefn], ctx: LifterCtx): Block =
    // replaces references to BlockMemberSymbols as needed with fresh variables, and
    // returns the mapping from the symbol to the required variable. When possible,
    // it also directly rewrites Results.
    def rewriteBms(b: Block, ctx: LifterCtx) =
      val syms: LinkedHashMap[BlockMemberSymbol, Local] = LinkedHashMap.empty

      val walker = new BlockTransformerNoRec(SymbolSubst()):
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
          case RefOfBms(l) => ctx.getIgnoredBmsPath(l) match
            case Some(value) => Value.Ref(value)
            case None => super.applyPath(p)
          
          case _ => super.applyPath(p)
      (walker.applyBlock(b), syms.toList)
    end rewriteBms
        
    def belongsToCtor(l: Symbol) = 
      ctorCls.match
      case None => false
      case Some(value) => 
        value.isym === l
    
    // rewrites references to variables
    val transformer1 = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Assign(lhs: InnerSymbol, rhs, rest) => ctx.getIsymPath(lhs) match
          case Some(value) if !belongsToCtor(value) => Assign(value, applyResult(rhs), applyBlock(rest))
          case _ => super.applyBlock(b)

        case Assign(t: TermSymbol, rhs, rest) if t.owner.isDefined =>
          ctx.getIsymPath(t.owner.get) match
            case Some(value) if !belongsToCtor(value) => 
              AssignField(value.asPath, t.id, applyResult(rhs), applyBlock(rest))(N)
            case _ => super.applyBlock(b)
        
        case Assign(lhs, rhs, rest) => ctx.getLocalCaptureSym(lhs) match
          case Some(captureSym) => 
            AssignField(ctx.getLocalClosPath(lhs).get, captureSym.id, applyResult(rhs), applyBlock(rest))(N)
          case None => ctx.getLocalPath(lhs) match
            case None => super.applyBlock(b)
            case Some(value) => Assign(value, applyResult(rhs), applyBlock(rest))
        
        case Define(d: Defn, rest: Block) => ctx.getBmsReqdInfo(d.sym) match
          case Some(LiftedInfo(modLocal = S(sym))) =>
            blockBuilder
              .assign(sym, Call(d.sym.asPath, getCallArgs(d.sym, ctx))(true, false))
              .rest(applyBlock(rest))
          case _ => super.applyBlock(b)
        
        
        case _ => super.applyBlock(b)
        
      override def applyPath(p: Path): Path = p match
        case Value.Ref(l: InnerSymbol) => ctx.getIsymPath(l) match
          case Some(value) if !belongsToCtor(value) => Value.Ref(value)
          case _ => super.applyPath(p)
        case Value.Ref(t: TermSymbol) if t.owner.isDefined =>
          ctx.getIsymPath(t.owner.get) match
            case Some(value) if !belongsToCtor(value) => Select(value.asPath, t.id)(N)
            case _ => super.applyPath(p)
        case s @ Select(qual, ident) => 
          s.symbol.flatMap(ctx.getLocalPath) match
          case Some(value: MemberSymbol[?]) => Select(qual, Tree.Ident(value.nme))(S(value))
          case _ => super.applyPath(p) 
        case Value.Ref(l) => ctx.getLocalCaptureSym(l) match
          case Some(captureSym) => 
            Select(ctx.getLocalClosPath(l).get, captureSym.id)(N)
          case None => ctx.getLocalPath(l) match
            case Some(value) => Value.Ref(value)
            case None => super.applyPath(p)
        case _ => super.applyPath(p)

    // rewrites references to block member symbols
    val transformer2 = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block =
        val (rewriten, syms) = rewriteBms(b, ctx)
        val pre = syms.foldLeft(blockBuilder):
          case (blk, (bms, local)) => 
            val initial = blk.assign(local, createCall(bms, ctx))
            ctx.defns(bms) match
              case c: ClsLikeDefn => initial.assignFieldN(local.asPath, Tree.Ident("class"), bms.asPath)
              case _ => initial
        pre.rest(super.applyBlock(rewriten))

    b |> transformer1.applyBlock |> transformer2.applyBlock

  def getCallArgs(sym: BlockMemberSymbol, ctx: LifterCtx) =
    val info = ctx.getBmsReqdInfo(sym).get
    val localsArgs = info.reqdVars.map(s => ctx.getLocalPath(s).get.asPath.asArg)
    val capturesArgs = info.reqdCaptures.map(ctx.getCapturePath(_).get.asArg)
    val iSymArgs = info.reqdInnerSyms.map(ctx.getIsymPath(_).get.asPath.asArg)
    val bmsArgs = info.reqdBms.map(ctx.getIgnoredBmsPath(_).get.asPath.asArg)
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
    case S(LiftedInfo(includedCaptures, includedLocals, clsCaptures, reqdBms, fakeCtorBms, singleCallBms, modLocal)) =>
      val createSym = d match
        case d: ClsLikeDefn =>
          // due to the possibility of capturing a TempSymbol in HandlerLowering, it is necessary to generate a discriminator
          val fresh = FreshInt()
          (nme: String) =>
            val id = fresh.make
            TermSymbol(syntax.ParamBind, S(d.isym), Tree.Ident(nme + "$" + id))
        case _ => ((nme: String) => VarSymbol(Tree.Ident(nme)))
      
      val capturesSymbols = includedCaptures.map: sym =>
        (sym, createSym(sym.nme + "$capture"))

      val localsSymbols = includedLocals.map: sym =>
        (sym, createSym(sym.nme))

      val isymSymbols = clsCaptures.map: sym =>
        (sym, createSym(sym.nme + "$instance"))

      val bmsSymbols = reqdBms.map: sym =>
        (sym, createSym(sym.nme + "$member"))

      val extraParamsCaptures = capturesSymbols.map: // parameter list
        case (d, sym) => Param(FldFlags.empty, sym, None)
      val newCapturePaths = capturesSymbols.map: // mapping from sym to param symbol
        case (d, sym) => d -> sym.asPath
      .toMap

      val extraParamsLocals = localsSymbols.map: // parameter list
        case (d, sym) => Param(FldFlags.empty, sym, None)
      val newLocalsPaths = localsSymbols.map: // mapping from sym to param symbol
        case (d, sym) => d -> sym
      .toMap

      val extraParamsIsyms = isymSymbols.map: // parameter list
        case (d, sym) => Param(FldFlags.empty, sym, None)
      val newIsymPaths = isymSymbols.map: // mapping from sym to param symbol
        case (d, sym) => d -> sym
      .toMap

      val extraParamsBms = bmsSymbols.map: // parameter list
        case (d, sym) => Param(FldFlags.empty, sym, None)
      val newBmsPaths = bmsSymbols.map: // mapping from sym to param symbol
        case (d, sym) => d -> sym
      .toMap

      val extraParams = extraParamsBms ++ extraParamsIsyms ++ extraParamsLocals ++ extraParamsCaptures

      val newCtx = ctx
        .replCapturePaths(newCapturePaths)
        .replLocalPaths(newLocalsPaths)
        .replIsymPaths(newIsymPaths)
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
            case Mod => syntax.Mod
            case Obj => syntax.Cls
            case _ => c.k // unreachable
          
          val newDef = c.copy(
            k = newK, paramsOpt = N,
            owner = N, auxParams = PlainParamList(extraParams) :: Nil
          )
          liftDefnsInCls(newDef, newCtx)

        case _ => Lifted(d, Nil)
  
  def liftDefnsInCls(c: ClsLikeDefn, ctx: LifterCtx): Lifted[ClsLikeDefn] = 
    val (preCtor, preCtorDefns) = c.preCtor.floatOut(ctx)
    val (ctor, ctorDefns) = c.ctor.floatOut(ctx)

    val allCtorDefns = preCtorDefns ++ ctorDefns
    val (ctorIgnored, ctorIncluded) = allCtorDefns.partition(d => ctx.ignored(d.sym))

    val modPaths: Map[Local, Local] = ctorIncluded.map:
      case c: ClsLikeDefn if modOrObj(c) => ctx.getBmsReqdInfo(c.sym) match
        case Some(LiftedInfo(modLocal = Some(sym))) => S(c.sym -> sym)
        case _ => S(c.sym -> c.sym) 
      case _ => None
    .collect:
      case Some(x) => x
    .toMap
    
    val newCtx = ctx
      .addIsymPath(c.isym, c.isym)
      .addLocalPaths(modPaths)

    val newPreCtor = rewriteBlk(preCtor, S(c), newCtx)
    val newCtor = rewriteBlk(ctor, S(c), newCtx)
    

    val ctorDefnsLifted = ctorIncluded.flatMap: defn =>
      val Lifted(liftedDefn, extraDefns) = liftOutDefnCont(c, defn, newCtx)
      liftedDefn :: extraDefns
    
    val fLifted = c.methods.map(liftDefnsInFn(_, newCtx)) 
    val methods = fLifted.collect:
      case Lifted(liftedDefn, extraDefns) => liftedDefn 
    val fExtra = fLifted.flatMap:
      case Lifted(liftedDefn, extraDefns) => extraDefns

    val extras = (ctorDefnsLifted ++ fExtra).map:
      case f: FunDefn => f.copy(owner = N)
      case c: ClsLikeDefn => c.copy(owner = N) 
      case d => d

    val newDef = c.copy(
      methods = methods,
      preCtor = newPreCtor,
      ctor = newCtor
    )
    
    Lifted(newDef, extras)

  def liftDefnsInFn(f: FunDefn, ctx: LifterCtx): Lifted[FunDefn] =
    val (captureCls, varsMap, varsList) = createCaptureCls(f, ctx)
    
    val (blk, nested) = f.body.floatOut(ctx)

    val (ignored, included) = nested.partition(d => ctx.ignored(d.sym))

    val modPaths: Map[Local, Local] = nested.map:
        case c: ClsLikeDefn if modOrObj(c) => ctx.getBmsReqdInfo(c.sym) match
          case Some(LiftedInfo(modLocal = Some(sym))) => S(c.sym -> sym)
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
      .addIgnoredBmsPaths(ignored.map(d => d.sym -> d.sym).toMap)
    val nestedCtx = captureCtx.addFnLocals(captureCtx.usedLocals(f.sym))

    // lift out the nested defns
    val nestedLifted = included.map(liftOutDefnCont(f, _, nestedCtx))
    val ignoredExtra = ignored.flatMap(liftOutDefnCont(f, _, nestedCtx).extraDefns)
    val newDefns = ignoredExtra ++ nestedLifted.flatMap:
      case Lifted(liftedDefn, extraDefns) => liftedDefn :: extraDefns

    val transformed = rewriteBlk(blk, N, captureCtx)

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

  def desugarLambdas(b: Block) =
    def rewriteOneBlk(b: Block) =
      var lambdasList: List[(BlockMemberSymbol, Value.Lam)] = Nil
      val lambdaRewriter = new BlockTransformerNoRec(SymbolSubst()):
        override def applyValue(v: Value): Value = v match
          case lam: Value.Lam => 
            val sym = BlockMemberSymbol("lambda", Nil)
            lambdasList ::= (sym -> super.applyLam(lam))
            Value.Ref(sym)
          case _ => super.applyValue(v)
      val blk = lambdaRewriter.applyBlock(b)
      (blk, lambdasList)

    val transformer = new BlockTransformer(SymbolSubst()):
      override def applyBlock(b: Block): Block =
        val (newBlk, lambdasList) = rewriteOneBlk(b)
        val lambdaDefns = lambdasList.map:
          case (sym, Value.Lam(params, body)) =>
            FunDefn(None, sym, params :: Nil, body)
        val ret = lambdaDefns.foldLeft(newBlk):
          case (acc, defn) => Define(defn, acc)
        super.applyBlock(ret)
    transformer.applyBlock(b)

  // top-level
  def transform(b: Block) =
    val blk = desugarLambdas(b)
    val analyzer = UsedVarAnalyzer(blk)
    val ctx = LifterCtx
      .withLocals(analyzer.findUsedLocals)
      .withDefns(analyzer.defnsMap)
      .withAccesses(analyzer.accessMap)
      .withInScopes(analyzer.inScopeDefns)
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(d, rest) =>
          val (unliftable, modules) = createMetadata(d, ctx)
          val ctxx = ctx.addIgnored(unliftable).addModules(modules)
          val Lifted(lifted, extra) = d match
            case f: FunDefn => liftDefnsInFn(f, ctxx.addBmsReqdInfo(createLiftInfoFn(f, ctxx)))
            case c: ClsLikeDefn => liftDefnsInCls(c, ctxx.addBmsReqdInfo(createLiftInfoCls(c, ctxx)))
            case _ => return super.applyBlock(b)
          (lifted :: extra).foldLeft(applyBlock(rest))((acc, defn) => Define(defn, acc))
        case _ => super.applyBlock(b)
    walker.applyBlock(blk)

/**
  * Analyzes which variables have been used and mutated by which functions.
  * Also finds which variables can be passed to a capture class without a heap
  * allocation (during class lifting) despite being mutable.
  * 
  * Assumes the input trees have no lambdas.
  */
class UsedVarAnalyzer(b: Block)(using State):
  import Lifter.*

  // the current problem is that we need extra code to find which variables were really defined by a function
  // this may be resolved in the future when the IR gets explicit variable declarations

  private case class DefnMetadata(
    definedLocals: Map[BlockMemberSymbol, Set[Local]], // locals defined explicitly by that function
    defnsMap: Map[BlockMemberSymbol, Defn], // map bms to defn
    existingVars: Map[BlockMemberSymbol, Set[Local]], // variables already existing when that defn is defined
    inScopeDefns: Map[BlockMemberSymbol, Set[BlockMemberSymbol]], // definitions that are in scope
    nestedDefns: Map[BlockMemberSymbol, List[Defn]], // definitions directly nested within another defn (shallow)
  )
  private def createMetadata: DefnMetadata =
    var defnsMap: Map[BlockMemberSymbol, Defn] = Map.empty
    var definedLocals: Map[BlockMemberSymbol, Set[Local]] = Map.empty
    var existingVars: Map[BlockMemberSymbol, Set[Local]] = Map.empty
    var inScopeDefns: Map[BlockMemberSymbol, Set[BlockMemberSymbol]] = Map.empty
    var nestedDefns: Map[BlockMemberSymbol, List[Defn]] = Map.empty

    def createMetadataFn(f: FunDefn, existing: Set[Local], inScope: Set[BlockMemberSymbol]): Unit =
      existingVars += (f.sym -> existing)
      val thisVars = Lifter.getVars(f) -- existing
      val newExisting = existing ++ thisVars

      val thisScopeDefns: List[Defn] = f.body.floatOutDefns()._2

      nestedDefns += f.sym -> thisScopeDefns

      val newInScope = inScope ++ thisScopeDefns.map(_.sym)
      for s <- thisScopeDefns do
        inScopeDefns += s.sym -> (newInScope - s.sym)

      defnsMap += (f.sym -> f)
      definedLocals += (f.sym -> thisVars)

      for d <- thisScopeDefns do createMetadataDefn(d, newExisting, newInScope)
      
      val walker = new BlockTransformerShallow(SymbolSubst()):
        override def applyDefn(defn: Defn): Defn =
          createMetadataDefn(defn, newExisting, inScope)
          defn
      walker.applyBlock(f.body)

    def createMetadataDefn(d: Defn, existing: Set[Local], inScope: Set[BlockMemberSymbol]): Unit =
      d match
      case f: FunDefn => 
        createMetadataFn(f, existing, inScope)
      case c: ClsLikeDefn =>
        createMetadataCls(c, existing, inScope)
      case d => Map.empty

    def createMetadataCls(c: ClsLikeDefn, existing: Set[Local], inScope: Set[BlockMemberSymbol]): Unit =
      existingVars += (c.sym -> existing)
      val thisVars = Lifter.getVars(c) -- existing
      val newExisting = existing ++ thisVars

      val thisScopeDefns: List[Defn] = 
        (c.methods ++ c.preCtor.floatOutDefns()._2 ++ c.ctor.floatOutDefns()._2)

      nestedDefns += c.sym -> thisScopeDefns
      
      val newInScope = inScope ++ thisScopeDefns.map(_.sym)
      for s <- thisScopeDefns do
        inScopeDefns += s.sym -> (newInScope - s.sym)
      
      defnsMap += (c.sym -> c)
      definedLocals += (c.sym -> thisVars)

      for d <- thisScopeDefns do createMetadataDefn(d, newExisting, newInScope)
  
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyDefn(defn: Defn): Defn =
        inScopeDefns += defn.sym -> Set.empty
        createMetadataDefn(defn, b.definedVars, Set.empty)
        defn
    walker.applyBlock(b)
    DefnMetadata(definedLocals, defnsMap, existingVars, inScopeDefns, nestedDefns)

  val DefnMetadata(definedLocals, defnsMap, existingVars, inScopeDefns, nestedDefns) = createMetadata
  
  private val blkMutCache: MutMap[Local, AccessInfo] = MutMap.empty
  private def blkAccessesShallow(b: Block, cacheId: Opt[Local] = N): AccessInfo = 
    cacheId.flatMap(blkMutCache.get) match
    case Some(value) => value
    case None => 
      var accessed: AccessInfo = AccessInfo.empty
      val walker = new BlockTransformerShallow(SymbolSubst()):
        override def applyBlock(b: Block): Block = b match
          case Assign(lhs, rhs, rest) =>
            accessed = accessed.addMutated(lhs)
            applyResult(rhs)
            applyBlock(rest)
          case Label(label, body, rest) =>
            accessed ++= blkAccessesShallow(body, S(label))
            applyBlock(rest)
          case _ => super.applyBlock(b)
        
        override def applyValue(v: Value): Value = v match
          case Value.Ref(_: BuiltinSymbol) => super.applyValue(v)
          case RefOfBms(l) =>
            accessed = accessed.addRefdDefn(l); v
          case Value.Ref(l) =>
            accessed = accessed.addAccess(l); v
          case _ => super.applyValue(v)
      
      walker.applyBlock(b)

      cacheId match
        case None => ()
        case Some(value) => blkMutCache.addOne(value -> accessed)
      
      accessed

  private val accessedCache: MutMap[BlockMemberSymbol, AccessInfo] = MutMap.empty
  
  /**
    * Finds the variables which this definition could possibly mutate, excluding mutations through
    * calls to other functions and, in the case of functions, mutations of its own variables.
    *
    * @param defn The definition to search through.
    * @return The variables which this definition could possibly mutate.
    */
  private def findAccessesShallow(defn: Defn): AccessInfo = accessedCache.get(defn.sym) match
    case Some(value) => value
    case None => 
      val ret = defn match
        case f: FunDefn =>
          val fVars = definedLocals(f.sym)
          blkAccessesShallow(f.body).withoutLocals(fVars)
        case c: ClsLikeDefn =>
          c.methods.foldLeft(blkAccessesShallow(c.preCtor) ++ blkAccessesShallow(c.ctor)): 
            // here, we count the class as "accessing" all its methods (since they could be invoked anywhere)
            case (acc, defn) => acc.addRefdDefn(defn.sym)
        case _: ValDefn => AccessInfo.empty
      accessedCache.addOne(defn.sym -> ret)
      ret

  // MUST be called from a top-level defn
  private def findAccesses(d: Defn): Map[BlockMemberSymbol, AccessInfo] =
    var defns: List[Defn] = Nil
    var definedVarsDeep: Set[Local] = Set.empty

    val walker = new BlockTransformer(SymbolSubst()):
      override def applyFunDefn(f: FunDefn): FunDefn =
        defns +:= f; definedVarsDeep ++= definedLocals(f.sym)
        super.applyFunDefn(f)
      
      override def applyDefn(defn: Defn): Defn = 
        defn match
          case c: ClsLikeDefn => defns +:= c; definedVarsDeep ++= definedLocals(c.sym)
          case _ => 
        super.applyDefn(defn)
    
    walker.applyDefn(d)

    val defnSyms = defns.map(_.sym).toSet
    val accessInfo = defns.map: d =>
      val AccessInfo(accessed, mutated, refdDefns) = findAccessesShallow(d)
      d.sym -> AccessInfo(
        accessed.intersect(definedVarsDeep),
        mutated.intersect(definedVarsDeep),
        refdDefns.intersect(defnSyms)
      )

    val accessInfoMap = accessInfo.toMap

    val edges = 
      for 
        (sym, AccessInfo(_, _, refd)) <- accessInfo
        r <- refd
        if defnSyms.contains(r)
      yield sym -> r
    .toSet

    // (sccs, sccEdges) forms a directed acyclic graph (DAG)
    val algorithms.SccsInfo(sccs, sccEdges, inDegs, outDegs) = algorithms.sccsWithInfo(edges, defnSyms)
    
    // all defns in the same scc must have at least the same accesses as each other
    val base = for (id, scc) <- sccs yield id -> 
      scc.foldLeft(AccessInfo.empty):
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
    yield sym -> (sccAccessInfo(id).intersectLocals(existingVars(sym)))

  private def findAccessesTop =
    var accessMap: Map[BlockMemberSymbol, AccessInfo] = Map.empty
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyDefn(defn: Defn): Defn = defn match
        case _: FunDefn | _: ClsLikeDefn => 
          accessMap ++= findAccesses(defn); defn
        case _ => super.applyDefn(defn)
    walker.applyBlock(b)
    accessMap
  
  val accessMap = findAccessesTop

  // TODO: let declarations inside loops (also broken without class lifting)
  // I'll fix it once it's fixed in the IR since we will have more tools to determine
  // what locals belong to what block.
  private def reqdCaptureLocals(f: FunDefn) =
    var (_, defns) = f.body.floatOutDefns()
    val defnSyms = defns.collect:
      case f: FunDefn => f.sym -> f
      case c: ClsLikeDefn => c.sym -> c
    .toMap

    val thisVars = definedLocals(f.sym)

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
      
      val walker = new BlockTransformerShallow(SymbolSubst()):
        override def applyBlock(b: Block): Block = b match
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
            b
          case Label(label, body, rest) => 
            // for now, if the loop body mutates a variable and that variable is accessed or mutated by a defn,
            // or if it reads a variable that is later mutated by an instance inside the loop,
            // we put it in a capture. this preserves the current semantics of the IR (even though it's incorrect).
            // See the above TODO
            val c @ CaptureInfo(req, read, mut) = rec(body)
            merge(c)
            reqCapture ++= read.intersect(blkAccessesShallow(body, S(label)).mutated)
            reqCapture ++= mut.intersect(body.freeVars)
            applyBlock(rest)
            b
          case Begin(sub, rest) =>
            rec(sub) |> merge
            applyBlock(rest)
            b
          case TryBlock(sub, finallyDo, rest) =>
            // sub and finallyDo could be executed sequentially, so we must merge
            rec(sub) |> merge
            rec(finallyDo) |> merge
            applyBlock(rest)
            b
          case Return(res, false) =>
            applyResult(res)
            hasReader = Set.empty
            hasMutator = Set.empty
            b
          case _ => super.applyBlock(b)

        def handleCalledBms(l: BlockMemberSymbol) = defnSyms.get(l) match
          case None => ()
          case Some(defn) =>
            val AccessInfo(accessed, muted, refd) = accessMap(defn.sym) 
            val muts = muted.intersect(thisVars)
            val reads = defn.freeVars.intersect(thisVars) -- muts
            // this not a naked reference. if it's a ref to a class, this can only ever create once instance
            // so the "one writer" rule applies
            for l <- muts do
              if hasReader.contains(l) || hasMutator.contains(l) || defn.isInstanceOf[FunDefn] then
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
              l <- accessMap(sym).mutated
            do
              reqCapture += l
              hasMutator += l

        override def applyResult(r: Result): Result = r match
          case Call(RefOfBms(l), args) =>
            args.map(super.applyArg(_))
            handleCalledBms(l)
            r
          case Instantiate(InstSel(l), args) =>
            args.map(super.applyPath(_))
            handleCalledBms(l)
            r
          case _ => super.applyResult(r)
        
        override def applyPath(p: Path): Path = p match
          case RefOfBms(l) => 
            defnSyms.get(l) match
            case None => super.applyPath(p)
            case Some(defn) =>
              val isMod = defn match
                case c: ClsLikeDefn => modOrObj(c)
                case _ => false
              if isMod then super.applyPath(p)
              else
                val AccessInfo(accessed, muted, refd) = accessMap(defn.sym) 
                val muts = muted.intersect(thisVars)
                val reads = defn.freeVars.intersect(thisVars) -- muts
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
                  l <- accessMap(sym).mutated
                do
                  reqCapture += l
                  hasMutator += l
              
              p          
          case Value.Ref(l) => 
            if hasMutator.contains(l) then reqCapture += (l)
            p
          case _ => super.applyPath(p)
      
        override def applyDefn(defn: Defn): Defn = defn match
          case c: ClsLikeDefn if modOrObj(c) =>
            handleCalledBms(c.sym)
            super.applyDefn(defn)
          case _ => super.applyDefn(defn)

      walker.applyBlock(b)

      CaptureInfo(reqCapture, hasReader, hasMutator)

    val reqCapture = go(f.body, Set.empty, Set.empty, Set.empty).reqCapture
    val usedVars = defns.flatMap(_.freeVars.intersect(thisVars)).toSet
    (usedVars, reqCapture)

  // the current problem is that we need extra code to find which variables were really defined by a function
  // this may be resolved in the future when the IR gets explicit variable declarations
  private def findUsedLocalsFn(f: FunDefn): Map[BlockMemberSymbol, FreeVars] =
    val thisVars = definedLocals(f.sym)

    val (vars, cap) = reqdCaptureLocals(f)

    var usedMap: Map[BlockMemberSymbol, FreeVars] = Map.empty
    usedMap += (f.sym -> Lifter.FreeVars(vars.intersect(thisVars), cap.intersect(thisVars)))
    for d <- nestedDefns(f.sym) do
      usedMap ++= findUsedLocalsDefn(d)
    usedMap

  private def findUsedLocalsDefn(d: Defn) =
    d match
    case f: FunDefn => 
      findUsedLocalsFn(f)
    case c: ClsLikeDefn =>
      findUsedLocalsCls(c)
    case d => Map.empty

  private def findUsedLocalsCls(c: ClsLikeDefn): Map[BlockMemberSymbol, FreeVars] =
    nestedDefns(c.sym).foldLeft(Map.empty):
      case (acc, d) => acc ++ findUsedLocalsDefn(d)
  
  /**
    * Finds the used locals of functions which have been used by their nested definitions.
    *
    * @param b
    * @return
    */
  def findUsedLocals: Lifter.UsedLocalsMap = 
    var usedMap: Map[BlockMemberSymbol, FreeVars] = Map.empty
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyDefn(defn: Defn): Defn =
        usedMap ++= findUsedLocalsDefn(defn)
        defn
        
    walker.applyBlock(b)
    Lifter.UsedLocalsMap(usedMap)