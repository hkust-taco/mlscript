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

// TODO: modules not working

object Lifter:
  /**
    * Describes the free variables of a function that have been accessed by nested definitions.
    * @param vars The free variables that are accessed by nested classes/functions.
    * @param reqCapture The free variables that must be captured using a heap-allocated object.
    */
  case class FreeVars(vars: Set[Local], reqCapture: Set[Local])

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

  def getVars(f: FunDefn): Set[Local] = 
    (f.body.definedVars ++ f.params.flatMap(_.paramSyms)).collect:
      case s: FlowSymbol => s

/**
  * Lifts classes and functions to the top-level. Also automatically rewrites lambdas.
  * Assumes the input block does not have any `HandleBlock`s.
  */
class Lifter(using State, Raise):
  import Lifter.*

  /**
    * The context of the class lifter.
    * @param usedLocals Describes the locals belonging to each function that are accessed/mutated by nested defns
    * @param localCaptureSyms The symbols in a capture corresponding to a particular local
    * @param prevFnDefns Function definitoins that have already been traversed
    * @param prevClsDefns Class definitions that have already been traversed
    * @param capturePaths The path to access a particular function's capture in the local scope
    * @param bmsReqdInfo The (mutable) captures and (immutable) local variables each function requires
    * @param bmsPaths The path to access a particular BlockMemberSymbol in the local scope with the captures already applied
    * @param localPaths The path to access a particular local (possibly belonging to a previous function) in the current scope
    * @param iSymPaths The path to access a particular `innerSymbol` (possibly belonging to a previous class) in the current scope
    */
  case class LifterCtx(
    val usedLocals: UsedLocalsMap,
    val ignoredDefns: Set[BlockMemberSymbol],
    val modules: Set[BlockMemberSymbol],
    val localCaptureSyms: Map[Local, LocalSymbol & NamedSymbol],
    val prevFnDefns: List[FunDefn],
    val prevClsDefns: List[ClsLikeDefn],
    val capturePaths: Map[BlockMemberSymbol, Path],
    val bmsReqdInfo: Map[BlockMemberSymbol, LiftedInfo], // required captures
    val bmsPaths: Map[BlockMemberSymbol, Path],
    val localPaths: Map[Local, Local],
    val isymPaths: Map[InnerSymbol, Local]
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
    def ignored(b: BlockMemberSymbol) = ignoredDefns.contains(b)
    def isModule(b: BlockMemberSymbol) = modules.contains(b)
    
    def addIgnored(defns: Set[BlockMemberSymbol]) = copy(ignoredDefns = ignoredDefns ++ defns)
    def addModules(mods: Set[BlockMemberSymbol]) = copy(modules = mods ++ modules)
    def addFnDefn(f: FunDefn) = copy(prevFnDefns = f :: prevFnDefns)
    def addClsDefn(c: ClsLikeDefn) = copy(prevClsDefns = c :: prevClsDefns)
    def addLocalCaptureSyms(m: Map[Local, LocalSymbol & NamedSymbol]) = copy(localCaptureSyms = localCaptureSyms ++ m)
    def getBmsReqdInfo(sym: BlockMemberSymbol) = bmsReqdInfo.get(sym)
    def replCapturePaths(paths: Map[BlockMemberSymbol, Path]) = copy(capturePaths = paths)
    def addCapturePath(src: BlockMemberSymbol, path: Path) = copy(capturePaths = capturePaths + (src -> path))
    def addBmsReqdInfo(mp: Map[BlockMemberSymbol, LiftedInfo]) = copy(bmsReqdInfo = bmsReqdInfo ++ mp)
    def replLocalPaths(m: Map[Local, Local]) = copy(localPaths = m)
    def replIsymPaths(m: Map[InnerSymbol, Local]) = copy(isymPaths = m)
    def addLocalPaths(m: Map[Local, Local]) = copy(localPaths = localPaths ++ m)
    def addIsymPath(isym: InnerSymbol, l: Local) = copy(isymPaths = isymPaths + (isym -> l))
  
  object LifterCtx:
    def empty = LifterCtx(UsedLocalsMap(Map.empty), Set.empty, Set.empty,
      Map.empty, Nil, Nil, Map.empty, Map.empty, Map.empty, Map.empty, Map.empty)
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
    val fakeCtorBms: Option[BlockMemberSymbol], // only for classes
    val singleCallBms: BlockMemberSymbol, // optimization
    val isMod: Bool
  )

  case class Lifted[+T <: Defn](
    val liftedDefn: T,
    val extraDefns: List[Defn],
  )

  // d is a top-level definition
  // returns (unliftable classes, modules)
  def createMetadata(d: Defn): (Set[BlockMemberSymbol], Set[BlockMemberSymbol]) =
    var clsSymToBms: Map[Local, BlockMemberSymbol] = Map.empty
    var modules: Set[BlockMemberSymbol] = Set.empty
    
    val walker = new BlockTransformer(SymbolSubst()):
      override def applyDefn(defn: Defn): Defn = 
        defn match
          case c: ClsLikeDefn => 
            clsSymToBms += c.isym -> c.sym
            if c.k is syntax.Mod then modules += c.sym
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
        case Instantiate(Select(Value.Ref(_: BlockMemberSymbol), Tree.Ident("class")), args) =>
          args.map(applyPath)
          r
        case _ => super.applyResult(r)

      override def applyValue(v: Value): Value = v match
        case Value.Ref(l: BlockMemberSymbol) if clsSyms.contains(l) && !modules.contains(l) =>
          raise(WarningReport(
            msg"Cannot yet lift the class `${l.nme}` as it is used as a higher-order class." -> N :: Nil,
            N, Diagnostic.Source.Compilation
          ))
          unliftable += l
          v
        case _ => super.applyValue(v)
    walker2.applyDefn(d)
    
    (unliftable, modules)    
      

  def createLiftInfoCont(d: Defn, parentCls: Opt[ClsLikeDefn], ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    /* 
    the commented code is incorrect, more in-depth analysis is needed to properly remove variables/captures
    that aren't needed. For example,
    fun f() =
      fun g(x) = x
      fun h(y) = y
    both g and h both capture x and y, but this is not needed.
    
    Incorrect code:
    
    val includedCaptures = ctx.prevFnDefns.filter(needsCapture(_, d, ctx))

    val includedLocals = ctx.prevFnDefns.flatMap: ls =>
      neededImutLocals(ls, d, ctx)

    val clsCaptures: List[InnerSymbol] = ctx.prevClsDefns.filter(needsClsCapture(_, d)).map(_.isym).collect:
      // this line is just to satisfy the type system, in reality anything we capture is an InnerSymbol
      case s: InnerSymbol => s

    val info = LiftedInfo(includedCaptures.map(_.sym), includedLocals, clsCaptures)
    */

    // for now, we just include everything
    val includedCaptures = ctx.prevFnDefns.filter: f =>
      val FreeVars(vars, cap) = ctx.usedLocals(f.sym)
      cap.size != 0

    val includedLocals = ctx.prevFnDefns.flatMap: f =>
      val FreeVars(vars, cap) = ctx.usedLocals(f.sym)
      vars.filter(!cap.contains(_))
    .sortBy(_.uid)

    val clsCaptures: List[InnerSymbol] = ctx.prevClsDefns.map(_.isym)

    val fakeCtorBms = d match
      case c: ClsLikeDefn => S(BlockMemberSymbol(d.sym.nme + "$ctor", Nil))
      case _ => N

    val singleCallBms = BlockMemberSymbol(d.sym.nme + "$", Nil)

    val isMod = d match
      case c: ClsLikeDefn => c.k is syntax.Mod
      case _ => false

    val info = LiftedInfo(includedCaptures.map(_.sym), includedLocals, clsCaptures, fakeCtorBms, singleCallBms, isMod)

    if includedCaptures.isEmpty && includedLocals.isEmpty && clsCaptures.isEmpty then Map.empty
    else d match
      case f: FunDefn => 
        createLiftInfoFn(f, parentCls, ctx) + (d.sym -> info)
      case c: ClsLikeDefn => 
        createLiftInfoCls(c, ctx) + (d.sym -> info)
      case _ => Map.empty
  
  def createLiftInfoFn(f: FunDefn, parentCls: Opt[ClsLikeDefn], ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val (_, defns) = f.body.floatOutDefns()
    defns.flatMap(createLiftInfoCont(_, N, ctx.addFnDefn(f))).toMap

  def createLiftInfoCls(c: ClsLikeDefn, ctx: LifterCtx): Map[BlockMemberSymbol, LiftedInfo] =
    val defns = c.preCtor.floatOutDefns()._2 ++ c.ctor.floatOutDefns()._2
    val newCtx = ctx.addClsDefn(c)
    defns.flatMap(f => createLiftInfoCont(f, N, newCtx)).toMap 
      ++ c.methods.flatMap(f => createLiftInfoFn(f, S(c), newCtx))
  
  def createLiftInfo(b: Block, ctx: LifterCtx) =
    var ret: Map[BlockMemberSymbol, LiftedInfo] = Map.empty
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(f: FunDefn, rest) => 
          ret = ret ++ createLiftInfoFn(f, N, ctx)
          super.applyBlock(b)
        case Define(c: ClsLikeDefn, rest) => 
          ret = ret ++ createLiftInfoCls(c, ctx)
          super.applyBlock(b)
        case _ => super.applyBlock(b)
    walker.applyBlock(b)
    ret

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
          case c @ Call(Value.Ref(l: BlockMemberSymbol), args) => ctx.bmsReqdInfo.get(l) match
            case Some(info) =>
              val extraArgs = getCallArgs(l, ctx)
              val newArgs = args.map(applyArg(_))
              Call(info.singleCallBms.asPath, extraArgs ++ newArgs)(c.isMlsFun, false)
            case None => super.applyResult(r)
          case c @ Instantiate(Select(Value.Ref(l: BlockMemberSymbol), Tree.Ident("class")), args) => 
            ctx.bmsReqdInfo.get(l) match
            case Some(info) =>
              val extraArgs = getCallArgs(l, ctx)
              val newArgs = args.map(applyPath(_)).map(_.asArg)
              Call(info.singleCallBms.asPath, extraArgs ++ newArgs)(true, false)
            case None => super.applyResult(r)
          // if possible, directly create the bms and replace the result with it
          case Value.Ref(l: BlockMemberSymbol) if ctx.bmsReqdInfo.contains(l) => createCall(l, ctx)
          case _ => super.applyResult(r)
        
        // otherwise, there's no choice but to create the call earlier
        override def applyValue(v: Value): Value = v match
          case Value.Ref(l: BlockMemberSymbol) if ctx.bmsReqdInfo.contains(l) => 
            val newSym = syms.get(l) match
              case None =>
                val newSym = FlowSymbol(l.nme + "$this")
                syms.addOne(l -> newSym)
                newSym
              case Some(value) => value
            Value.Ref(newSym)
          case _ => super.applyValue(v)
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
        case _ => super.applyBlock(b)
        
      override def applyPath(p: Path): Path = p match
        /*
        case Value.Ref(b: BlockMemberSymbol) => newCtx.getBmsPath(b) match
          case None => super.applyPath(p)
          case Some(value) => value
        */
        case Value.Ref(l: InnerSymbol) => ctx.getIsymPath(l) match
          case Some(value) if !belongsToCtor(value) => Value.Ref(value)
          case _ => super.applyPath(p)
        case Value.Ref(t: TermSymbol) if t.owner.isDefined =>
          ctx.getIsymPath(t.owner.get) match
            case Some(value) if !belongsToCtor(value) => Select(value.asPath, t.id)(N)
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
            blk.assign(local, createCall(bms, ctx))
        pre.rest(super.applyBlock(rewriten))

    b |> transformer1.applyBlock |> transformer2.applyBlock

  def getCallArgs(sym: BlockMemberSymbol, ctx: LifterCtx) =
    val info = ctx.getBmsReqdInfo(sym).get
    val localsArgs = info.reqdVars.map(ctx.getLocalPath(_).get.asPath.asArg)
    val capturesArgs = info.reqdCaptures.map(ctx.getCapturePath(_).get.asArg)
    val iSymArgs = info.reqdInnerSyms.map(ctx.getIsymPath(_).get.asPath.asArg)
    iSymArgs ++ localsArgs ++ capturesArgs
  
  def createCall(sym: BlockMemberSymbol, ctx: LifterCtx): Call =
    val info = ctx.getBmsReqdInfo(sym).get
    val callSym = info.fakeCtorBms match
      case Some(v) => v
      case None => sym  
    Call(callSym.asPath, getCallArgs(sym, ctx))(false, false)

  // deals with creating parameter lists
  def liftOutDefnCont(base: Defn, d: Defn, ctx: LifterCtx): Lifted[Defn] = ctx.getBmsReqdInfo(d.sym) match
    case N => Lifted(d, Nil)
    case S(LiftedInfo(includedCaptures, includedLocals, clsCaptures, fakeCtorBms, singleCallBms, isMod)) =>
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

      val localsSymbols = includedLocals.map:sym =>
        (sym, createSym(sym.nme))

      val isymSymbols = clsCaptures.map:sym =>
        (sym, createSym(sym.nme + "$instance"))

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

      val extraParams = extraParamsIsyms ++ extraParamsLocals ++ extraParamsCaptures

      val newCtx = ctx
        .replCapturePaths(newCapturePaths)
        .replLocalPaths(newLocalsPaths)
        .replIsymPaths(newIsymPaths)

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
        case c: ClsLikeDefn =>
          val newDef = c.copy(
            owner = N, auxParams = c.auxParams.appended(PlainParamList(extraParams))
          )
          val Lifted(lifted, extras) = liftDefnsInCls(newDef, newCtx)

          fakeCtorBms match
          case None => Lifted(lifted, extras) // unreachable
          case Some(bms) =>
            // create the fake ctor here

            inline def mapParams(ps: ParamList) = ps.params.map(p => VarSymbol(p.sym.id))

            val paramSyms = c.paramsOpt.map(mapParams)
            val auxSyms = c.auxParams.map(mapParams)
            val extraSyms = extraParams.map(p => VarSymbol(p.sym.id))

            val paramArgs = paramSyms.getOrElse(Nil).map(_.asPath)

            inline def toPaths(l: List[Local]) = l.map(_.asPath)
            
            var curSym = TempSymbol(None, "tmp")
            val inst = Instantiate(c.sym.asPath, paramArgs)
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
        case _ => Lifted(d, Nil)
  
  def liftDefnsInCls(c: ClsLikeDefn, ctx: LifterCtx): Lifted[ClsLikeDefn] = 
    val (preCtor, preCtorDefns) = c.preCtor.floatOutDefns()
    val (ctor, ctorDefns) = c.ctor.floatOutDefns()
    
    val newCtx = ctx.addIsymPath(c.isym, c.isym) 
    // TODO: add block member symbol replacement

    val newPreCtor = rewriteBlk(preCtor, S(c), newCtx)
    val newCtor = rewriteBlk(ctor, S(c), newCtx)

    val ctorDefnsLifted = (preCtorDefns ++ ctorDefns).flatMap: defn =>
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
    
    val (blk, nested) = f.body.floatOutDefns()

    // add the mapping from this function's locals to the capture's symbols and the capture path
    val captureSym = FlowSymbol("capture")
    val captureCtx = ctx
      .addLocalCaptureSyms(varsMap) // how to access locals via. the capture class from now on
      .addCapturePath(f.sym, captureSym.asPath) // the path to this function's capture
    val nestedCtx = captureCtx.addFnDefn(f)

    // lift out the nested defns
    val nestedLifted = nested.map(liftOutDefnCont(f, _, nestedCtx))
    val newDefns = nestedLifted.flatMap:
      case Lifted(liftedDefn, extraDefns) => liftedDefn :: extraDefns

    // some book-keeping
    val thisVars = ctx.usedLocals(f.sym)
    val newCtx = captureCtx
      .addLocalPaths((thisVars.vars.toSet -- thisVars.reqCapture).map(s => s -> s).toMap)

    val transformed = rewriteBlk(blk, N, newCtx)

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
    val ctx = LifterCtx.withLocals(UsedVarAnalyzer(blk).findUsedLocals)
    val ctxx = ctx.addBmsReqdInfo(createLiftInfo(blk, ctx))
    
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyBlock(b: Block): Block = b match
        case Define(d, rest) =>
          val (unliftable, modules) = createMetadata(d)
          val ctxxx = ctxx.addIgnored(unliftable).addModules(modules)
          val Lifted(lifted, extra) = d match
            case f: FunDefn => liftDefnsInFn(f, ctxxx)
            case c: ClsLikeDefn => liftDefnsInCls(c, ctxxx)
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
class UsedVarAnalyzer(b: Block):
  import Lifter.FreeVars

  private case class AccessInfo(
    accessed: Set[Local], 
    mutated: Set[Local], 
    refdDefns: Set[BlockMemberSymbol]):
    def ++(that: AccessInfo) = AccessInfo(
        accessed ++ that.accessed,
        mutated ++ that.mutated,
        refdDefns ++ that.refdDefns
      )
    def addAccess(l: Local) = this.copy(accessed = accessed + l)
    def addMutated(l: Local) = this.copy(accessed = accessed + l, mutated = mutated + l)
    def addRefdDefn(l: BlockMemberSymbol) = this.copy(refdDefns = refdDefns + l)
  private object AccessInfo:
    val empty = AccessInfo(Set.empty, Set.empty, Set.empty)

  // the current problem is that we need extra code to find which variables were really defined by a function
  // this may be resolved in the future when the IR gets explicit variable declarations

  private def getDefinedLocals: (Map[BlockMemberSymbol, Set[Local]], Map[BlockMemberSymbol, Defn]) =
    var defnsMap: Map[BlockMemberSymbol, Defn] = Map.empty
    var usedMap: Map[BlockMemberSymbol, Set[Local]] = Map.empty

    def getDefinedLocalsFn(f: FunDefn, existing: Set[Local]): Unit =
      val thisVars = Lifter.getVars(f) -- existing
      val newExisting = existing ++ thisVars

      defnsMap += (f.sym -> f)
      usedMap += (f.sym -> thisVars)
      val walker = new BlockTransformerShallow(SymbolSubst()):
        override def applyDefn(defn: Defn): Defn =
          getDefinedLocalsDefn(defn, newExisting)
          defn
      walker.applyBlock(f.body)

    def getDefinedLocalsDefn(d: Defn, existing: Set[Local]): Unit =
      d match
      case f: FunDefn => 
        getDefinedLocalsFn(f, existing)
      case c: ClsLikeDefn =>
        getDefinedLocalsCls(c, existing)
      case d => Map.empty

    def getDefinedLocalsCls(c: ClsLikeDefn, existing: Set[Local]): Unit =
      defnsMap += (c.sym -> c)
      val newExisting = existing ++ c.preCtor.definedVars ++ c.ctor.definedVars
      for f <- c.methods do getDefinedLocalsFn(f, newExisting)
  
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyDefn(defn: Defn): Defn = 
        getDefinedLocalsDefn(defn, b.definedVars)
        defn
    walker.applyBlock(b)
    (usedMap, defnsMap)

  private val (definedLocals, defnsMap) = getDefinedLocals
  
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
          case Value.Ref(l: BlockMemberSymbol) =>
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
          blkAccessesShallow(f.body)
        case c: ClsLikeDefn =>
          c.methods.foldLeft(blkAccessesShallow(c.preCtor) ++ blkAccessesShallow(c.ctor)): 
            // here, we count the class as "accessing" all its methods (since they could be invoked anywhere)
            case (acc, defn) => acc.addAccess(defn.sym) ++ findAccessesShallow(defn)
        case _: ValDefn => AccessInfo.empty
      accessedCache.addOne(defn.sym -> ret)
      ret

  // MUST be called from a top-level defn
  private def findAccesses(f: FunDefn): Map[BlockMemberSymbol, AccessInfo] =
    var defns: List[Defn] = Nil
    val walker = new BlockTransformer(SymbolSubst()):
      override def applyDefn(defn: Defn): Defn = 
        defn match
          case f: FunDefn => defns +:= f
          case c: ClsLikeDefn => defns +:= c
          case _ => 
        super.applyDefn(defn)
    walker.applyBlock(f.body)

    val defnSyms = defns.map(_.sym).toSet

    val accessInfo = defns.map: d =>
      val accesses = findAccessesShallow(d)
      d.sym -> accesses.copy(refdDefns = accesses.refdDefns.intersect(defnSyms))

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
    yield sym -> sccAccessInfo(id)

  private def findAccessesTop =
    var accessMap: Map[BlockMemberSymbol, AccessInfo] = Map.empty
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyDefn(defn: Defn): Defn = defn match
        case f: FunDefn => 
          accessMap ++= findAccesses(f); f
        case c: ClsLikeDefn =>
          for f <- c.methods do accessMap ++= findAccesses(f); c
        case _ => super.applyDefn(defn)
    walker.applyBlock(b)
    accessMap
  
  private val accessMap = findAccessesTop

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
          case Call(Value.Ref(l: BlockMemberSymbol), args) =>
            args.map(super.applyArg(_))
            handleCalledBms(l)
            r
          case Instantiate(Select(Value.Ref(l: BlockMemberSymbol), Tree.Ident("class")), args) =>
            args.map(super.applyPath(_))
            handleCalledBms(l)
            r
          case _ => super.applyResult(r)
        
        override def applyValue(v: Value): Value = v match
          case Value.Ref(l: BlockMemberSymbol) => 
            defnSyms.get(l) match
            case None => super.applyValue(v)
            case Some(defn) =>
              val isMod = defn match
                case c: ClsLikeDefn => c.k is syntax.Mod
                case _ => false
              if isMod then super.applyValue(v)
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
              
              v          
          case Value.Ref(l) => 
            if hasMutator.contains(l) then reqCapture += (l)
            v
          case _ => super.applyValue(v)
      
        override def applyDefn(defn: Defn): Defn = defn match
          case c: ClsLikeDefn if c.k is syntax.Mod =>
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
    val walker = new BlockTransformerShallow(SymbolSubst()):
      override def applyDefn(defn: Defn): Defn = defn match
        case f: FunDefn => 
          usedMap ++= findUsedLocalsFn(f)
          f
        case c: ClsLikeDefn =>
          for f <- c.methods do
            usedMap ++= findUsedLocalsFn(f)
          c
        case d => super.applyDefn(d)
    walker.applyBlock(f.body)
    usedMap

  private def findUsedLocalsDefn(d: Defn) =
    d match
    case f: FunDefn => 
      findUsedLocalsFn(f)
    case c: ClsLikeDefn =>
      findUsedLocalsCls(c)
    case d => Map.empty

  private def findUsedLocalsCls(c: ClsLikeDefn): Map[BlockMemberSymbol, FreeVars] =
    c.methods.foldLeft(Map.empty):
      case (acc, f) => acc ++ findUsedLocalsFn(f)
  
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