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
import hkmc2.ScopeData.ScopedObject.Top
import hkmc2.ScopeData.ScopedObject.Companion
import hkmc2.ScopeData.ScopedObject.ClassCtor
import hkmc2.ScopeData.ScopedObject.Func
import hkmc2.ScopeData.ScopedObject.Loop
import hkmc2.ScopeData.ScopedObject.ScopedBlock

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
  
  extension (l: Local)
    def asLocalPath: LocalPath = LocalPath.Sym(l)
    def asDefnRef: DefnRef = DefnRef.Sym(l)
  
  enum LocalPath:
    case Sym(l: Local)
    case BmsRef(l: BlockMemberSymbol, d: DefinitionSymbol[?])
    case InCapture(capturePath: Path, field: TermSymbol)
    case PubField(isym: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol, sym: BlockMemberSymbol, tsym: TermSymbol)
    
    def read(using ctx: LifterCtxNew): Path = this match
      case Sym(l) => l.asPath
      case BmsRef(l, d) => Value.Ref(l, S(d))
      case InCapture(path, field) => Select(path, field.id)(S(field))
      case PubField(isym, sym, tsym) => Select(ctx.symbolsMap(isym).read, Tree.Ident(sym.nme))(S(tsym))
      
    def asArg(using ctx: LifterCtxNew) = read.asArg
    
    def assign(value: Result, rest: Block)(using ctx: LifterCtxNew): Block = this match
      case Sym(l) => Assign(l, value, rest)
      case BmsRef(l, d) => lastWords("Tried to assign to a BlockMemberSymbol")
      case InCapture(path, field) => AssignField(path, field.id, value, rest)(S(field))
      case PubField(isym, sym, tsym) => AssignField(ctx.symbolsMap(isym).read, Tree.Ident(sym.nme), value, rest)(S(tsym))

  enum DefnRef:
    case Sym(l: Local)
    case InScope(l: BlockMemberSymbol, d: DefinitionSymbol[?])
    case Field(isym: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol, l: BlockMemberSymbol, d: DefinitionSymbol[?])
  
    def read(using ctx: LifterCtxNew): Path = this match
      case Sym(l) => l.asPath
      case InScope(l, d) => Value.Ref(l, S(d))
      case Field(isym, l, d) => Select(ctx.symbolsMap(isym).read, Tree.Ident(l.nme))(S(d))
    
    def asArg(using ctx: LifterCtxNew) = read.asArg
  
  case class FunSyms[T <: DefinitionSymbol[?]](b: BlockMemberSymbol, d: T):
    def asPath = Value.Ref(b, S(d))
  object FunSyms:
    def fromFun(b: BlockMemberSymbol, owner: Opt[InnerSymbol] = N) =
      FunSyms(b, TermSymbol.fromFunBms(b, owner))
  
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
      case s @ ScopeNode(obj = o: ScopedObject.Companion) if !s.isTopLevel => o
    
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
            if nestedScopes.contains(cls) && !ignored.contains(cls) && !data.getNode(cls).isInTopLevelMod then // don't generate a warning if it's already ignored
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
        case RefOfBms(_, S(l)) if nestedScopes.contains(l) => data.getNode(l).obj match
          case c: (ScopedObject.Class | ClassCtor) =>
            if !c.node.get.isInTopLevelMod then
              raise(WarningReport(
                msg"Cannot yet lift class `${l.nme}` as it is used as a first-class class." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
            val isym = c match
              case c: ScopedObject.Class => c.cls.isym
              case c: ClassCtor => c.cls.isym
            ignored += isym
          case Func(fun, isMethod) => firstClsFns += fun.dSym
          case _ => super.applyValue(v)
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
          case c @ Call(RefOfBms(l, S(d)), args) =>
            def join = ctx.defnsMap.get(d) match
              case Some(value) => c.copy(fun = value.read)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall)
              case None => c
            val newCall = ctx.rewrittenScopes.get(d) match
              case None => c
              case Some(value) => value match
                // function call
                case f: LiftedFunc => f.rewriteCall(c)
                // ctor call (without using `new`)
                case ctor: RewrittenClassCtor => ctor.getRewrittenCls match
                  case cls: LiftedClass =>
                    cls.rewriteCall(c)
                  case _ => ctx.defnsMap.get(d) match
                    case Some(value) => join
                    case None => c
                case _ => join
            applyArgs(newCall.args): newArgs =>
              if (newCall.args is newArgs) && (c is newCall) then k(newCall)
              else k(Call(newCall.fun, newArgs)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall))
          case inst @ Instantiate(mut, RefOfBms(l, S(d)), args) => 
            // It is VERY IMPORTANT that we rewrite it like this and not using super.applyResult.
            // The reason is that Instantiate is disambiguated using the class's InnerSymbol, which is also
            // used to represent the class's `this`. super.applyResult would apply super.applyPath on the
            // disambiguated BMS ref, which would replace it with the InnerSymbol, since the class scoped object
            // adds `this -> this` to the symbols map.
            val newInst = ctx.rewrittenScopes.get(d) match
              case S(c: LiftedClass) => c.rewriteInstantiate(inst)
              case _ => ctx.defnsMap.get(d) match
                case Some(value) => Instantiate(inst.mut, value.read, inst.args)
                case None => inst
              
            applyArgs(newInst.args): newArgs =>
              if (newInst.args is newArgs) && (newInst is inst) then k(newInst)
              else k(Instantiate(newInst.mut, newInst.cls, newArgs))
          case _ => super.applyResult(r)(k)
        
        // extract the call
        override def applyPath(p: Path)(k: Path => Block): Block = p match
          case r @ RefOfBms(l, S(d)) => ctx.rewrittenScopes.get(d) match
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
            case _ => ctx.defnsMap.get(d) match
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
            case l: LiftedFunc => blk.assign(local, l.rewriteRef)
            case _ => die
      
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
    
    override def applyPath(p: Path)(k: Path => Block): Block = p match
      // This rewrites naked references to locals,
      case Value.Ref(l, _) => ctx.symbolsMap.get(l) match
        case Some(value) => k(value.read)
        case _ => super.applyPath(p)(k)
      
      case _ => super.applyPath(p)(k)
  
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
  
  case class LifterResult[+T](liftedDefn: T, extraDefns: List[Defn])
  case class LifterCtxNew(
    liftedScopes: MutMap[LiftedSym, LiftedScope[?]] = MutMap.empty,
    rewrittenScopes: MutMap[ScopedInfo, RewrittenScope[?]] = MutMap.empty,
    var symbolsMap: Map[Local, LocalPath] = Map.empty,
    var defnsMap: Map[DefinitionSymbol[?], DefnRef] = Map.empty,
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
      : (ClsLikeDefn, List[(Symbol, TermSymbol)]) =
    val nme = "Capture$" + s.nme

    val clsSym = ClassSymbol(
      Tree.DummyTypeDef(syntax.Cls),
      Tree.Ident(nme)
    )

    val cap = usedVars.reqdCaptures(s.toInfo)

    val fresh = FreshInt()
    
    val sortedVars: Array[(ctorSyms: (local: Local, vs: VarSymbol), param: Param, valDefn: ValDefn)] = cap.toArray.sortBy(_.uid).map: sym =>
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
      PlainParamList(sortedVars.iterator.map(_.param).toList) :: Nil, None, Nil, Nil, 
      Nil,
      End(),
      sortedVars.iterator.foldLeft[Block](End()):
        case (acc, (_, _, vd)) => Define(vd, acc),
      N,
      N,
    )
    
    (defn, sortedVars.iterator.map(x => (x.ctorSyms.local, x.valDefn.tsym)).toList)
  
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
        val newComp = c.companion.map(comp => applyRewrittenScope(ctx.rewrittenScopes(comp.isym))) match
          case Some(c: ClsLikeBody) => S(c)
          case Some(_) => die 
          case None => N
        
        k(newCls.copy(companion = newComp))
      case _ => super.applyDefn(defn)(k)

  /**
    * Represents a scoped object that will be rewritten to reference the lifted version of objects and variables.
    */
  sealed abstract class RewrittenScope[T](val obj: TScopedObject[T]):
    val node = obj.node.get
    
    protected final val thisCapturedLocals = usedVars.reqdCaptures(obj.toInfo)
    val hasCapture = !thisCapturedLocals.isEmpty
    
    // These are lazy, because we don't necessarily need a captrue 
    private final lazy val captureInfo: (ClsLikeDefn, List[(Local, TermSymbol)]) = createCaptureCls(obj)
    
    lazy val captureClass = captureInfo._1
    lazy val captureMap = captureInfo._2.toMap
    
    lazy val capturePath: Path

    protected def rewriteImpl: LifterResult[T]
    
    protected final def addCaptureSym(b: Block, captureSym: Local, define: Bool): Block =
      if hasCapture then
        val undef = Value.Lit(Tree.UnitLit(false)).asArg
        val inst = Instantiate(
          true,
          Value.Ref(captureClass.sym, S(captureClass.isym)),
          captureInfo._2.map:
            case (sym, _) => sym.asPath.asArg
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
    final def rewrite =
      if hasCapture then
        val LifterResult(defn, extra) = rewriteImpl
        LifterResult(defn, captureClass :: extra)
      else rewriteImpl
    
    /** The path to access locals defined by this object. The primary purpose of this is to rewrite accesses
      * to locals that have been moved to a capture.
      */
    protected final def pathsFromThisObj: Map[Local, LocalPath] =
      // Remove child BlockMemberSymbols; we will use their definition symbols instead
      val childrenBms = node.children.collect:
        case ScopeNode(obj = r: ScopedObject.Referencable[?]) => r.bsym
        
      // Locals introduced by this object
      val fromThisObj = node.localsWithoutBms
        .map: s =>
          s -> s.asLocalPath
        .toMap
      // Locals introduced by this object that are inside this object's capture
      val fromCap = thisCapturedLocals
        .map: s =>
          val tSym = captureMap(s)
          s -> LocalPath.InCapture(capturePath, tSym)
        .toMap
      // Note: the order here is important, as fromCap must override keys from
      // fromThisObj.
      fromThisObj ++ fromCap
    
    lazy val capturePaths =
      if thisCapturedLocals.isEmpty then Map.empty
      else Map(obj.toInfo -> capturePath)
    
    // BMS refs from ignored defns
    // Note that we map the DefinitionSymbol to the disambiguated BMS.
    protected lazy val defnPathsFromThisObj: Map[DefinitionSymbol[?], DefnRef] =
      node.children.collect:
        case s @ ScopeNode(obj = r: ScopedObject.Referencable[?]) if !s.isLifted =>
          r.sym -> DefnRef.InScope(r.bsym, r.sym)
      .toMap
    
    lazy val defnPaths: Map[DefinitionSymbol[?], DefnRef] = defnPathsFromThisObj
    
    lazy val symbolsMap: Map[Local, LocalPath] = pathsFromThisObj
  
  /** Represents a scoped object that is to be rewritten and lifted. */
  sealed abstract class LiftedScope[T <: Defn](override val obj: ScopedObject.Liftable[T])(using ctx: LifterCtxNew) extends RewrittenScope[T](obj):
    private val AccessInfo(accessed, _, refdScopes) = usedVars.accessMap(obj.toInfo)
    private val refdDSyms = refdScopes.collect:
        case d: LiftedSym => d
      .toSet
    
    /** Symbols that this object will lose access to once lifted, and therefore must receive
      * as a parameter. Does not include neighbouring objects that this definition may lose
      * access to. Those are in a separate list.
      */
    final val reqSymbols = accessed
    
    private val (reqPassedSymbols, captures) = reqSymbols
      .partitionMap: s =>
        usedVars.capturesMap.get(s) match
          case Some(info) => R((s, info))
          case None => L(s)
    
    /** Locals that are directly passed to this object, i.e. not via a capture. */
    final val passedSyms: Set[Local] = reqPassedSymbols
    /** Maps locals to the scope where they were defined. */
    final val capturesOrigin: Map[Local, ScopedInfo] = captures.toMap
    /** Locals that are inside captures. */
    final val inCaptureSyms: Set[Local] = captures.map(_._1)
    /** Scopes whose captures this object requires. */
    final val reqCaptures: Set[ScopedInfo] = captures.map(_._2)
    /**
      * Neighbouring objects that this definition may lose access to
      * once lifted, referenced by their *definition symbol* (not BMS).
      */
    final val reqDefns = node.reqCaptureObjs.map(_.sym).toSet.intersect(refdDSyms)
    
    /** Maps directly passed locals to the path representing that local within this object. */
    protected val passedSymsMap: Map[Local, LocalPath]
    /** Maps scopes to the path representing their captures within this object. */
    protected val capSymsMap: Map[ScopedInfo, Path]
    /** Maps definition symbols to the path representing that definition. */
    protected val passedDefnsMap: Map[DefinitionSymbol[?], DefnRef]
    
    protected lazy val capturesOrdered: List[ScopedInfo]
    protected final lazy val passedSymsOrdered: List[Local] = reqPassedSymbols.toList.sortBy(_.uid)
    protected final lazy val passedDefnsOrdered: List[DefinitionSymbol[?]] = reqDefns.toList.sortBy(_.uid)
    
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
    
    override lazy val defnPaths: Map[DefinitionSymbol[?], DefnRef] =
      val fromParents = reqDefns
        .map: s =>
          s -> passedDefnsMap(s)
        .toMap
      defnPathsFromThisObj ++ fromParents
    
    final def formatArgs: List[Arg] =
      val defnsArgs = passedDefnsOrdered.map(d => ctx.defnsMap(d).asArg)
      val captureArgs = capturesOrdered.map(c => ctx.capturesMap(c).asArg)
      val localArgs = passedSymsOrdered.map(l => ctx.symbolsMap(l).asArg)
      defnsArgs ::: captureArgs ::: localArgs
  
  /* MIXINS */
  
  /**
    * A rewritten scope with a generic VarSymbol capture symbol.
    */
  sealed trait GenericRewrittenScope[T] extends RewrittenScope[T]:
    lazy val captureSym = VarSymbol(Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath = captureSym.asPath
    
    protected def addCaptureSym(b: Block): Block = addCaptureSym(b, captureSym, true)
  
  sealed trait ClsLikeRewrittenScope[T](isym: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol) extends RewrittenScope[T]:
    // always select using `this`
    override lazy val defnPathsFromThisObj =
      node.children.collect:
        case s @ ScopeNode(obj = r: ScopedObject.Referencable[?]) if !s.isLifted =>
          r.sym -> DefnRef.Field(isym, r.bsym, r.sym)
      .toMap
  
  // some helpers
  private def dupParam(p: Param): Param = p.copy(sym = VarSymbol(Tree.Ident(p.sym.nme)))
  private def dupParams(plist: List[Param]): List[Param] = plist.map(dupParam)
  private def dupParamList(plist: ParamList): ParamList =
    plist.copy(params = dupParams(plist.params), restParam = plist.restParam.map(dupParam))
  
  /* CONCRETE IMPLS */
  
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

  private def rewriteMethods(node: ScopeNode, methods: List[FunDefn])(using ctx: LifterCtxNew) =
    val mtds = node.children
      .map: c =>
        ctx.rewrittenScopes(c.obj.toInfo)
      .collect:
        case r: RewrittenFunc if r.obj.isMethod.isDefined => r 
    val (liftedMtds, extras) = mtds.map(liftNestedScopes).unzip(using l => (l.liftedDefn, l.extraDefns))
    LifterResult(liftedMtds, extras.flatten)
  
  class RewrittenClassCtor(override val obj: ScopedObject.ClassCtor)(using ctx: LifterCtxNew) extends RewrittenScope[Unit](obj):

    override lazy val capturePath: Path = lastWords("tried to create a capture class for a class ctor")

    override protected def rewriteImpl: LifterResult[Unit] = LifterResult((), Nil) // dummy
    
    def getRewrittenCls = ctx.rewrittenScopes(obj.cls.isym)
  
  class RewrittenClass(override val obj: ScopedObject.Class)(using ctx: LifterCtxNew)
      extends RewrittenScope[ClsLikeDefn](obj)
      with ClsLikeRewrittenScope[ClsLikeDefn](obj.cls.isym):
    
    private val captureSym = TermSymbol(syntax.ImmutVal, S(obj.cls.isym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath: Path = captureSym.asPath
      
    override def rewriteImpl: LifterResult[ClsLikeDefn] =
      val rewriterCtor = new BlockRewriter
      val rewriterPreCtor = new BlockRewriter
      val rewrittenCtor = rewriterCtor.rewrite(obj.cls.ctor)
      val rewrittenPrector = rewriterPreCtor.rewrite(obj.cls.preCtor)
      val ctorWithCap = addCaptureSym(rewrittenCtor, captureSym, false)
        
      val LifterResult(newMtds, extras) = rewriteMethods(node, obj.cls.methods)
      val newCls = obj.cls.copy(
        ctor = ctorWithCap,
        preCtor = rewrittenPrector,
        privateFields = captureSym :: obj.cls.privateFields,
        methods = newMtds,
      )
      LifterResult(newCls, rewriterCtor.extraDefns.toList ::: rewriterPreCtor.extraDefns.toList ::: extras)

  class RewrittenCompanion(override val obj: ScopedObject.Companion)(using ctx: LifterCtxNew)
      extends RewrittenScope[ClsLikeBody](obj)
      with ClsLikeRewrittenScope[ClsLikeBody](obj.comp.isym):
    
    private val captureSym = TermSymbol(syntax.ImmutVal, S(obj.comp.isym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath: Path = captureSym.asPath
      
    override def rewriteImpl: LifterResult[ClsLikeBody] =
      val rewriterCtor = new BlockRewriter
      val rewrittenCtor = rewriterCtor.rewrite(obj.comp.ctor)
      val ctorWithCap = addCaptureSym(rewrittenCtor, captureSym, false)
      val LifterResult(newMtds, extras) = rewriteMethods(node, obj.comp.methods)
      val newComp = obj.comp.copy(
        ctor = ctorWithCap,
        privateFields = captureSym :: obj.comp.privateFields,
        methods = newMtds
      )
      LifterResult(newComp, rewriterCtor.extraDefns.toList ::: extras)
   
  class LiftedFunc(override val obj: ScopedObject.Func)(using ctx: LifterCtxNew) extends LiftedScope[FunDefn](obj) with GenericRewrittenScope[FunDefn]:
    private val passedSymsMap_ : Map[Local, VarSymbol] = passedSyms.map: s =>
        s -> VarSymbol(Tree.Ident(s.nme))
      .toMap
    private val capSymsMap_ : Map[ScopedInfo, VarSymbol] = reqCaptures.map: i =>
        val nme = data.getNode(i).obj.nme
        i -> VarSymbol(Tree.Ident(nme + "$cap"))
      .toMap
    private val defnSymsMap_ : Map[DefinitionSymbol[?], VarSymbol] = reqDefns.map: i =>
        val nme = data.getNode(i).obj.nme
        i -> VarSymbol(Tree.Ident(nme + "$"))
      .toMap
    
    override lazy val capturesOrdered: List[ScopedInfo] = reqCaptures.toList.sortBy(c => capSymsMap_(c).uid)
    
    override protected val passedSymsMap = passedSymsMap_.view.mapValues(_.asLocalPath).toMap
    override protected val capSymsMap = capSymsMap_.view.mapValues(_.asPath).toMap
    override protected val passedDefnsMap = defnSymsMap_.view.mapValues(_.asDefnRef).toMap
    
    val auxParams: List[Param] =
      (passedDefnsOrdered.map(defnSymsMap_) ::: capturesOrdered.map(capSymsMap_) ::: passedSymsOrdered.map(passedSymsMap_))
      .map: s =>
        val decl = Param(FldFlags.empty.copy(isVal = false), s, N, Modulefulness.none)
        s.decl = S(decl)
        decl
    
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
      val newDefn = fun.copy(owner = N, sym = mainSym, dSym = mainDsym, params = newPlists, body = withCapture)(fun.forceTailRec)
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
        N,
        auxSym,
        auxDsym,
        newPlists,
        bod
      )(false)
    
    def rewriteCall(c: Call)(using ctx: LifterCtxNew): Call =
      if isTrivial then c
      else
        Call(
          Value.Ref(mainSym, S(mainDsym)),
          formatArgs ::: c.args
        )(
          isMlsFun = true,
          mayRaiseEffects = c.mayRaiseEffects,
          explicitTailCall = c.explicitTailCall
        )
    
    def rewriteRef(using ctx: LifterCtxNew): Call =
      Call(
        Value.Ref(auxSym, S(auxDsym)),
        formatArgs
      )(
        isMlsFun = true,
        mayRaiseEffects = false,
        explicitTailCall = false
      )
    
    def rewriteImpl: LifterResult[FunDefn] =
      val LifterResult(lifted, extra) = mkFlattenedDefn
      if isTrivial then LifterResult(lifted, extra)
      else LifterResult(lifted, mkAuxDefn :: extra)
  class LiftedClass(override val obj: ScopedObject.Class)(using ctx: LifterCtxNew)
      extends LiftedScope[ClsLikeDefn](obj)
      with ClsLikeRewrittenScope[ClsLikeDefn](obj.cls.isym):
    
    private val captureSym = TermSymbol(syntax.ImmutVal, S(obj.cls.isym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath: Path = captureSym.asPath
    
    private val passedSymsMap_ : Map[Local, (vs: VarSymbol, ts: TermSymbol)] = passedSyms.map: s =>
        s -> 
          (
            VarSymbol(Tree.Ident(s.nme)),
            TermSymbol(syntax.MutVal, S(obj.cls.isym), Tree.Ident(s.nme))
          )
      .toMap
    private val capSymsMap_ : Map[ScopedInfo, (vs: VarSymbol, ts: TermSymbol)] = reqCaptures.map: i =>
        val nme = data.getNode(i).obj.nme + "$cap"
        i -> 
          (
            VarSymbol(Tree.Ident(nme)),
            TermSymbol(syntax.ImmutVal, S(obj.cls.isym), Tree.Ident(nme))
          )
      .toMap
    private val defnSymsMap_ : Map[DefinitionSymbol[?], (vs: VarSymbol, ts: TermSymbol)] = reqDefns.map: i =>
        i -> 
          (
            VarSymbol(Tree.Ident(i.nme + "$")),
            TermSymbol(syntax.ImmutVal, S(obj.cls.isym), Tree.Ident(i.nme + "$"))
          )
      .toMap
    
    override lazy val capturesOrdered: List[ScopedInfo] = reqCaptures.toList.sortBy(c => capSymsMap_(c).vs.uid)
    
    override protected val passedSymsMap = passedSymsMap_.view.mapValues(_.ts.asLocalPath).toMap
    override protected val capSymsMap = capSymsMap_.view.mapValues(_.ts.asPath).toMap
    override protected val passedDefnsMap = defnSymsMap_.view.mapValues(_.ts.asDefnRef).toMap
    
    val auxParams: List[Param] =
      (passedDefnsOrdered.map(x => defnSymsMap_(x).vs) ::: capturesOrdered.map(x => capSymsMap_(x).vs) ::: passedSymsOrdered.map(x => passedSymsMap_(x).vs))
      .map(Param.simple(_))
    
    // Whether this can be lifted without the need to pass extra parameters.
    val isTrivial = auxParams.isEmpty
    
    val cls = obj.cls
    
    def rewriteInstantiate(inst: Instantiate): Instantiate =
      if isTrivial then inst
      else
        Instantiate(
          inst.mut,
          Value.Ref(cls.sym, S(cls.isym)),
          formatArgs ::: inst.args
        )
    
    def rewriteCall(c: Call)(using ctx: LifterCtxNew): Call =
      if isTrivial then c
      else
        Call(
          Value.Ref(cls.sym, S(cls.ctorSym.get)),
          formatArgs ::: c.args
        )(
          isMlsFun = true,
          mayRaiseEffects = c.mayRaiseEffects,
          explicitTailCall = c.explicitTailCall
        )
    
    def rewriteImpl: LifterResult[ClsLikeDefn] =
      val rewriterCtor = new BlockRewriter
      val rewriterPreCtor = new BlockRewriter
      val rewrittenCtor = rewriterCtor.rewrite(obj.cls.ctor)
      val rewrittenPrector = rewriterPreCtor.rewrite(obj.cls.preCtor)
      
      val ctorWithCap = addCaptureSym(rewrittenCtor, captureSym, false)
      
      // Assign passed locals and captures
      val ctorWithPassed = passedSymsOrdered.foldRight(ctorWithCap):
        case (sym, acc) =>
          val (vs, ts) = passedSymsMap_(sym)
          Assign(ts, vs.asPath, acc)
      val ctorWithCaps = capturesOrdered.foldRight(ctorWithPassed):
        case (sym, acc) =>
          val (vs, ts) = capSymsMap_(sym)
          Assign(ts, vs.asPath, acc)
      
      val (newPlist, newAuxList) = cls.paramsOpt match
        case Some(plist) =>
          (
            S(plist.copy(params = auxParams ::: plist.params)),
            cls.auxParams
          )
        case None =>
          (
            N,
            PlainParamList(auxParams) :: cls.auxParams
          )
      
      val LifterResult(newMtds, extras) = rewriteMethods(node, obj.cls.methods)
      val newCls = obj.cls.copy(
        owner = N,
        ctor = ctorWithCaps,
        preCtor = rewrittenPrector,
        privateFields = captureSym :: obj.cls.privateFields,
        methods = newMtds,
        paramsOpt = newPlist,
        auxParams = newAuxList
      )
      LifterResult(newCls, rewriterCtor.extraDefns.toList ::: rewriterPreCtor.extraDefns.toList ::: extras)
  
  private def createRewritten[T](s: TScopeNode[T])(using ctx: LifterCtxNew): RewrittenScope[T] = s.obj match
    case _: ScopedObject.Top => lastWords("tried to rewrite the top-level scope")
    case o: ScopedObject.Class =>
      if s.isLifted && !s.isTopLevel then LiftedClass(o)
      else RewrittenClass(o)
    case o: ScopedObject.Companion => RewrittenCompanion(o)
    case o: ScopedObject.ClassCtor => RewrittenClassCtor(o)
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
    ctx.defnsMap ++= scope.defnPaths
        
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
    val curDefns = ctx.defnsMap
    val ret = liftNestedScopesImpl(r)
    ctx.symbolsMap = curSyms
    ctx.capturesMap = curCaptures
    ctx.defnsMap = curDefns
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
    
    