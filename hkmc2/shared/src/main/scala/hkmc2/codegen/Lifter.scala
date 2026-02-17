package hkmc2

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
  
  extension (l: List[Lazy[Defn] | Defn])
    def gatherUsed: List[Defn] = l.collect:
      case l: Lazy[?] if !l.isEmpty => l.force_!
      case d: Defn => d
    
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

  object RefOfBms:
    def unapply(p: Path): Opt[(BlockMemberSymbol, Opt[DefinitionSymbol[?]], Bool)] = p match
      case Value.Ref(l: BlockMemberSymbol, disamb) => S((l, disamb, false))
      case s @ Select(_, _) => s.symbol match
        case Some(value) => value.asBlkMember.map((_, S(value), true))
        case _ => N
      case _ => N
  
  def modOrObj(d: Defn) = d match
    case c: ClsLikeDefn => (c.companion.isDefined) || (c.k is syntax.Obj)
    case _ => false

/**
  * Lifts classes and functions to the top-level. Also automatically rewrites lambdas.
  * Assumes the input block does not have any `HandleBlock`s.
  */
class Lifter(topLevelBlk: Block)(using State, Raise, Config):
  // TODO: implement tracing debug system

  import Lifter.*
  
  extension (l: Local)
    def asLocalPath: LocalPath = LocalPath.Sym(l)
    def asDefnRef: DefnRef = DefnRef.Sym(l)
  
  enum LocalPath:
    case Sym(l: Local)
    case BmsRef(l: BlockMemberSymbol, d: DefinitionSymbol[?])
    case InCapture(capturePath: Path, field: TermSymbol)
    
    def read(using ctx: LifterCtxNew): Path = this match
      case Sym(l) => l.asPath
      case BmsRef(l, d) => Value.Ref(l, S(d))
      case InCapture(path, field) => Select(path, field.id)(S(field))
      
    def asArg(using ctx: LifterCtxNew) = read.asArg
    
    def assign(value: Result, rest: Block)(using ctx: LifterCtxNew): Block = this match
      case Sym(l) => Assign(l, value, rest)
      case BmsRef(l, d) => lastWords("Tried to assign to a BlockMemberSymbol")
      case InCapture(path, field) => AssignField(path, field.id, value, rest)(S(field))

  enum DefnRef:
    case Sym(l: Local)
    case InScope(l: BlockMemberSymbol, d: DefinitionSymbol[?])
    case Field(isym: InnerSymbol, l: BlockMemberSymbol, d: DefinitionSymbol[?])
  
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
  ):
    def ++(that: LifterMetadata) =
      LifterMetadata(unliftable ++ that.unliftable)
  object LifterMetadata:
    def empty = LifterMetadata(Set.empty)
  
  // s is a top-level definition
  // returns (ignored classes, modules)
  private def createMetadata(s: ScopeNode): LifterMetadata =
    var ignored: Set[ClsSym | ModuleOrObjSym] = Set.empty
    val nestedScopes: Set[ScopedInfo] = s.allChildNodes.map(_.obj.toInfo).toSet - s.obj.toInfo
    
    // hack: ClassLikeSymbol does not extend DefinitionSymbol directly, so we must
    // use a map to convert
    
    val moduleObjs: List[ScopedObject.Companion | ScopedObject.Class] = s.allChildNodes.collect:
      case s @ ScopeNode(obj = o: ScopedObject.Companion) if !s.inModOrTopLevel => o
      case s @ ScopeNode(obj = o: ScopedObject.Class) if !s.inModOrTopLevel && o.isObj => o
    
    for m <- moduleObjs do
      m match
        case c: ScopedObject.Class =>
          ignored += c.cls.isym
          raise(WarningReport(
            msg"Objects are not yet lifted." -> c.cls.isym.toLoc :: Nil,
            N, Diagnostic.Source.Compilation
          ))
        case m: ScopedObject.Companion =>
          ignored += m.compDefn.isym
          ignored += m.clsBody.isym
          raise(WarningReport(
            msg"Modules are not yet lifted." -> m.clsBody.isym.toLoc :: Nil,
            N, Diagnostic.Source.Compilation
          ))
    
    var inheritanceTree: Set[(ClsSym, ClsSym)] = Set.empty
    
    // search for unliftable classes and build the extends graph
    new BlockTraverser:
      this.applyScopedObject(s.obj)
      override def applyCase(cse: Case): Unit =
        cse match
          case Case.Cls(cls: (ClassSymbol | ModuleOrObjectSymbol), _) =>
            if nestedScopes.contains(cls) && !ignored.contains(cls) && !data.getNode(cls).inModOrTopLevel then // don't generate a warning if it's already ignored
              raise(WarningReport(
                msg"Cannot yet lift class/module `${cls.nme}` as it is used in an instance check." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
              ignored += cls
          case _ => ()
      
      override def applyResult(r: Result): Unit = r match
        // do not search the ref to the class
        case Instantiate(mut, RefOfBms(_, S(d), _), args) =>
          args.foreach(applyArg)
        // for class constructors
        case Call(RefOfBms(_, S(d), _), args) =>
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
            case Some(RefOfBms(_, S(s: (ClassSymbol | ModuleOrObjectSymbol)), _)) =>
              if nestedScopes.contains(s) then inheritanceTree += (s -> isym)
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
        case RefOfBms(_, S(l), _) if nestedScopes.contains(l) => data.getNode(l).obj match
          case c: ScopedObject.Class if c.isObj => ()
          case c: (ScopedObject.Class | ScopedObject.ClassCtor) =>
            if !c.node.get.inModOrTopLevel then
              raise(WarningReport(
                msg"Cannot yet lift class `${l.nme}` as it is used as a first-class class." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
            val isym = c match
              case c: ScopedObject.Class => c.cls.isym
              case c: ScopedObject.ClassCtor => c.cls.isym
            ignored += isym
          case _ => super.applyValue(v)
        case _ => super.applyValue(v)
    
    // analyze the extends graph
    val extendsEdges = inheritanceTree.groupBy(_._1).map:
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
    
    LifterMetadata(ignored ++ newUnliftable)
  
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
    //
    // References to methods and unlifted classes nested inside classes/modules are
    // always rewritten using `this.defnName` (when accessed internally) or `object.defnName`.
    def rewriteBms(b: Block) =
      // BMS's that need to be created
      val syms: LinkedHashMap[FunSyms[?], Local] = LinkedHashMap.empty
      val extraLocals: MutSet[Local] = MutSet.empty

      val walker = new BlockDataTransformer(SymbolSubst()):
        // only scan within the block. don't traverse
        
        def resolveDefnRef(l: BlockMemberSymbol, d: DefinitionSymbol[?], r: RewrittenScope[?]) =
          ctx.defnsMap.get(d) match
          case Some(defnRef) => S(defnRef.read)
          case None => r.obj match
            case c: ScopedObject.Class if c.isObj =>
              ctx.symbolsMap.get(c.cls.isym).map(_.read)
            case c: ScopedObject.Companion =>
              ctx.symbolsMap.get(c.clsBody.isym).map(_.read)
            case _ => N

        override def applyResult(r: Result)(k: Result => Block): Block =
          r match
          // if possible, directly rewrite the call using the efficient version
          case c @ Call(RefOfBms(l, S(d), _), args) =>
            ctx.rewrittenScopes.get(d) match
              case N => super.applyResult(r)(k) // external call, or have not yet traversed that function
              case S(r) =>
                applyArgs(args): newArgs =>
                  def join2: Block =
                    resolveDefnRef(l, d, r) match
                      case Some(value) => k(c.copy(fun = value, args = newArgs)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall).withLoc(c.toLoc))
                      case None =>
                        if args is newArgs then k(c)
                        else k(c.copy(args = newArgs)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall).withLoc(c.toLoc))
                  r match
                    // function call
                    case f: LiftedFunc => k(f.rewriteCall(c, newArgs))
                    // ctor call (without using `new`)
                    case ctor: RewrittenClassCtor => ctor.getRewrittenCls match
                      case cls: LiftedClass =>
                        k(cls.rewriteCall(c, newArgs))
                      case _ => join2
                    case _ => join2
          case inst @ Instantiate(mut, RefOfBms(l, S(d), _), args) =>
            applyArgs(args): newArgs =>
              def join =
                if args is newArgs then inst
                else inst.copy(args = newArgs).withLoc(inst.toLoc)
              val res = ctx.rewrittenScopes.get(d) match
                case N => join
                case S(c: LiftedClass) => c.rewriteInstantiate(inst, newArgs)
                case S(r) => resolveDefnRef(l, d, r) match
                  case Some(value) => Instantiate(inst.mut, value, newArgs).withLoc(inst.toLoc)
                  case None => join
              k(res)
          case _ => super.applyResult(r)(k)
        
        // extract the call
        override def applyPath(p: Path)(k: Path => Block): Block = p match
          case r @ RefOfBms(l, S(d), isSel) => ctx.rewrittenScopes.get(d) match
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
            // 
            // For now, do not immediately rewrite selections if they are not referencing
            // a lifted function, and instead rewrite `qual`. This is so that, when we reference
            // a nested object or class using a selection `A.B`, we just rewrite the reference to `A`
            // instead of trying to rewrite the whole reference to `B`. The variable analyzer is
            // written so that a reference to `A` is available (in the case that `A` is a module or object),
            // as a passed parameter if needed.
            //
            // Once we properly support lifting objects, which involves putting the object instance in
            // a new public field belonging to its owner, we will need to replace the selection's 
            // disambiguation with that public field's symbol.
            case S(r) if !isSel =>
              resolveDefnRef(l, d, r) match
              case Some(value) => k(value)
              case None => super.applyPath(p)(k)
            case _ => super.applyPath(p)(k)
          
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
        
        // rewrite object definitions, assigning to the saved symbol
        case Define(d @ ClsLikeDefn(k = syntax.Obj), rest: Block) => ctx.liftedScopes.get(d.isym) match
          case Some(l: LiftedClass) if l.obj.isObj =>
            ctx.symbolsMap(l.cls.isym).assign(l.instObject, applySubBlock(rest))
          case _ => super.applyBlock(rewritten)
        case _ => super.applyBlock(rewritten)
      
      pre.rest(remaining)
    
    override def applyPath(p: Path)(k: Path => Block): Block = p match
      // This rewrites naked references to locals,
      case Value.Ref(l, _) => ctx.symbolsMap.get(l) match
        case Some(value) => k(value.read)
        case _ => super.applyPath(p)(k)
      
      case _ => super.applyPath(p)(k)
  
  case class LifterResult[+T](liftedDefn: T, extraDefns: List[Lazy[Defn] | Defn])
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
    
    val sortedVars: Array[(ctorSyms: (local: Local, vs: VarSymbol), param: Param, valDefn: ValDefn)] =
      cap.toArray.sortBy(_.uid).map: sym =>
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
      extraDefns ++= defns.gatherUsed
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
    lazy val liftedObjsMap: Map[InnerSymbol, LocalPath]
    
    lazy val capturePath: Path

    protected def rewriteImpl: LifterResult[T]
    
    protected final def addExtraSyms(b: Block, captureSym: Local, objSyms: Iterable[Local], define: Bool): Block =
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
            Set(captureSym) ++ objSyms,
            assign
          )
        else assign
      else
        if define then Scoped(objSyms.toSet, b) else b
    
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
      // Inner symbols of nested modules and objects
      val isyms = node.children
        .collect:
          case ScopeNode(obj = c: ScopedObject.Companion) =>
            val s: Local = c.clsBody.isym
            s -> LocalPath.BmsRef(c.bsym, c.clsBody.isym)
          case ScopeNode(obj = c: ScopedObject.Class) if c.isObj =>
            c.cls.isym -> (liftedObjsMap.get(c.cls.isym) match
              case Some(value) => value // lifted
              case None => LocalPath.BmsRef(c.bsym, c.cls.isym) // not lifted
            )
          
        .toMap
      // Note: the order here is important, as fromCap must override keys from
      // fromThisObj.
      isyms ++ fromThisObj ++ fromCap
    
    lazy val capturePaths =
      if thisCapturedLocals.isEmpty then Map.empty
      else Map(obj.toInfo -> capturePath)
    
    // BMS refs from ignored defns (including child defns of modules)
    // Note that we map the DefinitionSymbol to the disambiguated BMS.
    protected val defnPathsFromThisObj: Map[DefinitionSymbol[?], DefnRef] =
      node.children.filter:
        case s @ ScopeNode(obj = r: ScopedObject.Class) if r.isObj => false
        case _ => true
      .collect:
        case s @ ScopeNode(obj = r: ScopedObject.Referencable[?]) if !s.isLifted => 
          val path = r.owner match
            case Some(isym) => DefnRef.Field(isym, r.bsym, r.sym)
            case None => DefnRef.InScope(r.bsym, r.sym)
          r.sym -> path
      .toMap
    
    lazy val defnPaths: Map[DefinitionSymbol[?], DefnRef] = defnPathsFromThisObj
    
    lazy val symbolsMap: Map[Local, LocalPath] = pathsFromThisObj
  
  /** Represents a scoped object that is to be rewritten and lifted. */
  sealed abstract class LiftedScope[T <: Defn](override val obj: ScopedObject.Liftable[T])(using ctx: LifterCtxNew) extends RewrittenScope[T](obj):
    private val AccessInfo(accessed, _, refdScopes) = usedVars.accessMap(obj.toInfo)
    private val AccessInfo(_, _, allRefdScopes) = usedVars.accessMapWithIgnored(obj.toInfo)
    private val refdDSyms = refdScopes.collect:
        case d: LiftedSym => d
      .toSet
    
    /** Symbols that this object will lose access to once lifted, and therefore must receive
      * as a parameter. Does not include neighbouring objects that this definition may lose
      * access to. Those are in a separate list.
      * 
      * Includes symbols introduced by modules and objects, which could be introduced when
      * accessing their member functions.
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
    final val reqDefns = node.reqCaptureObjs
      .map(_.sym)
      .toSet.intersect(refdDSyms)
    
    /** Maps directly passed locals to the path representing that local within this object. */
    protected val passedSymsMap: Map[Local, LocalPath]
    /** Maps scopes to the path representing their captures within this object. */
    protected val capSymsMap: Map[ScopedInfo, Path]
    /** Maps definition symbols to the path representing that definition. */
    protected val passedDefnsMap: Map[DefinitionSymbol[?], DefnRef]
    
    protected lazy val capturesOrdered: List[ScopedInfo]
    protected final lazy val passedSymsOrdered: List[Local] = reqPassedSymbols.toList.sortBy(_.uid)
    protected final lazy val passedDefnsOrdered: List[DefinitionSymbol[?]] = reqDefns.toList.sortBy(_.uid)
    
    override lazy val capturePaths: Map[ScopedInfo, Path] =
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
    protected val liftedObjsSyms: Map[InnerSymbol, VarSymbol] = node.liftedObjSyms.map: s =>
        s -> VarSymbol(Tree.Ident(s.nme + "$"))
      .toMap
    override lazy val liftedObjsMap: Map[InnerSymbol, LocalPath] = liftedObjsSyms.map:
      case k -> v => k -> v.asLocalPath
    
    protected def addExtraSyms(b: Block): Block = addExtraSyms(b, captureSym, liftedObjsSyms.values, true)
    
  /**
    * A rewritten scope with a TermSymbol capture symbol.
    */
  sealed trait ClsLikeRewrittenScope[T](sym: InnerSymbol) extends RewrittenScope[T]:
    lazy val captureSym = TermSymbol(syntax.ImmutVal, S(sym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath = captureSym.asPath
    protected val liftedObjsSyms: Map[InnerSymbol, TermSymbol] = node.liftedObjSyms.map: s =>
        s -> TermSymbol(syntax.ImmutVal, S(sym), Tree.Ident(s.nme + "$"))
      .toMap
    override lazy val liftedObjsMap: Map[InnerSymbol, LocalPath] = liftedObjsSyms.map:
      case k -> v => k -> v.asLocalPath
    protected def rewriteMethods(node: ScopeNode, methods: List[FunDefn])(using ctx: LifterCtxNew) =
      val mtds = node.children
        .map: c =>
          ctx.rewrittenScopes(c.obj.toInfo)
        .collect:
          case r: RewrittenFunc if r.obj.isMethod.isDefined => r 
      val (liftedMtds, extras) = mtds.map(liftNestedScopes).unzip(using l => (l.liftedDefn, l.extraDefns))
      LifterResult(liftedMtds, extras.flatten)
  
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
      val liftedChildSyms = node.allChildNodes.collect:
        case s @ ScopeNode(obj = l: ScopedObject.Liftable[?]) if s.isLifted => l.defn.sym
      
      val (syms, rewritten) = (obj.block.syms.toSet -- liftedChildSyms, rewriter.rewrite(obj.block.body))
      val withCapture = addExtraSyms(rewritten)
      LifterResult(Scoped(syms, withCapture), rewriter.extraDefns.toList)
  
  class RewrittenLoop(override val obj: ScopedObject.Loop)(using ctx: LifterCtxNew) extends RewrittenScope[Block](obj) with GenericRewrittenScope[Block]:
    override def rewriteImpl: LifterResult[Block] =
      val rewriter = new BlockRewriter
      
      val rewritten = rewriter.rewrite(obj.body)
      val withCapture = addExtraSyms(rewritten)
      LifterResult(withCapture, rewriter.extraDefns.toList)
  
  class RewrittenFunc(override val obj: ScopedObject.Func)(using ctx: LifterCtxNew) extends RewrittenScope[FunDefn](obj) with GenericRewrittenScope[FunDefn]:
    override def rewriteImpl: LifterResult[FunDefn] =
      val rewriter = new BlockRewriter
      
      val rewritten = rewriter.rewrite(obj.fun.body)
      val withCapture = addExtraSyms(rewritten)
      LifterResult(obj.fun.copy(body = withCapture)(obj.fun.forceTailRec), rewriter.extraDefns.toList)
  
  class RewrittenClassCtor(override val obj: ScopedObject.ClassCtor)(using ctx: LifterCtxNew) extends RewrittenScope[Unit](obj):
    override lazy val capturePath: Path = lastWords("tried to create a capture class for a class ctor")
    override lazy val liftedObjsMap: Map[InnerSymbol, LocalPath] = lastWords("tried to create obj syms for a class ctor")

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
      val ctorWithCap = addExtraSyms(rewrittenCtor, captureSym, Nil, false)
        
      val LifterResult(newMtds, extras) = rewriteMethods(node, obj.cls.methods)
      val newCls = obj.cls.copy(
        ctor = ctorWithCap,
        preCtor = rewrittenPrector,
        privateFields = captureSym :: liftedObjsSyms.values.toList ::: obj.cls.privateFields,
        methods = newMtds,
      )
      LifterResult(newCls, rewriterCtor.extraDefns.toList ::: rewriterPreCtor.extraDefns.toList ::: extras)

  class RewrittenCompanion(override val obj: ScopedObject.Companion)(using ctx: LifterCtxNew)
      extends RewrittenScope[ClsLikeBody](obj)
      with ClsLikeRewrittenScope[ClsLikeBody](obj.clsBody.isym):
    
    private val captureSym = TermSymbol(syntax.ImmutVal, S(obj.clsBody.isym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath: Path = captureSym.asPath
      
    override def rewriteImpl: LifterResult[ClsLikeBody] =
      val rewriterCtor = new BlockRewriter
      val rewrittenCtor = rewriterCtor.rewrite(obj.clsBody.ctor)
      val ctorWithCap = addExtraSyms(rewrittenCtor, captureSym, Nil, false)
      val LifterResult(newMtds, extras) = rewriteMethods(node, obj.clsBody.methods)
      val newComp = obj.clsBody.copy(
        ctor = ctorWithCap,
        privateFields = captureSym :: liftedObjsSyms.values.toList ::: obj.clsBody.privateFields,
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
      val withCapture = addExtraSyms(newBod)
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
        case Nil => lastWords("tried to make an aux defn for a function with no parameter list")
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
    
    private val aux = Lazy[Defn](mkAuxDefn)
    
    def rewriteCall(c: Call, args: List[Arg])(using ctx: LifterCtxNew): Call =
      if isTrivial then
        if args is c.args then c
        else c.copy(args = args)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall).withLocOf(c)
      else
        Call(
          Value.Ref(mainSym, S(mainDsym)),
          formatArgs ::: args
        )(
          isMlsFun = true,
          mayRaiseEffects = c.mayRaiseEffects,
          explicitTailCall = c.explicitTailCall
        ).withLoc(c.toLoc)
    
    def rewriteRef(using ctx: LifterCtxNew): Call =
      if isTrivial then lastWords("tried to rewrite a ref to a trivial function")
      aux.force // forces computation
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
      else LifterResult(lifted, aux :: extra)
  class LiftedClass(override val obj: ScopedObject.Class)(using ctx: LifterCtxNew)
      extends LiftedScope[ClsLikeDefn](obj)
      with ClsLikeRewrittenScope[ClsLikeDefn](obj.cls.isym):
    
    private val captureSym = TermSymbol(syntax.ImmutVal, S(obj.cls.isym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath: Path = captureSym.asPath
    
    private val passedSymsMap_ : Map[Local, (vs: VarSymbol, ts: TermSymbol)] = passedSyms.map: s =>
        s -> 
          (
            VarSymbol(Tree.Ident(s.nme)),
            TermSymbol(syntax.LetBind, S(obj.cls.isym), Tree.Ident(s.nme))
          )
      .toMap
    private val capSymsMap_ : Map[ScopedInfo, (vs: VarSymbol, ts: TermSymbol)] = reqCaptures.map: i =>
        val nme = data.getNode(i).obj.nme + "$cap"
        i ->
          (
            VarSymbol(Tree.Ident(nme)),
            TermSymbol(syntax.LetBind, S(obj.cls.isym), Tree.Ident(nme))
          )
      .toMap
    private val defnSymsMap_ : Map[DefinitionSymbol[?], (vs: VarSymbol, ts: TermSymbol)] = reqDefns.map: i =>
        i -> 
          (
            VarSymbol(Tree.Ident(i.nme + "$")),
            TermSymbol(syntax.LetBind, S(obj.cls.isym), Tree.Ident(i.nme + "$"))
          )
      .toMap
    
    private val extraPrivSyms = 
      liftedObjsSyms.values ++ passedSymsMap_.values.map(_.ts)
      ++ capSymsMap_.values.map(_.ts) ++ defnSymsMap_.values.map(_.ts)
    
    override lazy val capturesOrdered: List[ScopedInfo] = reqCaptures.toList.sortBy(c => capSymsMap_(c).vs.uid)
    
    override protected val passedSymsMap = passedSymsMap_.view.mapValues(_.ts.asLocalPath).toMap
    override protected val capSymsMap = capSymsMap_.view.mapValues(_.ts.asPath).toMap
    override protected val passedDefnsMap = defnSymsMap_.view.mapValues(_.ts.asDefnRef).toMap
    
    val auxParams: List[Param] =
      (passedDefnsOrdered.map(x => defnSymsMap_(x).vs)
        ::: capturesOrdered.map(x => capSymsMap_(x).vs)
        ::: passedSymsOrdered.map(x => passedSymsMap_(x).vs))
      .map(Param.simple(_))
    
    // Whether this can be lifted without the need to pass extra parameters.
    val isTrivial = auxParams.isEmpty
    
    val cls = obj.cls
    
    val flattenedSym = BlockMemberSymbol(obj.cls.sym.nme + "$", Nil, true)
    val flattenedDSym = TermSymbol.fromFunBms(flattenedSym, N)
    
    def mkFlattenedDefn: FunDefn =
      val auxSyms = auxParams.map(p => VarSymbol(Tree.Ident(p.sym.nme)))
      val main = obj.cls.paramsOpt match
        case Some(value) => dupParamList(value)
        case None => obj.cls.auxParams.headOption match
          case Some(value) => dupParamList(value)
          case None => PlainParamList(Nil)
      val mainSyms = main.params.map(_.sym)
      val restSym = main.restParam.map(_.sym)
      val argList1_ = (restSym match
          case Some(value) => mainSyms.appended(value)
          case None => mainSyms
        ).map(s => s.asPath.asArg)
      val argList2_ = auxSyms.map(s => s.asPath.asArg)
      
      val clsIsParamless = cls.paramsOpt.isEmpty && cls.auxParams.length == 0
      
      val argList1 =
        if cls.paramsOpt.isEmpty && cls.auxParams.length == 0 then argList2_
        else argList1_
      val argList2 = argList2_
      
      val isMut = VarSymbol(Tree.Ident("isMut"))
      val params = ParamList(
        ParamListFlags.empty,
        Param.simple(isMut) :: auxSyms.map(Param.simple(_)) ::: main.params,
        main.restParam
      )
      val tmp = TempSymbol(N)
      val ref = Value.Ref(obj.cls.sym, S(obj.cls.isym))
      val instMut = Assign(tmp, Instantiate(true, ref, argList1), End())
      val inst = Assign(tmp, Instantiate(false, ref, argList1), End())
      val ret = 
        if clsIsParamless then Return(tmp.asPath, false)
        else Return(Call(tmp.asPath, argList2)(true, config.checkInstantiateEffect, false), false)
      val bod = Scoped(Set(tmp), Match(
        isMut.asPath,
        Case.Lit(Tree.BoolLit(true)) -> instMut :: Nil,
        S(inst),
        ret
      ))
      
      FunDefn(N, flattenedSym, flattenedDSym, params :: Nil, bod)(false)
    
    private val flat = Lazy[Defn](mkFlattenedDefn)
    
    def instObject = Instantiate(false, Value.Ref(cls.sym, S(cls.isym)), formatArgs)
    
    def rewriteInstantiate(inst: Instantiate, args: List[Arg]): Result =
      if obj.isObj then lastWords("tried to rewrite instantiate for an object")
      if isTrivial then
        val path = Value.Ref(cls.sym, S(cls.isym))
        if (inst.cls === path) && (inst.args is args) then inst
        else inst.copy(cls = path, args = args).withLocOf(inst)
      else
        flat.force // force computation
        Call(
          Value.Ref(flattenedSym, S(flattenedDSym)),
          Value.Lit(Tree.BoolLit(inst.mut)).asArg :: formatArgs ::: args
        )(true, config.checkInstantiateEffect, false).withLoc(inst.toLoc)
    
    def rewriteCall(c: Call, args: List[Arg])(using ctx: LifterCtxNew): Call =
      if obj.isObj then lastWords("tried to rewrite instantiate for an object")
      if isTrivial then
        if c.args is args then c
        else c.copy(args = args)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall).withLocOf(c)
      else
        flat.force // force computation
        Call(
          Value.Ref(flattenedSym, S(flattenedDSym)),
          Value.Lit(Tree.BoolLit(false)).asArg :: formatArgs ::: args
        )(
          isMlsFun = true,
          mayRaiseEffects = c.mayRaiseEffects,
          explicitTailCall = c.explicitTailCall
        ).withLoc(c.toLoc)
    
    def rewriteImpl: LifterResult[ClsLikeDefn] =
      val rewriterCtor = new BlockRewriter
      val rewriterPreCtor = new BlockRewriter
      val rewrittenCtor = rewriterCtor.rewrite(obj.cls.ctor)
      val rewrittenPrector = rewriterPreCtor.rewrite(obj.cls.preCtor)
      
      val ctorWithCap = addExtraSyms(rewrittenCtor, captureSym, Nil, false)
      
      // Assign passed locals and captures
      val ctorWithPassed = passedSymsOrdered.foldRight(ctorWithCap):
        case (sym, acc) =>
          val (vs, ts) = passedSymsMap_(sym)
          Assign(ts, vs.asPath, acc)
      val ctorWithCaps = capturesOrdered.foldRight(ctorWithPassed):
        case (sym, acc) =>
          val (vs, ts) = capSymsMap_(sym)
          Assign(ts, vs.asPath, acc)
      val ctorWithDefns = passedDefnsOrdered.foldRight(ctorWithCaps):
        case (sym, acc) =>
          val (vs, ts) = defnSymsMap_(sym)
          Assign(ts, vs.asPath, acc)
      
      val newAuxList = 
        if isTrivial then cls.auxParams
        else PlainParamList(auxParams) :: cls.auxParams
      
      val LifterResult(newMtds, extras) = rewriteMethods(node, obj.cls.methods)
      val newCls = obj.cls.copy(
        owner = N,
        k = syntax.Cls, // turn objects into classes
        ctor = ctorWithDefns,
        preCtor = rewrittenPrector,
        privateFields = captureSym :: extraPrivSyms.toList ::: obj.cls.privateFields,
        methods = newMtds,
        auxParams = newAuxList
      )
      val extrasDefns = rewriterCtor.extraDefns.toList ::: rewriterPreCtor.extraDefns.toList ::: extras
      LifterResult(newCls, flat :: extrasDefns)
  
  private def createRewritten[T](s: TScopeNode[T])(using ctx: LifterCtxNew): RewrittenScope[T] = s.obj match
    case _: ScopedObject.Top => lastWords("tried to rewrite the top-level scope")
    case o: ScopedObject.Class =>
      if s.isLifted then LiftedClass(o)
      else RewrittenClass(o)
    case o: ScopedObject.Companion => RewrittenCompanion(o)
    case o: ScopedObject.ClassCtor => RewrittenClassCtor(o)
    case o: ScopedObject.Func =>
      if s.isLifted then LiftedFunc(o)
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
    if r.node.isLifted then
      ctx.symbolsMap = Map.empty
      ctx.capturesMap = Map.empty
      ctx.defnsMap = Map.empty
    val ret = liftNestedScopesImpl(r)
    ctx.symbolsMap = curSyms
    ctx.capturesMap = curCaptures
    ctx.defnsMap = curDefns
    ret
  
  // entry point
  given ignoredScopes: IgnoredScopes = IgnoredScopes(N)
  val data = ScopeData(topLevelBlk)
  val metadata = data.root.children.foldLeft(LifterMetadata.empty)(_ ++ createMetadata(_))
  
  def asDSym(s: ClsSym | ModuleOrObjSym): DefinitionSymbol[?] = s
  val ignored: Set[ScopedInfo] = metadata.unliftable.map(asDSym)
  ignoredScopes.ignored = S(ignored)
    
  val usedVars = UsedVarAnalyzer(topLevelBlk, data)
  
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
