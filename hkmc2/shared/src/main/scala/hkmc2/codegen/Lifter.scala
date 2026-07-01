package hkmc2

import hkmc2.utils.*, shorthands.*
import utils.*

import syntax.{Keyword, SpreadKind}
import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.ScopeData.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.Tree

import scala.collection.mutable.LinkedHashMap
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.ListBuffer

  
/** This loose type is only here as a legacy for the lifter to work,
  * but eventually the lifter should use more precise types for the symbols it tracks. */
type ScopedOrInnerSymbol = ScopedSymbol | InnerSymbol


object Lifter:
  
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
      accessed: Set[ScopedOrInnerSymbol], 
      mutated: Set[ScopedOrInnerSymbol], 
      refdDefns: Set[ScopedInfo]
    ):
    def ++(that: AccessInfo) = AccessInfo(
        accessed ++ that.accessed,
        mutated ++ that.mutated,
        refdDefns ++ that.refdDefns
      )
    def withoutLocals(locals: Set[ScopedOrInnerSymbol]) = AccessInfo(
        accessed -- locals,
        mutated -- locals,
        refdDefns
      )
    def intersectLocals(locals: Set[ScopedOrInnerSymbol]) = AccessInfo(
        accessed.intersect(locals),
        mutated.intersect(locals),
        refdDefns
      )
    def addAccess(l: ScopedOrInnerSymbol) = copy(accessed = accessed + l)
    def addMutated(l: ScopedOrInnerSymbol) = copy(accessed = accessed + l, mutated = mutated + l)
    def addRefdScopedObj(l: ScopedInfo) = copy(refdDefns = refdDefns + l)
    
  object AccessInfo:
    val empty = AccessInfo(Set.empty, Set.empty, Set.empty)

  object RefOfDefn:
    def unapply(p: Path): Opt[(Opt[DefinitionSymbol[?]], Bool)] = p match
      case Value.MemberRef(_, disamb) => S(S(disamb), false)
      case s @ Select(_, _) => s.symbol match
        case Some(value: DefinitionSymbol[?]) => S(S(value), true)
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
  
  /** Symbols that can appear as a direct local-like `LocalPath.Sym` in the lifter.
    *
    * More structured references, such as block members, `this`, and fields, have
    * their own `LocalPath` cases so lifting cannot accidentally treat them as
    * assignable block-local variables.
    */
  type LocalPathSymbol = LocalVarSymbol | BuiltinSymbol
  
  extension (l: LocalPathSymbol)
    def asLocalPath: LocalPath = LocalPath.Sym(l)
  extension (l: LocalVarSymbol)
    def asDefnRef: DefnRef = DefnRef.Sym(l)
  
  enum LocalPath:
    case Sym(l: LocalPathSymbol)
    case ThisPath(sym: InnerSymbol)
    case BmsRef(l: BlockMemberSymbol, d: DefinitionSymbol[?])
    /** A source local whose storage has been moved to a field while lifting.
      *
      * This is not used for arbitrary source field selections: those should
      * already have been lowered to `Select`/`AssignField`. It is specifically
      * for locals that the lifter itself makes field-backed, such as captured
      * locals inside capture classes, values passed into lifted classes, and
      * neighboring lifted object references stored as private fields.
      */
    case Field(lhs: Path, field: TermSymbol)
    
    def read(using ctx: LifterCtxNew): Path = this match
      case Sym(l) => l.asSimpleRef
      case ThisPath(sym) => sym.asThis
      case BmsRef(l, d) => l.asMemberRef(d)
      case Field(path, field) => Select(path, field.id)(S(field))(false)
      
    def asArg(using ctx: LifterCtxNew) = read.asArg
    
    def assign(value: Result, rest: Block)(using ctx: LifterCtxNew): Block = this match
      case Sym(l: Assignable) => Assign(l, value, rest)
      case Sym(l) => lastWords(s"Tried to assign to non-variable local ${l.nme}")
      case ThisPath(sym) => lastWords(s"Tried to assign to this-path ${sym.nme}")
      case BmsRef(l, d) => lastWords("Tried to assign to a BlockMemberSymbol")
      case Field(path, field) => AssignField(path, field.id, value, rest)(S(field))
      
  end LocalPath
  object LocalPath:
    /** Use when the lifter deliberately stores a captured value, passed local,
      * or neighboring lifted object in a private field of the class it is
      * currently rewriting. The map still has to be keyed by the original
      * local symbol because the lifted body mentions that original symbol;
      * the value says that reads and writes are now field selections on self.
      * Source private members should already have been lowered to selections,
      * so this is not a recovery path for arbitrary private `Value.Ref`s.
      */
    def privateSelfField(field: TermSymbol): LocalPath =
      field.owner match
      case S(owner) => Field(owner.asThis, field)
      case N => lastWords(s"tried to build a private field path for ownerless symbol ${field.nme}")
  end LocalPath
  
  enum DefnRef:
    case Sym(l: LocalVarSymbol)
    case PathRef(path: Path)
    case InScope(l: BlockMemberSymbol, d: DefinitionSymbol[?])
    case Field(isym: InnerSymbol, l: BlockMemberSymbol, d: DefinitionSymbol[?])
  
    def read(using ctx: LifterCtxNew): Path = this match
      case Sym(l) => l.asSimpleRef
      case PathRef(path) => path
      case InScope(l, d) => l.asMemberRef(d)
      case Field(isym, l, d) => Select(ctx.symbolsMap(isym).read, Tree.Ident(l.nme))(S(d))(false)
    
    def asArg(using ctx: LifterCtxNew) = read.asArg
  
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
        case Instantiate(mut, RefOfDefn(S(d), _), argss) =>
          argss.flatten.foreach(applyArg)
        // for class constructors
        case Call(RefOfDefn(S(d), _), argss) =>
          argss.flatten.foreach(applyArg)
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
            case Some(RefOfDefn(S(s: (ClassSymbol | ModuleOrObjectSymbol)), _)) =>
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
          mod.foreach(applyCompanionModule)
      
      def isFun(d: Defn) = d match
        case _: FunDefn => true
        case _ => false
      
      override def applyValue(v: Value): Unit = v match
        case RefOfDefn(S(l), _) if nestedScopes.contains(l) => data.getNode(l).obj match
          case c: ScopedObject.Class if c.isObj => ()
          // Parameterized class constructors used as naked references are constructor function
          // references, not first-class class uses. They can be lifted using a curried wrapper.
          case c: ScopedObject.ClassCtor => ()
          case c: ScopedObject.Class =>
            if !c.node.get.inModOrTopLevel then
              raise(WarningReport(
                msg"Cannot yet lift class `${l.nme}` as it is used as a first-class class." -> N :: Nil,
                N, Diagnostic.Source.Compilation
              ))
            ignored += c.cls.isym
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
  class BlockRewriter(superClass: Opt[LiftedClass])(using ctx: LifterCtxNew) extends ScopeRewriter:
    // Closure symbols that point to an initialized closure in this scope
    var activeClosures: Set[TempSymbol] = Set.empty
    // Map from block member symbols to initialized closures
    val closureMap: MutMap[DefinitionSymbol[?], TempSymbol] = MutMap.empty
    val extraLocals: MutSet[ScopedSymbol] = MutSet.empty
    
    def rewrite(b: Block) =
      val ret = applyBlock(b)
      Scoped(extraLocals, ret)
    
    // Replaces references to definitions as needed with fresh variables, and
    // returns the mapping from the symbol to the required variable. When possible,
    // it also directly rewrites Results (Calls and Instantiates).
    // Since first-class classes can't be lifted, this is where class
    // instantiations are rewritten.
    //
    // Does *not* rewrite references to non-lifted definition symbols.
    //
    // References to methods and unlifted classes nested inside classes/modules are
    // always rewritten using `this.defnName` (when accessed internally) or `object.defnName`.
    def rewriteDefnRefs(b: Block) =
      // Defn refs that need to be rewritten, and variables that need to be created
      val syms: LinkedHashMap[DefinitionSymbol[?], LocalVarSymbol] = LinkedHashMap.empty
      val extraLocals: MutSet[ScopedSymbol] = MutSet.empty

      val walker = new BlockDataTransformer(SymbolSubst.Id):
        // only scan within the block. don't traverse
        
        // Resolve references to unlifted objects
        def resolveDefnRef(d: DefinitionSymbol[?], r: RewrittenScope[?]) =
          ctx.defnsMap.get(d) match
          case Some(defnRef) => S(defnRef.read) // Found reference to unlifted definition
          case None => r.obj match
            case c: ScopedObject.Class if c.isObj =>
              ctx.symbolsMap.get(c.cls.isym).map(_.read) // Reference to an unlifted object
            case c: ScopedObject.Companion =>
              ctx.symbolsMap.get(c.clsBody.isym).map(_.read) // Reference to an unlifted module
            case _ => N

        override def applyResult(r: Result)(k: Result => Block): Block =
          r match
          case c @ Call(Value.RefLike(State.superSymbol), argss) => superClass match
            case S(sc) => applyArgss(argss): newArgs =>
              sc.rewriteSuperCall(c, newArgs)(k)
            case N => super.applyResult(c)(k)
          
          case c @ Call(RefOfDefn(S(d), _), argss) =>
            ctx.rewrittenScopes.get(d) match
              case N => super.applyResult(r)(k) // External call, or have not yet traversed that function
              case S(r) =>
                applyArgss(argss): newArgss =>
                  def join2: Block =
                    // Resolve reference to unlifted object
                    resolveDefnRef(d, r) match
                      case Some(value) => k(c.copy(fun = value, argss = newArgss.ne_!)(c.metadata).withLoc(c.toLoc))
                      case None => super.applyPath(c.fun): fun2 =>
                        // Nothing to rewrite
                        if (fun2 is c.fun) && (argss is newArgss) then k(c)
                        else k(c.copy(fun = fun2, argss = newArgss.ne_!)(c.metadata).withLoc(c.toLoc))
                  r match
                    // Call to lifted function: Rewrite using the efficient version
                    case f: LiftedFunc => k(f.rewriteCall(c, newArgss))
                    // Call to lifted class (without using `new`)
                    case ctor: RewrittenClassCtor => ctor.getRewrittenCls match
                      case cls: LiftedClass =>
                        cls.rewriteCall(c, newArgss)(k)
                      case _ => join2
                    case _ => join2
          case inst @ Instantiate(mut, RefOfDefn(S(d), _), argss) =>
            applyArgss(argss): newArgss =>
              def join =
                if argss is newArgss then inst
                else inst.copy(argss = newArgss)(inst.metadata).withLoc(inst.toLoc)
              ctx.rewrittenScopes.get(d) match
                case N => k(join)
                case S(c: LiftedClass) => c.rewriteInstantiate(inst, newArgss)(k)
                case S(r) => resolveDefnRef(d, r) match
                  case Some(value) => k(Instantiate(inst.mut, value, newArgss)(inst.metadata).withLoc(inst.toLoc))
                  case None => k(join)
          case _ => super.applyResult(r)(k)
        
        // extract the call
        override def applyPath(p: Path)(k: Path => Block): Block = p match
          case r @ RefOfDefn(S(d), isSel) => ctx.rewrittenScopes.get(d) match
            case S(f: LiftedFunc) =>
              if f.isTrivial then k(r)
              else
                val newSym = closureMap.get(d) match
                  case None =>
                    val newSym = TempSymbol(N, d.nme + "$here")
                    extraLocals.add(newSym)
                    syms.addOne(d -> newSym) // add to `syms`: this closure will be initialized in `applyBlock`
                    closureMap.addOne(d -> newSym) // add to `closureMap`: `newSym` refers to the closure and can be used later
                    newSym

                  // symbol exists, and is initialized
                  case Some(value) if activeClosures.contains(value) => value
                  // symbol exists, needs initialization
                  case Some(value) =>
                    syms.addOne(d -> value)
                    value
                k(newSym.asSimpleRef)
            
            // Naked reference to a parameterized class constructor (used as a first-class function).
            // Replace with a partially applied curried C$ wrapper.
            case S(ctor: RewrittenClassCtor) if !isSel => ctor.getRewrittenCls match
              case cls: LiftedClass if !cls.isTrivial =>
                val newSym = closureMap.get(d) match
                  case None =>
                    val newSym = TempSymbol(N, d.nme + "$here")
                    extraLocals.add(newSym)
                    syms.addOne(d -> newSym)
                    closureMap.addOne(d -> newSym)
                    newSym
                  case Some(value) if activeClosures.contains(value) => value
                  case Some(value) =>
                    syms.addOne(d -> value)
                    value
                k(newSym.asSimpleRef)
              case _ =>
                resolveDefnRef(d, ctor) match
                case Some(value) => k(value)
                case None => super.applyPath(p)(k)
            
            // Other naked references to definitions.
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
              resolveDefnRef(d, r) match
              case Some(value) => k(value)
              case None => super.applyPath(p)(k)
            case _ => super.applyPath(p)(k)
          
          case _ => super.applyPath(p)(k)
      (walker.applyBlock(b), syms.toList, extraLocals)
    end rewriteDefnRefs
    
    def applySubBlockAndReset(b: Block): Block =
      val curActive = activeClosures
      val ret = applySubBlock(b)
      activeClosures = curActive
      ret
    
    override def applyBlock(b: Block): Block =
      // extract references to definitions in the block which now may
      // need to be enriched with aux parameters
      val (rewritten, syms, extras) = rewriteDefnRefs(b)
      extraLocals.addAll(extras)
      val pre = syms.foldLeft(blockBuilder):
        case (blk, (funSym, local)) =>
          ctx.liftedScopes.get(funSym) match
            case Some(l: LiftedFunc) => blk.assign(local, l.rewriteRef)
            case _ =>
              // ClassCtor reference: look up the rewritten class ctor to get the LiftedClass
              ctx.rewrittenScopes(funSym) match
                case ctor: RewrittenClassCtor => ctor.getRewrittenCls match
                  case cls: LiftedClass => blk.assign(local, cls.rewriteCtorRef)
                  case _ => die
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
        case Assign(NoSymbol, _, _) => super.applyBlock(rewritten)
        case Assign(lhs: LocalVarSymbol, rhs, rest) => ctx.symbolsMap.get(lhs) match
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
      case r: Value.RefLike => ctx.symbolsMap.get(r.symbol) match
        case Some(value) => k(value.read)
        case _ => super.applyPath(p)(k)
      
      case _ => super.applyPath(p)(k)
  
  case class LifterResult[+T](liftedDefn: T, extraDefns: List[Lazy[Defn] | Defn])
  case class LifterCtxNew(
    liftedScopes: MutMap[LiftedSym, LiftedScope[?]] = MutMap.empty,
    rewrittenScopes: MutMap[ScopedInfo, RewrittenScope[?]] = MutMap.empty,
    var symbolsMap: Map[ValueSymbol, LocalPath] = Map.empty,
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
      : (ClsLikeDefn, List[(ValueSymbol, TermSymbol)]) =
    val nme = "Capture$" + s.nme

    val clsSym = ClassSymbol(
      Tree.DummyTypeDef(syntax.Cls),
      Tree.Ident(nme)
    )

    val cap = usedVars.reqdCaptures(s.toInfo)

    val fresh = new Uid.Symbol.State
    
    val sortedVars: Array[(ctorSyms: (local: ValueSymbol, vs: VarSymbol), param: Param, valDefn: ValDefn)] =
      cap.toArray.sortBy(_.uid).map: sym =>
        val id = fresh.nextUid.asInt
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
          varSym.asSimpleRef
        )(N, Nil)
        
        (sym -> varSym, p, vd)
    
    val defn = ClsLikeDefn(
      None, clsSym, BlockMemberSymbol(nme, Nil),
      S(ClassCtorSymbol(syntax.Fun, N, clsSym)),
      syntax.Cls,
      N,
      PlainParamList(sortedVars.iterator.map(_.param).toList) :: Nil, None, Nil, Nil, 
      Nil,
      End(),
      sortedVars.iterator.foldLeft[Block](End()):
        case (acc, (_, _, vd)) => Define(vd, acc),
      N,
      N,
    )(N, Nil)
    
    (defn, sortedVars.iterator.map(x => (x.ctorSyms.local, x.valDefn.tsym)).toList)
  
  class ScopeRewriter(using ctx: LifterCtxNew) extends BlockTransformerShallow(SymbolSubst.Id):
    
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
        val blk = applyRewrittenScope(ctx.rewrittenScopes(l.label)) match
          case b: Block => b
          case _ => die
        val rst2 = applySubBlock(l.rest)
        if (blk is l.body) && (rst2 is l.rest) then l else l.copy(body = blk, rest = rst2)
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
        
        k(newCls.copy(companion = newComp)(newCls.configOverride, newCls.annotations))
      case _ => super.applyDefn(defn)(k)

  /**
    * Represents a scoped object that will be rewritten to reference the lifted version of objects and variables.
    */
  sealed abstract class RewrittenScope[T](val obj: TScopedObject[T]):
    val node = obj.node.get
    
    protected final val thisCapturedLocals = usedVars.reqdCaptures(obj.toInfo)
    val hasCapture = !thisCapturedLocals.isEmpty
    
    // These are lazy, because we don't necessarily need a captrue 
    private final lazy val captureInfo: (ClsLikeDefn, List[(ValueSymbol, TermSymbol)]) = createCaptureCls(obj)
    
    lazy val captureClass = captureInfo._1
    lazy val captureMap = captureInfo._2.toMap
    lazy val liftedObjsMap: Map[InnerSymbol, LocalPath]
    
    lazy val capturePath: Path
    
    protected def rewriteImpl: LifterResult[T]
    
    protected final def instantiateCapture: Instantiate =
      if hasCapture then
        Instantiate(
          true,
          captureClass.sym.asMemberRef(captureClass.isym),
          captureInfo._2.map(
            (sym, _) => sym.asPath.asArg) :: Nil
        )(InstantiateMetadata.empty)
      else lastWords("tried to instantiate an empty capture")
    
    protected final def addExtraSyms(b: Block, captureSym: LocalVarSymbol, objSyms: Iterable[ScopedSymbol]): Block =
      if hasCapture then
        Scoped(
          objSyms.toSet + captureSym,
          Assign(captureSym, instantiateCapture, b)
        )
      else
        Scoped(objSyms.toSet, b)
    
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
    protected final def pathsFromThisObj: Map[ScopedOrInnerSymbol, LocalPath] =
      // Remove child BlockMemberSymbols; we will use their definition symbols instead
      
      // Locals introduced by this object
      val fromThisObj: Map[ScopedOrInnerSymbol, LocalPath] = node.localsWithoutBms
        .flatMap: s =>
          s match
            case s: BlockMemberSymbol => N
            case s: LocalPathSymbol => S(s -> s.asLocalPath)
            case s: InnerSymbol => S(s -> LocalPath.ThisPath(s))
        .toMap
      // Locals introduced by this object that are inside this object's capture
      val fromCap: Map[ScopedOrInnerSymbol, LocalPath] = thisCapturedLocals
        .map: s =>
          val tSym = captureMap(s)
          s -> LocalPath.Field(capturePath, tSym)
        .toMap
      // Inner symbols of nested modules and objects
      val isyms: Map[ScopedOrInnerSymbol, LocalPath] = node.children
        .collect:
          case ScopeNode(obj = c: ScopedObject.Companion) =>
            c.clsBody.isym -> LocalPath.BmsRef(c.bsym, c.clsBody.isym)
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
    
    // Defn refs from ignored defns (including child defns of modules)
    protected val defnPathsFromThisObj: Map[DefinitionSymbol[?], DefnRef] =
      node.children.filter:
        case s @ ScopeNode(obj = r: ScopedObject.Class) if r.isObj => false
        case s @ ScopeNode(obj = r: ScopedObject.Func) if r.isMethod.isDefined => false
        case _ => true
      .collect:
        case s @ ScopeNode(obj = r: ScopedObject.Referencable[?]) if !s.isLifted => 
          val path = r.owner match
            case Some(isym) => DefnRef.Field(isym, r.bsym, r.sym)
            case None => DefnRef.InScope(r.bsym, r.sym)
          r.sym -> path
      .toMap
    
    lazy val defnPaths: Map[DefinitionSymbol[?], DefnRef] = defnPathsFromThisObj
    
    lazy val symbolsMap: Map[ScopedOrInnerSymbol, LocalPath] = pathsFromThisObj
  
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
    final val passedSyms: Set[ScopedOrInnerSymbol] = reqPassedSymbols
    /** Maps locals to the scope where they were defined. */
    final val capturesOrigin: Map[ValueSymbol, ScopedInfo] = captures.toMap
    /** Scopes whose captures this object requires. */
    final val reqCaptures: Set[ScopedInfo] = captures.map(_._2)
    /**
      * Neighbouring objects that this definition may lose access to
      * once lifted, referenced by their *definition symbol*.
      */
    final val reqDefns = node.reqCaptureObjs
      .map(_.sym)
      .toSet.intersect(refdDSyms)
    
    /** Maps directly passed locals to the path representing that local within this object. */
    protected val passedSymsMap: Map[ValueSymbol, LocalPath]
    /** Maps scopes to the path representing their captures within this object. */
    protected val capSymsMap: Map[ScopedInfo, Path]
    /** Maps definition symbols to the path representing that definition. */
    protected val passedDefnsMap: Map[DefinitionSymbol[?], DefnRef]
    
    protected lazy val capturesOrdered: List[ScopedInfo] = reqCaptures.toList.sorted
    protected final lazy val passedSymsOrdered: List[ValueSymbol] = reqPassedSymbols.toList.sortBy(_.uid)
    protected final lazy val reqDefnsOrdered: List[DefinitionSymbol[?]] = reqDefns.toList.sortBy(_.uid)
    
    override lazy val capturePaths: Map[ScopedInfo, Path] =
      if thisCapturedLocals.isEmpty then capSymsMap
      else capSymsMap + (obj.toInfo -> capturePath)
    
    // Note: we have to make this lazy because Scala's type system is unsound and
    // lets you access the above two fields before they are initialized
    // (since this constructor runs before the child classes' constructors)
    
    /** Maps symbols to the path representing that local within this object.
      * Includes locals defined by this object's parents, and this object's own defined locals.
      */
    override lazy val symbolsMap: Map[ScopedOrInnerSymbol, LocalPath] = 
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
              s -> LocalPath.Field(capSym, tSym)
        .toMap
      fromParents ++ pathsFromThisObj
    
    override lazy val defnPaths: Map[DefinitionSymbol[?], DefnRef] =
      val fromParents = reqDefns
        .map: s =>
          s -> passedDefnsMap(s)
        .toMap
      defnPathsFromThisObj ++ fromParents
    
    final def formatArgs: List[Arg] =
      val defnsArgs = reqDefnsOrdered.map(d => ctx.defnsMap(d).asArg)
      val captureArgs = capturesOrdered.map(c => ctx.capturesMap(c).asArg)
      val localArgs = passedSymsOrdered.map(l => ctx.symbolsMap(l).asArg)
      defnsArgs ::: captureArgs ::: localArgs
    
    final lazy val liftedFromStagedModule: Bool =
      node.allAncestors.exists:
        case ScopeNode(ScopedObject.Companion(comp, _), _, _) => comp.isStaged
        case _ => false
  
  /* MIXINS */
  
  /**
    * A rewritten scope with a generic VarSymbol capture symbol.
    */
  sealed trait GenericRewrittenScope[T] extends RewrittenScope[T]:
    lazy val captureSym = VarSymbol(Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath = captureSym.asSimpleRef
    protected val liftedObjsOrdered: List[InnerSymbol] = node.liftedObjSyms.toList.sortBy(_.uid)
    protected val liftedObjsSyms: Map[InnerSymbol, VarSymbol] = liftedObjsOrdered.map: s =>
        s -> VarSymbol(Tree.Ident(s.nme + "$"))
      .toMap
    override lazy val liftedObjsMap: Map[InnerSymbol, LocalPath] = liftedObjsSyms.map:
      case k -> v => k -> v.asLocalPath
    
    protected def addExtraSyms(b: Block): Block = addExtraSyms(b, captureSym, liftedObjsSyms.values)
    
  /**
    * A rewritten scope with a TermSymbol capture symbol.
    */
  sealed trait ClsLikeRewrittenScope[T](sym: InnerSymbol) extends RewrittenScope[T]:
    lazy val captureSym = TermSymbol(syntax.ImmutVal, S(sym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath = Select(Value.This(sym), captureSym.id)(S(captureSym))(false)
    protected val liftedObjsOrdered: List[InnerSymbol] = node.liftedObjSyms.toList.sortBy(_.uid)
    protected val liftedObjsSyms: Map[InnerSymbol, TermSymbol] = liftedObjsOrdered.map: s =>
        s -> TermSymbol(syntax.ImmutVal, S(sym), Tree.Ident(s.nme + "$"))
      .toMap
    override lazy val liftedObjsMap: Map[InnerSymbol, LocalPath] = liftedObjsSyms.map:
      case k -> v => k -> LocalPath.privateSelfField(v)
    protected def appendCaptureField(privFields: List[TermSymbol]) =
      if hasCapture then captureSym :: privFields else privFields
    protected def rewriteMethods(node: ScopeNode, methods: List[FunDefn])(using ctx: LifterCtxNew) =
      val mtds = node.children
        .map: c =>
          ctx.rewrittenScopes(c.obj.toInfo)
        .collect:
          case r: RewrittenFunc if r.obj.isMethod.isDefined => r 
      val (liftedMtds, extras) = mtds.map(liftNestedScopes).unzip(using l => (l.liftedDefn, l.extraDefns))
      LifterResult(liftedMtds, extras.flatten)
    protected final def initCaptureField(b: Block): Block =
      if hasCapture then AssignField(sym.asThis, captureSym.id, instantiateCapture, b)(S(captureSym))
      else b
  
  // some helpers
  private def dupParam(p: Param): Param = p.copy(sym = VarSymbol(Tree.Ident(p.sym.nme)))
  private def dupParams(plist: List[Param]): List[Param] = plist.map(dupParam)
  private def dupParamList(plist: ParamList): ParamList =
    plist.copy(params = dupParams(plist.params), restParam = plist.restParam.map(dupParam))
  
  /* CONCRETE IMPLS */
  
  class RewrittenScopedBlock(override val obj: ScopedObject.ScopedBlock)(using ctx: LifterCtxNew) extends RewrittenScope[Block](obj) with GenericRewrittenScope[Block]:
    override def rewriteImpl: LifterResult[Block] =
      val rewriter = new BlockRewriter(N)
      
      // Remove symbols belonging to lifted scopes
      val liftedChildSyms = node.allChildNodes.collect:
        case s @ ScopeNode(obj = l: ScopedObject.Liftable[?]) if s.isLifted => l.defn.sym
      
      val syms = if obj.block.syms.forall(!liftedChildSyms.contains(_))
        then obj.block.syms else obj.block.syms.toSet -- liftedChildSyms
      val rewritten = rewriter.rewrite(obj.block.body)
      val withCapture = addExtraSyms(rewritten)
      if (syms is obj.block.syms) && (withCapture is obj.block.body) then
        LifterResult(obj.block, Nil)
      else
        LifterResult(Scoped(syms, withCapture), rewriter.extraDefns.toList)
  
  class RewrittenLoop(override val obj: ScopedObject.Loop)(using ctx: LifterCtxNew) extends RewrittenScope[Block](obj) with GenericRewrittenScope[Block]:
    override def rewriteImpl: LifterResult[Block] =
      val rewriter = new BlockRewriter(N)
      
      val rewritten = rewriter.rewrite(obj.body)
      val withCapture = addExtraSyms(rewritten)
      LifterResult(withCapture, rewriter.extraDefns.toList)
  
  class RewrittenFunc(override val obj: ScopedObject.Func)(using ctx: LifterCtxNew) extends RewrittenScope[FunDefn](obj) with GenericRewrittenScope[FunDefn]:
    override def rewriteImpl: LifterResult[FunDefn] =
      val rewriter = new BlockRewriter(N)
      
      val rewritten = rewriter.rewrite(obj.fun.body)
      val withCapture = addExtraSyms(rewritten)
      LifterResult(obj.fun.copy(body = withCapture)(obj.fun.configOverride, obj.fun.annotations), rewriter.extraDefns.toList)
  
  class RewrittenClassCtor(override val obj: ScopedObject.ClassCtor)(using ctx: LifterCtxNew) extends RewrittenScope[Unit](obj):
    override lazy val capturePath: Path = lastWords("tried to create a capture class for a class ctor")
    override lazy val liftedObjsMap: Map[InnerSymbol, LocalPath] = lastWords("tried to create obj syms for a class ctor")

    override protected def rewriteImpl: LifterResult[Unit] = LifterResult((), Nil) // dummy
    
    def getRewrittenCls = ctx.rewrittenScopes(obj.cls.isym)
  
  class RewrittenValDef(override val obj: ScopedObject.ValDef)(using ctx: LifterCtxNew) extends RewrittenScope[ValDefn](obj):
    override lazy val capturePath: Path = lastWords("tried to create a capture class for a val defn")
    override lazy val liftedObjsMap: Map[InnerSymbol, LocalPath] = lastWords("tried to create obj syms for a val defn")

    override protected def rewriteImpl: LifterResult[ValDefn] = die // dummy
  
  class RewrittenClass(override val obj: ScopedObject.Class)(using ctx: LifterCtxNew)
      extends RewrittenScope[ClsLikeDefn](obj)
      with ClsLikeRewrittenScope[ClsLikeDefn](obj.cls.isym):
    
    private val captureSym = TermSymbol(syntax.ImmutVal, S(obj.cls.isym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath: Path = Select(Value.This(obj.cls.isym), captureSym.id)(S(captureSym))(false)
    
    override def rewriteImpl: LifterResult[ClsLikeDefn] =
      val liftedSuper = obj.cls.parentPath.flatMap:
        case RefOfDefn(S(dSym),_) => ctx.rewrittenScopes.get(dSym).collect:
          case c: LiftedClass => c
        case _ => N
      
      val rewriterCtor = new BlockRewriter(liftedSuper)
      val rewriterPreCtor = new BlockRewriter(liftedSuper)
      val rewrittenCtor = rewriterCtor.rewrite(obj.cls.ctor)
      val rewrittenPrector = rewriterPreCtor.rewrite(obj.cls.preCtor)
      val ctorWithCap = initCaptureField(rewrittenCtor)
      val rewrittenPrivateFields = appendCaptureField(liftedObjsOrdered.map(liftedObjsSyms) ::: obj.cls.privateFields)
      
      val LifterResult(newMtds, extras) = rewriteMethods(node, obj.cls.methods)
      if (obj.cls.ctor is ctorWithCap) && (obj.cls.preCtor is rewrittenPrector) &&
          (obj.cls.privateFields is rewrittenPrivateFields) && (obj.cls.methods is newMtds)
      then LifterResult(obj.cls, Nil)
      else
        val newCls = obj.cls.copy(
          ctor = ctorWithCap,
          preCtor = rewrittenPrector,
          privateFields = rewrittenPrivateFields,
          methods = newMtds,
        )(obj.cls.configOverride, obj.cls.annotations)
        LifterResult(newCls, rewriterCtor.extraDefns.toList ::: rewriterPreCtor.extraDefns.toList ::: extras)
      

  class RewrittenCompanion(override val obj: ScopedObject.Companion)(using ctx: LifterCtxNew)
      extends RewrittenScope[ClsLikeBody](obj)
      with ClsLikeRewrittenScope[ClsLikeBody](obj.clsBody.isym):
    
    private val captureSym = TermSymbol(syntax.ImmutVal, S(obj.clsBody.isym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath: Path = Select(Value.This(obj.clsBody.isym), captureSym.id)(S(captureSym))(false)
      
    override def rewriteImpl: LifterResult[ClsLikeBody] =
      val rewriterCtor = new BlockRewriter(N)
      val rewrittenCtor = rewriterCtor.rewrite(obj.clsBody.ctor)
      val ctorWithCap = initCaptureField(rewrittenCtor)
      val rewrittenPrivateFields = appendCaptureField(liftedObjsOrdered.map(liftedObjsSyms) ::: obj.clsBody.privateFields)
      val LifterResult(newMtds, extras) = rewriteMethods(node, obj.clsBody.methods)
      if (obj.clsBody.ctor is ctorWithCap) && (obj.clsBody.privateFields is rewrittenPrivateFields) &&
          (obj.clsBody.methods is newMtds)
      then LifterResult(obj.clsBody, Nil)
      else
        val newComp = obj.clsBody.copy(
          ctor = ctorWithCap,
          privateFields = rewrittenPrivateFields,
          methods = newMtds
        )
        LifterResult(newComp, rewriterCtor.extraDefns.toList ::: extras)
  
  class LiftedFunc(override val obj: ScopedObject.Func)(using ctx: LifterCtxNew) extends LiftedScope[FunDefn](obj) with GenericRewrittenScope[FunDefn]:
    private val passedSymsMap_ : Map[ValueSymbol, VarSymbol] = passedSymsOrdered.map: s =>
        s -> VarSymbol(Tree.Ident(s.nme))
      .toMap
    private val capSymsMap_ : Map[ScopedInfo, VarSymbol] = capturesOrdered.map: i =>
        val nme = data.getNode(i).obj.nme
        i -> VarSymbol(Tree.Ident(nme + "$cap"))
      .toMap
    private val defnSymsMap_ : Map[DefinitionSymbol[?], VarSymbol] = reqDefnsOrdered.sortBy(_.uid).map: i =>
        val nme = data.getNode(i).obj.nme
        i -> VarSymbol(Tree.Ident(nme + "$"))
      .toMap
    
    override protected val passedSymsMap = passedSymsMap_.view.mapValues(_.asLocalPath).toMap
    override protected val capSymsMap = capSymsMap_.view.mapValues(s => s.asSimpleRef).toMap
    override protected val passedDefnsMap = defnSymsMap_.view.mapValues(_.asDefnRef).toMap
    
    val auxParams: List[Param] =
      (reqDefnsOrdered.map(defnSymsMap_) ::: capturesOrdered.map(capSymsMap_) ::: passedSymsOrdered.map(passedSymsMap_))
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
      val rewriter = new BlockRewriter(N)
      val newBod = rewriter.rewrite(fun.body)
      val withCapture = addExtraSyms(newBod)
      val newDefn = fun.copy(owner = N, sym = mainSym, dSym = mainDsym, params = newPlists, body = withCapture)(
        fun.configOverride,
        if liftedFromStagedModule && !fun.isStaged then Annot.Modifier(Keyword.`staged`) :: fun.annotations
        else fun.annotations)
      LifterResult(newDefn, rewriter.extraDefns.toList)
    
    // Definition with the auxiliary parameters as a new first parameter list.
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
          val tail = Arg(S(SpreadKind.Eager), value.asSimpleRef) :: Nil
          syms.foldLeft(tail):
            case (acc, sym) => Arg(N, sym.asSimpleRef) :: acc
        case None => syms.map(s => Arg(N, s.asSimpleRef))
      
      val call = Call(fun.sym.asMemberRef(fun.dSym), args ne_:: Nil)(CallMetadata.mlsFunWithEffect)
      val bod = Return(call)
      
      FunDefn(
        N,
        auxSym,
        auxDsym,
        newPlists,
        bod
      )(N, Annot.Inline :: fun.annotations)
    
    private val aux = Lazy[Defn](mkAuxDefn)
    
    def rewriteCall(c: Call, argss: NELs[List[Arg]])(using ctx: LifterCtxNew): Call =
      if isTrivial then
        if argss is c.argss then c
        else c.copy(argss = argss)(c.metadata).withLocOf(c)
      else
        Call.raw(
          mainSym.asMemberRef(mainDsym),
          (formatArgs ::: argss.head) ne_:: argss.tail
        )(c.metadata.copy(isMlsFun = true)).withLoc(c.toLoc)
    
    def rewriteRef(using ctx: LifterCtxNew): Call =
      if isTrivial then lastWords("tried to rewrite a ref to a trivial function")
      aux.force // forces computation
      Call.raw(
        auxSym.asMemberRef(auxDsym),
        formatArgs ne_:: Nil
      )(CallMetadata.defaultMlsFun)
    
    def rewriteImpl: LifterResult[FunDefn] =
      val LifterResult(lifted, extra) = mkFlattenedDefn
      if isTrivial then LifterResult(lifted, extra)
      else LifterResult(lifted, aux :: extra)
  class LiftedClass(override val obj: ScopedObject.Class)(using ctx: LifterCtxNew)
      extends LiftedScope[ClsLikeDefn](obj)
      with ClsLikeRewrittenScope[ClsLikeDefn](obj.cls.isym):
    
    private val captureSym = TermSymbol(syntax.ImmutVal, S(obj.cls.isym), Tree.Ident(obj.nme + "$cap"))
    override lazy val capturePath: Path = Select(Value.This(obj.cls.isym), captureSym.id)(S(captureSym))(false)
    
    private val passedSymsMap_ : Map[ValueSymbol, (vs: VarSymbol, ts: TermSymbol)] = passedSymsOrdered.map: s =>
        s ->
          (
            VarSymbol(Tree.Ident(s.nme)),
            TermSymbol(syntax.LetBind, S(obj.cls.isym), Tree.Ident(s.nme))
          )
      .toMap
    private val capSymsMap_ : Map[ScopedInfo, (vs: VarSymbol, ts: TermSymbol)] = capturesOrdered.map: i =>
        val nme = data.getNode(i).obj.nme + "$cap"
        i ->
          (
            VarSymbol(Tree.Ident(nme)),
            TermSymbol(syntax.LetBind, S(obj.cls.isym), Tree.Ident(nme))
          )
      .toMap
    private val defnSymsMap_ : Map[DefinitionSymbol[?], (vs: VarSymbol, ts: TermSymbol)] = reqDefnsOrdered.map: i =>
        i -> 
          (
            VarSymbol(Tree.Ident(i.nme + "$")),
            TermSymbol(syntax.LetBind, S(obj.cls.isym), Tree.Ident(i.nme + "$"))
          )
      .toMap
    
    private lazy val extraPrivSyms: List[TermSymbol] = 
      liftedObjsOrdered.map(liftedObjsSyms)
      ::: reqDefnsOrdered.map(defnSymsMap_(_).ts)
      ::: capturesOrdered.map(capSymsMap_(_).ts)
      ::: passedSymsOrdered.map(passedSymsMap_(_).ts)
    
    override protected val passedSymsMap = passedSymsMap_.view.mapValues(x => LocalPath.privateSelfField(x.ts)).toMap
    override protected val capSymsMap = capSymsMap_.view.mapValues(x => LocalPath.privateSelfField(x.ts).read).toMap
    override protected val passedDefnsMap = defnSymsMap_.view.mapValues(x => DefnRef.PathRef(LocalPath.privateSelfField(x.ts).read)).toMap

    private val passedSymsMapVs = passedSymsMap_.view.mapValues(x => LocalPath.Sym(x.vs)).toMap
    private val capSymsMapVs = capSymsMap_.view.mapValues(x => LocalPath.Sym(x.vs).read).toMap
    private val passedDefnsMapVs = defnSymsMap_.view.mapValues(x => DefnRef.PathRef(LocalPath.Sym(x.vs).read)).toMap
    
    val auxParams: List[Param] =
      (reqDefnsOrdered.map(x => defnSymsMap_(x).vs)
        ::: capturesOrdered.map(x => capSymsMap_(x).vs)
        ::: passedSymsOrdered.map(x => passedSymsMap_(x).vs))
      .map(Param.simple(_))
    val auxParamList = PlainParamList(auxParams)
    
    // Whether this can be lifted without the need to pass extra parameters.
    val isTrivial = auxParams.isEmpty
    
    val cls = obj.cls
    
    val flattenedSym = BlockMemberSymbol(obj.cls.sym.nme + "$", Nil, true)
    val flattenedDSym = TermSymbol.fromFunBms(flattenedSym, N)
    
    // Contains *all* parameters, and applies them all at once in a single `Instantiate`
    def mkFlattenedDefn: FunDefn =
      // Symbols for the aux parameter list
      val auxSyms = auxParams.map(p => VarSymbol(Tree.Ident(p.sym.nme)))
      val auxParamListLocal = PlainParamList(auxSyms.map(Param.simple(_)))
      
      val dupedClsAuxParams = cls.auxParams.map(dupParamList(_))
      val dupedMainOpt = cls.paramsOpt.map(dupParamList(_))
      val clsParamLists = dupedMainOpt match
        case Some(dupedMain) => dupedMain :: dupedClsAuxParams
        case None => dupedClsAuxParams
      // Contains aux param list
      val allParamLists = auxParamListLocal :: clsParamLists
      
      // Uses the symbols from pl1.
      def applyPlToPl(pl1: ParamList, pl2: ParamList): List[Arg] = (pl1.restParam, pl2.restParam) match
        case (S(rp), S(_)) => pl1.params.foldRight(Arg(S(SpreadKind.Eager), rp.sym.asSimpleRef) :: Nil)((p, ls) => p.sym.asSimpleRef.asArg :: ls)
        case (N, N) => pl1.paramSyms.map(s => s.asSimpleRef.asArg)
        case _ => die
      
      // If class has a main param list, the aux list comes after it
      inline def appliedMainAndAuxArgs(rest: List[List[Arg]]): List[List[Arg]] = (dupedMainOpt, cls.paramsOpt) match
        case (S(dupedMain), S(clsParams)) => applyPlToPl(dupedMain, clsParams) :: applyPlToPl(auxParamListLocal, auxParamList) :: rest
        case (N, N) => applyPlToPl(auxParamListLocal, auxParamList) :: rest
        case _ => die
      
      val appliedClsAuxArgs = (dupedClsAuxParams zip cls.auxParams).map(applyPlToPl)
      
      // main :: aux :: clsAuxArgs
      // or aux :: clsAuxArgs
      val argsList = appliedMainAndAuxArgs(appliedClsAuxArgs)
      
      val ref = obj.cls.sym.asMemberRef(obj.cls.isym)
      val inst = Instantiate(false, ref, argsList)(InstantiateMetadata.empty)
      val bod = Return(inst)
      
      FunDefn(N, flattenedSym, flattenedDSym, allParamLists, bod)(N, annotations = Nil)
    
    private val flat = Lazy[Defn](mkFlattenedDefn)
    
    def instObject = Instantiate(false, cls.sym.asMemberRef(cls.isym), formatArgs :: Nil)(InstantiateMetadata.empty)
    
    // Rewrite a naked reference to a parameterized class constructor.
    // Returns a Call to the curried C$ wrapper partially applied with formatArgs.
    def rewriteCtorRef: Call =
      if isTrivial then lastWords("tried to rewrite a ref to a trivial class ctor")
      flat.force
      Call.raw(
        flattenedSym.asMemberRef(flattenedDSym),
        formatArgs ne_:: Nil
      )(CallMetadata.defaultMlsFun)
    
    def rewriteInstantiate(inst: Instantiate, argss: List[List[Arg]])(k: Result => Block): Block =
      if obj.isObj then lastWords("tried to rewrite instantiate for an object")
      val path = cls.sym.asMemberRef(cls.isym)
      if isTrivial then
        if (inst.cls === path) && (inst.argss is argss) then k(inst)
        else k(inst.copy(cls = path, argss = argss)(inst.metadata).withLocOf(inst))
      else if cls.paramsOpt.isEmpty && cls.auxParams.isEmpty then
        // Paramless class: lifter args go directly into the Instantiate constructor
        k(Instantiate(inst.mut, path, (formatArgs ::: argss.head) :: argss.tail)(inst.metadata).withLoc(inst.toLoc))
      else
        // Parameterized class: use Instantiate with original args + lifter args inserted after the first list
        k(Instantiate(inst.mut, path, argss.head :: formatArgs :: argss.tail)(inst.metadata).withLoc(inst.toLoc))
    
    def rewriteSuperCall(superCall: Call, argss: List[List[Arg]])(k: Result => Block): Block =
      if obj.isObj then lastWords("tried to rewrite instantiate for an object")
      if isTrivial then k(superCall)
      else if cls.paramsOpt.isEmpty && cls.auxParams.isEmpty then
        // Paramless class: lifter args go directly into the Instantiate constructor
        k(Call(superCall.fun, (formatArgs ::: argss.head) ne_:: argss.tail)(CallMetadata.defaultMlsFun).withLoc(superCall.toLoc))
      else
        // Parameterized class: use Instantiate with original args + lifter args inserted after the first list
        k(Call(superCall.fun, argss.head ne_:: formatArgs ne_:: argss.tail)(CallMetadata.mlsFunWithEffect).withLoc(superCall.toLoc))
    
    def rewriteCall(c: Call, argss: NELs[List[Arg]])(k: Result => Block)(using ctx: LifterCtxNew): Block =
      if obj.isObj then lastWords("tried to rewrite instantiate for an object")
      val path = cls.sym.asMemberRef(cls.isym)
      val clsParamLists = cls.paramsOpt.toList ::: cls.auxParams
      def callFlattenedCtor: Call =
        flat.force
        Call.raw(
          flattenedSym.asMemberRef(flattenedDSym),
          (formatArgs :: argss).ne_!
        )(c.metadata.copy(isMlsFun = true, mayRaiseEffects = false)).withLoc(c.toLoc)
      if isTrivial then
        if c.argss is argss then k(c)
        else k(c.copy(argss = argss)(c.metadata).withLocOf(c))
      else if cls.paramsOpt.isEmpty && cls.auxParams.isEmpty then
        // Paramless class: unreachable
        lastWords("Call to paramless class")
      else if argss.lengthCompare(clsParamLists.length) === 0 then
        // Parameterized class: Same as Instantiate case
        k(Instantiate(false, path, argss.head :: formatArgs :: argss.tail)(InstantiateMetadata(c.metadata.annotations)).withLoc(c.toLoc))
      else
        // Unsaturated constructor calls must remain ordinary curried calls to
        // the lifted wrapper; only saturated constructor applications may
        // become Instantiate nodes after the global class-param flattening pass.
        k(callFlattenedCtor)
    
    def rewriteImpl: LifterResult[ClsLikeDefn] =
      val liftedSuper = obj.cls.parentPath.flatMap:
        case RefOfDefn(S(dSym),_) => ctx.rewrittenScopes.get(dSym).collect:
          case c: LiftedClass => c
        case _ => N
      
      val rewriterCtor = new BlockRewriter(liftedSuper)
      val rewriterPreCtor = new BlockRewriter(liftedSuper)
      val rewrittenCtor = rewriterCtor.rewrite(obj.cls.ctor)
      
      // We must reference the VarSymbols in the PreCtor
      // manually add them for now.
      val rewrittenPreCtor = runAndPreserveCtx:
        val fromParents = reqSymbols
          .map: s =>
            passedSymsMapVs.get(s) match
              // The symbol is passed directly
              case Some(value) => s -> value
              // The symbol is passed in a capture
              case None =>
                val fromScope = capturesOrigin(s)
                val capSym = capSymsMapVs(fromScope)
                val tSym = ctx.rewrittenScopes(fromScope).captureMap(s)
                s -> LocalPath.Field(capSym, tSym)
          .toMap
        ctx.symbolsMap ++= fromParents
        ctx.capturesMap ++= capSymsMapVs
        ctx.defnsMap ++= passedDefnsMapVs
        rewriterPreCtor.rewrite(obj.cls.preCtor)
      
      val ctorWithCap = initCaptureField(rewrittenCtor)
      
      // Assign passed locals and captures
      val ctorWithPassed = passedSymsOrdered.foldRight(ctorWithCap):
        case (sym, acc) =>
          val (vs, ts) = passedSymsMap_(sym)
          LocalPath.privateSelfField(ts).assign(vs.asPath, acc)
      val ctorWithCaps = capturesOrdered.foldRight(ctorWithPassed):
        case (sym, acc) =>
          val (vs, ts) = capSymsMap_(sym)
          LocalPath.privateSelfField(ts).assign(vs.asPath, acc)
      val ctorWithDefns = reqDefnsOrdered.foldRight(ctorWithCaps):
        case (sym, acc) =>
          val (vs, ts) = defnSymsMap_(sym)
          LocalPath.privateSelfField(ts).assign(vs.asPath, acc)
      
      val newAuxList = 
        if isTrivial then cls.auxParams
        else auxParamList :: cls.auxParams
      
      val LifterResult(newMtds, extras) = rewriteMethods(node, obj.cls.methods)
      
      val newCls = obj.cls.copy(
        owner = N,
        k = syntax.Cls, // turn objects into classes
        ctor = ctorWithDefns,
        preCtor = rewrittenPreCtor,
        privateFields = appendCaptureField(extraPrivSyms ::: obj.cls.privateFields),
        methods = newMtds,
        auxParams = newAuxList
      )(obj.cls.configOverride,
        if liftedFromStagedModule && !obj.cls.isStaged then Annot.Modifier(Keyword.`staged`) :: obj.cls.annotations
        else obj.cls.annotations)
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
    case o: ScopedObject.ValDef => RewrittenValDef(o)
  
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
    
  inline def runAndPreserveCtx[T](thunk: => T)(using ctx: LifterCtxNew): T =
    val curSyms = ctx.symbolsMap
    val curCaptures = ctx.capturesMap
    val curDefns = ctx.defnsMap
    val ret = thunk
    ctx.symbolsMap = curSyms
    ctx.capturesMap = curCaptures
    ctx.defnsMap = curDefns
    ret

  def liftNestedScopes[T](r: RewrittenScope[T])(using ctx: LifterCtxNew): LifterResult[T] = runAndPreserveCtx:
    if r.node.isLifted then
      ctx.symbolsMap = Map.empty
      ctx.capturesMap = Map.empty
      ctx.defnsMap = Map.empty
    liftNestedScopesImpl(r)
  
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
