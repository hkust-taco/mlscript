package hkmc2
package semantics

import scala.collection.mutable.{Buffer, Set as MutSet}

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.utils.Scope
import hkmc2.utils.Scope.scope
import hkmc2.document.*
import hkmc2.document.Document.*

import Elaborator.State
import hkmc2.typing.Type
import hkmc2.semantics.Elaborator.{Ctx, ctx}
import hkmc2.Message.MessageContext
import hkmc2.codegen.Erasure


final case class QuantVar(sym: VarSymbol, ub: Opt[Term], lb: Opt[Term])

/** Each annotation occurrence owns its source span, including marker annotations.
  * The auxiliary location does not affect equality or matching by annotation kind.
  */
enum Annot extends Located:
  val toLoc: Opt[Loc]

  case JsSymbol(key: SymbolKey)(val toLoc: Opt[Loc])
  case Fresh()(val toLoc: Opt[Loc])
  case Untyped()(val toLoc: Opt[Loc])
  case Modifier(mod: Keyword)(val toLoc: Opt[Loc])
  case Trm(trm: Term)(val toLoc: Opt[Loc])
  // NOTE: The presence of TailRec and TailCall annotations does not affect whether a function is optimized or not;
  // it only affects whether a warning is thrown if the function/call is not actually tail-recursive.
  case TailRec()(val toLoc: Opt[Loc])
  case TailCall()(val toLoc: Opt[Loc])
  case Inline()(val toLoc: Opt[Loc])
  case NoInline()(val toLoc: Opt[Loc])
  case Generator()(val toLoc: Opt[Loc])
  case Async()(val toLoc: Opt[Loc])
  case RaiseEffects()(val toLoc: Opt[Loc])
  // Whether the function is guaranteed to not raise effects.
  case Pure()(val toLoc: Opt[Loc])
  // Buffered classes expose generated allocation and access methods on the class value.
  case Bufferable(keepInstances: Bool)(val toLoc: Opt[Loc])
  case Config(modify: hkmc2.Config => hkmc2.Config)(val toLoc: Opt[Loc])
  case Debug(modify: hkmc2.Config => hkmc2.Config)(val toLoc: Opt[Loc])
  // Marks if a function or lambda is one-shot, i.e. called at most once.
  // Functions with multiple parameter lists are considered here as a chain of
  // function values. `whichParamList` is the zero-based index of the parameter
  // list whose corresponding function value is one-shot.
  // For example, on `fun f(a)(b)`,
  // - its list of annotations containing `Affine(0)` says that `f` is one-shot;
  // - its list of annotations containing `Affine(1)` says that
  //   each function value produced by `f(a)` is one-shot;
  // - its list of annotations containing both `Affine(0)` and `Affine(1)` says that
  //   `f` is one-shot and each function value produced by `f(a)` is also one-shot.
  case Affine(whichParamList: Int)(val toLoc: Opt[Loc])
  
  def symbol: Opt[Symbol] = this match
    case Trm(trm) => trm.symbol
    case _ => N
  
  def subTerms: Vector[Term] = this match
    case Trm(trm) => Vector.single(trm)
    case JsSymbol(key) => Vector.single(key.term)
    case Fresh() | _: Modifier | Untyped() | TailRec() | TailCall() | Inline() | NoInline()
      | Generator() | Async() | RaiseEffects() | Pure() | _: Bufferable | _: Config | _: Debug | _: Affine => Vector.empty
  
  def show(using Scope, ShowCfg, Raise): Document = this match
    case JsSymbol(key) => doc"@jsSymbol(${key.term.show})"
    case Fresh() => doc"@annotations.fresh"
    case Untyped() => doc"@untyped"
    case Inline() => doc"@inline"
    case NoInline() => doc"@noInline"
    case Generator() => doc"@generator"
    case Async() => doc"@async"
    case RaiseEffects() => doc"@raiseEffects"
    case TailRec() => doc"@tailrec"
    case TailCall() => doc"@tailcall"
    case Affine(n) => doc"@affine($n)"
    case Modifier(mod) => doc"@${mod.name}"
    case Pure() => doc"@pure"
    case Bufferable(keepInstances) => if keepInstances then doc"@bufferable" else doc"@buffered"
    case Trm(trm) => doc"@${trm.show}"
    case Config(_) => doc"@config(...)"
    case Debug(_) => doc"@dbg(...)"
  
  def mkClone(using State, Erasure): Annot = Cloner(SymbolSubst.Id).annotation(this)

object Annot:
  
  val Private = Modifier(Keyword.`private`)(N)
  
  /** The `declare` modifier in `annotations`, if present. */
  def declareModifierOf(annotations: Ls[Annot]): Opt[Annot.Modifier] = annotations.collectFirst:
    case mod @ Annot.Modifier(Keyword.`declare`) => mod
  
end Annot

type AnySelTerm = AnySel & Resolvable

sealed trait AnySel extends ResolvableImpl:
  self: Term.Sel | Term.SynthSel | Term.SelProj =>
  
  val sym: Opt[MemberSymbol]
  val typ: Opt[Type]
  val nme: Tree.Ident
  val resSym: FlowSymbol
  val prefix: Term
  val originalCtx: Opt[SrcScope]
  
  var resolvedTargets: Ls[flow.SelectionTarget] = Nil // * filled during flow analysis
end AnySel

object AnySel:
  def unapply(t: AnySelTerm): S[(Term, Tree.Ident, Opt[Term])] = t match
    case Term.Sel(lhs, id) => S((lhs, id, N))
    case Term.SynthSel(lhs, id) => S((lhs, id, N))
    case Term.SelProj(lhs, cls, proj) => S((lhs, proj, S(cls)))
end AnySel

type Resolvable = Term & ResolvableImpl

// TODO: remove when the new resolution migration is completed.
sealed trait ResolvableImpl extends ShapeHost, PossiblyErroneous:
  this: Term =>
  
  import Resolvable.CallableDefinition
  
  /**
   * The expanded form of the term, if it exists. 
   * 
   * - If it is None, the term hasn't yet expanded.
   * - If it is Some of None, the term has expanded to itself.
   * - If it is Some of Some, the term has expanded to something else.
   */
  private[semantics]
  var expansion: Opt[Opt[Term]] = N

  def duplicate(using State): this.type =
    this.match
      case t: Term.Resolved => t.copy()(t.typ)
      case t: Term.Ref => t.copy()(t.tree, t.typ)
      case t: Term.App => t.copy()(t.tree, t.typ, t.resSym)
      case t: Term.TyApp => t.copy()(t.typ)
      case t: Term.Sel => t.copy()(t.sym, t.resSym, t.typ, t.originalCtx)
      case t: Term.SynthSel => t.copy()(t.sym, t.resSym, t.typ, t.originalCtx)
      case t: Term.LeadingDotSel => t.copy()(t.originalCtx)
      case t: Term.SelProj => t.copy()(t.sym, t.resSym, t.typ, t.originalCtx)
      case t: Term.New => t.copy()(t.resSym, t.typ)
    .withLocOf(this)
    .asInstanceOf
  
  def withSym(sym: MemberSymbol): this.type = 
    this.match
      case t: Term.Sel => t.copy()(S(sym), t.resSym, t.typ, t.originalCtx)
      case t: Term.SynthSel => t.copy()(S(sym), t.resSym, t.typ, t.originalCtx)
      case t: Term.SelProj => t.copy()(S(sym), t.resSym, t.typ, t.originalCtx)
      case _ => lastWords(s"withSym called on non-selection term: $this")
    .withLocOf(this)
    .asInstanceOf
  
  def withTyp(typ: Type)(using DebugPrinter): this.type = 
    this.match
      case t: Term.Resolved => t.copy()(S(typ))
      case t: Term.Ref => t.copy()(t.tree, S(typ))
      case t: Term.App => t.copy()(t.tree, S(typ), t.resSym)
      case t: Term.TyApp => t.copy()(S(typ))
      case t: Term.Sel => t.copy()(t.sym, t.resSym, S(typ), t.originalCtx)
      case t: Term.SynthSel => t.copy()(t.sym, t.resSym, S(typ), t.originalCtx)
      case _: Term.LeadingDotSel => lastWords(s"Cannot attach a type to leading dot selection: ${this.showDbg}")
      case t: Term.SelProj => t.copy()(t.sym, t.resSym, S(typ), t.originalCtx)
      case t: Term.New => t.copy()(t.resSym, S(typ))
    .withLocOf(this)
    .asInstanceOf
  
  def expandedIn[T](in: Term => T): T =
    in(expanded)
  
  def expandedResolvableIn[T](in: Resolvable => T)(using DebugPrinter): T =
    expanded match
      case r: Resolvable => in(r)
      case t => lastWords(s"Expected a resolvable term, but got ${t.showDbg}.")

  /** 
   * Expanding a term to another, which can be later retrieved by the
   * `instantiate` method. 
   *
   * If a term is expanding to a term that contains itself, the
   * `instantiate` method goes into an infinite loop and the expansion
   * never ends. Thus, the term itself should be duplicated by the
   * `duplicate` method if it appears in its own expansion.
   *
   * This method is only supposed to be called by Resolver. 
   */
  private[semantics] def expand(expansion: Opt[Term]): this.type =
    // An occurrence has one expansion. Reusing it may request that same
    // expansion again, but further transformations must expand its current
    // result instead of replacing it. Term equality is occurrence identity.
    if this.expansion.isDefined && this.expansion.get =/= expansion then
      lastWords(s"Cannot expand the term ${this} multiple times (to different expansions ${expansion}).")
    
    this.expansion = S(expansion)
    this
    
  def resolve: this.type = expand(N)
  def dontResolve: this.type = this // TODO rm
  
  /**
   * A helper function to create a resolved term for this term.
   */
  def resolved(sym: AnyDefinitionSymbol): Term.Resolved =
    Term.Resolved(this, sym)(typ = resolvedTyp)
  
  def hasExpansion = expansion.isDefined
  
  def defn: Opt[Definition] = legacyResolvedSym match
    case S(sym: BlockMemberSymbol) => N
    case S(sym: AnyDefinitionSymbol) => sym.defn
    case _ => N
  
  def typDefn = resolvedTyp match
    case S(typ) => typ.symbol match
      case S(sym: TypeSymbol) => sym.defn
      case _ => N
    case N => N
  
  def callableDefn: Opt[CallableDefinition] = defn.flatMap:
    CallableDefinition.fromDefn(_)
  
  def singletonDefn: Opt[ModuleOrObjectDef] = typDefn match
    case S(td: ModuleOrObjectDef) => S(td)
    case _ => N

object Resolvable:
  case class CallableDefinition(
    sym: BlockMemberSymbol,
    params: Ls[ParamList],
    tparams: Opt[Ls[Param]],
    sign: Opt[Term],
    flags: TermDefFlags,
    modulefulness: Modulefulness,
    defn: Definition
  )
  
  object CallableDefinition:
    def fromDefn(defn: Definition): Opt[CallableDefinition] = defn match
      case defn: TermDefinition => S(CallableDefinition(
        defn.sym,
        defn.params,
        defn.tparams,
        defn.sign,
        defn.flags,
        defn.modulefulness,
        defn,
      ))
      case defn: TypeDef => S(CallableDefinition(
        defn.bsym,
        Nil,
        if defn.tparams.isEmpty
        then N
        else S(defn.tparams.map(tp => Param(FldFlags.empty, tp.sym, N, Modulefulness.none)(tp.toLoc))),
        defn.rhs,
        TermDefFlags.empty, // TODO: handle class-like definitions with flags
        Modulefulness.none, // TODO: handle modulefulness for class-like definitions
        defn,
      ))
      case defn: ClassLikeDef => S(CallableDefinition(
        defn.bsym, 
        defn.paramsOpt.toList ::: defn.auxParams, 
        if defn.tparams.isEmpty
        then N
        else S(defn.tparams.map(tp => Param(FldFlags.empty, tp.sym, N, Modulefulness.none)(tp.toLoc))),
        N, // TODO: handle class-like definitions with signatures
        TermDefFlags.empty, // TODO: handle class-like definitions with flags
        Modulefulness.none, // TODO: handle modulefulness for class-like definitions
        defn,
      ))

case class SrcScope(outer: Elaborator.OuterCtx, parent: Opt[SrcScope]):
  
  /** Whether code written in this scope can access the private members of `owner`: whether it is nested in the
    * definition of `owner` or of one of its companions, which are the other class-like definitions of its block member
    * symbol. These are found through `owner`, whose definition is complete, unlike the definitions enclosing this scope,
    * which may still be in the process of being elaborated. Notably, a subclass of `owner` cannot access these members. */
  def canAccessPrivatesOf(owner: ClassLikeDef): Bool =
    def grantsAccess(inner: InnerSymbol): Bool =
      (inner is owner.sym) || owner.bsym.asCls.exists(_ is inner) || owner.bsym.asModOrObj.exists(_ is inner)
    outer.inner.exists(grantsAccess) || parent.exists(_.canAccessPrivatesOf(owner))

object SrcScope:
  given s: Ctx => SrcScope = summon[Ctx].scope



enum Term extends Statement, AutoLocated, ShapePublisher:
  /** Filled by the type interpreter during elaboration; erasure validates the completed result. */
  private[hkmc2] var typeInterpretation: Opt[TypeResolution] = N

  case Error()
  case UnitVal()
  case DynTy()
  case Missing // Placeholder terms that were not elaborated due to the "lightweight" elaboration mode `Mode.Light`
  case Lit(lit: Literal)
  
  // --- NEW ---
  case SimpleRef(sym: SimpleRefSymbol)(val tree: Opt[Tree.Ident]) extends Term, NewRefImpl
  case SelfRef(sym: InnerSymbol)(val tree: Tree.Ident) extends Term, NewRefImpl
  case MemberRef(sym: MemberSymbol)(val tree: Opt[Tree.Ident], val resSym: FlowSymbol) extends Term, NewResolvableImpl, NewRefImpl
  /** A direct reference to an inherited implementation, retaining the lexical receiver. */
  case Super(receiver: Term, owner: InnerSymbol, id: Tree.Ident)(val resSym: FlowSymbol) extends Term, NewResolvableImpl, ShapeHost
  /** An optional class selection fixes the lookup scope for an explicit member projection. */
  case NewSel(prefix: Term, id: Tree.Ident, cls: Opt[NewSel])(val resSym: FlowSymbol) extends Term, NewSelImpl, ShapeHost
  case UnresolvedRef(prefixes: Ls[Term], id: Tree.Ident)(val resSym: FlowSymbol) extends Term, UnresolvedRefImpl, ShapeHost
  case Capture(base: Term, thru: AnyDefinitionSymbol) extends Term
  // --- LEGACY ---
  /** A term that wraps another term, indicating that the symbol of the inner term is resolved.
    * This is mainly used to disambiguate overloaded definitions. */
  case Resolved(t: Term, sym: AnyDefinitionSymbol)
    (val typ: Opt[Type]) extends Term, ResolvableImpl
  case Ref(sym: Symbol)
    (val tree: Tree.Ident, val typ: Opt[Type]) extends Term, ResolvableImpl, AnyRefImpl
  case Sel(prefix: Term, nme: Tree.Ident)
    (val sym: Opt[MemberSymbol], val resSym: FlowSymbol, val typ: Opt[Type], val originalCtx: Opt[SrcScope])
    extends Term, AnySel
  case SynthSel(prefix: Term, nme: Tree.Ident)
    (val sym: Opt[MemberSymbol], val resSym: FlowSymbol, val typ: Opt[Type], val originalCtx: Opt[SrcScope])
    extends Term, AnySel
  case SelProj(prefix: Term, cls: Term, nme: Tree.Ident)
    (val sym: Opt[MemberSymbol], val resSym: FlowSymbol, val typ: Opt[Type], val originalCtx: Opt[SrcScope])
    extends Term, AnySel
  // --- END ---
  
  case App(lhs: Term, rhs: Term)
    (val tree: Tree.App, val typ: Opt[Type], val resSym: FlowSymbol) extends Term, ResolvableImpl, AppImpl
  case TyApp(lhs: Term, targs: Ls[Term])
    (val typ: Opt[Type]) extends Term, ResolvableImpl
  /** `checked` asks resolution to validate the receiver and determine the element
    * interface (`obj.[idx]`); it does not require a compile-time index value.
    * `arrayIdx` independently selects array indexing in the generated code. */
  case DynSel(prefix: Term, fld: Term, arrayIdx: Bool, checked: Bool)
  case Tup(fields: Ls[Elem])(val tree: Tree.Tup) extends Term, ShapeHost
  case Mut(underlying: Tup | Rcd | New | DynNew)
  case CtxTup(fields: Ls[Elem])(val tree: Tree.Tup) extends Term, ShapeHost
  case IfLike(kw: Keyword.SplitLike, form: IfLikeForm, split: SimpleSplit) extends Term, ShapeHost
  /** `If` expressions synthesized by the pattern compiler. It should only be
   *  created and used in `Lowering`. One must make sure that all terms in the
   *  split are correctly resolved. In the future, we might look for a way to
   *  remove `SynthIf` by generating IR `Match` blocks directly. */
  case SynthIf(split: Split)
  /** `while` loops synthesized by the pattern compiler, subject to the same
   *  restrictions as `SynthIf`. The split's branch consequents are evaluated
   *  for their effects and the loop is re-entered; the loop exits when no
   *  branch matches. Used by `ups.FixedPointCompiler` to drive the generated
   *  matcher machine. */
  case SynthWhile(split: Split)
  case Lam(params: ParamList, body: Term)
  case FunTy(lhs: Term, rhs: Term, eff: Opt[Term])
  case Forall(tvs: Ls[QuantVar], outer: Opt[VarSymbol], body: Term)
  case Constrained(constraints: Ls[SubConstraint], body: Term)
  case WildcardTy(in: Opt[Term], out: Opt[Term])
  case Blk(stats: Ls[Statement], res: Term) extends Term, BlkImpl
  case Rcd(mut: Bool, stats: Ls[Statement]) extends Term, ShapeHost
  case Quoted(body: Term)
  case Unquoted(body: Term)
  case New(cls: Term, args: Ls[Term], rft: Opt[ClassSymbol -> ObjBody])
    (val resSym: FlowSymbol, val typ: Opt[Type]) extends Term, ResolvableImpl
  case DynNew(cls: Term, args: Ls[Term])
  case Asc(term: Term, ty: Term)
  case CompType(lhs: Term, rhs: Term, pol: Bool)
  case Neg(rhs: Term)
  case Region(name: VarSymbol, body: Term)
  case RegRef(reg: Term, value: Term)
  case Assgn(lhs: Term, rhs: Term)
  case Drop(trm: Term)
  case Deref(ref: Term)
  case SetRef(ref: Term, value: Term)
  case Ret(result: Term)
  case Throw(result: Term)
  case Label(label: LabelSymbol, result: TempSymbol, body: Term, hasNonLocalContinueDispatch: Bool)
  case Break(label: LabelSymbol, result: TempSymbol, value: Opt[Term])
  case Continue(label: LabelSymbol)
  case Try(body: Term, finallyDo: Term)
  case Annotated(annot: Annot, target: Term)
  case Handle(lhs: LocalVarSymbol, rhs: Term, args: List[Term],
    derivedClsSym: ClassSymbol, defs: Ls[HandlerTermDefinition], body: Term)(
    // Abortive handlers never resume their body: a method's result is the handled expression's result.
    val isAbortive: Bool)
  case LeadingDotSel(nme: Tree.Ident)(
      val originalCtx: Opt[SrcScope]
    ) (using State) extends Term, ResolvableImpl, LeadingDotSelImpl
  
  // Terms are individual occurrences with their own resolution state and source
  // locations. Comparing their syntax does not establish that they denote the
  // same value; clients such as pattern normalization compare symbols instead.
  final override def equals(that: Any): Bool = that match
    case that: Term => this eq that
    case _ => false
  final override def hashCode: Int = System.identityHashCode(this)
  
  def withoutCaptures: Term = this match
    case Capture(base, _) => base.withoutCaptures
    case _ => this

  /** Class target validation looks through wrappers with no runtime representation.
    * Shape propagation still processes captures to retain their provenance.
    */
  def classHead: Term = this match
    case Capture(base, _) => base.classHead
    case TyApp(base, _) => base.classHead
    case _ => this
  
  def expanded: Term = this match
    case t: Resolvable => t.expansion match
      case S(S(t)) => t.expanded
      case S(N) => this
      case N => this
    case _ => this
  
  /**
   * This field equals `S(lds)` if the term is a chain of selections
   * and applications that originates with a leading-dot selection,
   * namely `lds`. Otherwise this field equals `N`.
   * It is evaluated during flow analysis to constrain the LDS with
   * the type of the whole term.
   */
  lazy val ldsRoot: Opt[LeadingDotSel] = this match
    case Sel(prefix, nme) => prefix.ldsRoot
    case App(lhs, rhs) => lhs.ldsRoot
    case sel: LeadingDotSel => S(sel)
    case _ => N

  /**
   * The prelinminary symbol for the term that is resolved during
   * elaboration. 
   */
  lazy val symbol: Opt[Symbol] = this match
    case Capture(base, _) => base.symbol
    case res: Resolved => S(res.sym)
    case Ref(sym) => S(sym)
    case sel: Sel => sel.sym
    case sel: SynthSel => sel.sym
    case sel: SelProj => sel.sym
    case TyApp(lhs = lhs) => lhs.symbol
    case _ => N
  
  /**
   * The symbol representing the evaluation result of the term. This
   * symbol is resolved during the resolution stage. Reading its final value requires
   * erasure; elaboration must listen for shapes instead.
   */
  def resolvedSym(using Erasure): Opt[Symbol] = resolvedSymImpl

  /** Read-only lookup shared by erasure and legacy consumers of completed imports.
    * The public accessors establish completion before reading new-resolution targets.
    */
  private def resolvedSymImpl: Opt[Symbol] = expanded match
    case res: Resolved => S(res.sym)
    case SimpleRef(sym) => S(sym)
    case Capture(base, _) => base.resolvedSymImpl
    case ref: UnresolvedRef if ref.resolvedMembers.distinct.sizeCompare(1) =/= 0 => N
    case sel: NewSel if sel.hasAmbiguousClassImpl => N
    case ref: NewResolvable =>
      if ref.isErroneous then N else ref.resolvedTargets.distinct match
        case sym :: Nil => S(sym)
        case _ => N
    case ref: Ref => ref.symbol
    case sel: Sel => sel.sym
    case sel: SynthSel => sel.sym
    case sel: SelProj => sel.sym
    case app: TyApp => app.lhs.resolvedSymImpl
    case _ => N
  
  /** The old resolver may inspect its own expansions while resolving legacy terms,
    * and completed references in imported new-resolution signatures. Never observe
    * a new reference while its defining block can still change its selected targets.
    */
  private[semantics] def legacyResolvedSym: Opt[Symbol] = expanded match
    case term: (NewResolvable | NewRefImpl | Capture) =>
      assert(term.originalData.completed, "Legacy symbol query on an incomplete new-resolution term")
      term.resolvedSymImpl
    case app: TyApp => app.lhs.legacyResolvedSym
    case term => term.symbol

  def resolvedTyp: Opt[Type] = expanded match
    case res: Resolved => res.typ
    case ref: Ref => ref.typ
    case app: App => app.typ
    case app: TyApp => app.typ
    case sel: Sel => sel.typ
    case sel: SynthSel => sel.typ
    case nu: New => nu.typ
    case _ => N
  
  /** The set of free variable names in this term.
    * Note: it is wrong to compute this based on strings, rather than symbols,
    * but strings are good enough for now. This is currently only used to detect useless pattern variables.
    * (These definitions were generated as part of a slop PR.) */
  lazy val freeVars: Set[Str] = this match
    case Ref(sym) => Set.single(sym.nme)
    case SimpleRef(sym) => Set.single(sym.nme)
    case MemberRef(sym) => Set.single(sym.nme)
    case SelfRef(sym) => Set.single(sym.nme)
    case Lam(params, body) =>
      val paramNames = params.allParams.iterator.map(_.sym.nme).toSet
      body.freeVars -- paramNames
    case Blk(stats, res) =>
      Term.blkFreeVars(stats, res.freeVars)
    case IfLike(_, _, split) => split.freeVars
    case SynthIf(split) => split.freeVars
    case SynthWhile(split) => split.freeVars
    case Region(name, body) =>
      body.freeVars - name.nme
    case Handle(lhs, rhs, args, _, defs, body) =>
      val rhsFree = rhs.freeVars
      val argsFree = args.iterator.flatMap(_.freeVars).toSet
      val defsFree = defs.iterator.flatMap(d => Term.termDefFreeVars(d.td)).toSet
      val bodyFree = body.freeVars - lhs.nme
      rhsFree ++ argsFree ++ defsFree ++ bodyFree
    case Label(_, result, body, _) =>
      val bodyFree = body.freeVars
      if bodyFree(result.nme) then bodyFree - result.nme else bodyFree
    case Forall(_, _, body) => body.freeVars
    case Error | Missing | _: Lit | _: DynTy | _: UnitVal | _: LeadingDotSel | _: Continue => Set.empty
    case Break(_, result, value) => value.iterator.flatMap(_.freeVars).toSet + result.nme
    case _ => subTerms.iterator.flatMap(_.freeVars).toSet

  def sel(id: Tree.Ident, sym: Opt[MemberSymbol])(using State, Elaborator.Ctx): Sel =
    Sel(this, id)(sym, FlowSymbol.sel(id.name), N, S(summon))
  /** Select a known synthetic member without performing source-level lookup. */
  def synthSel(sym: MemberSymbol)(using State): SynthSel =
    SynthSel(this, Tree.Ident(sym.nme))(S(sym), FlowSymbol.synthSel(sym.nme), N, N)

  def selNoSym(nme: Str, synth: Bool = false)(using State, Elaborator.Ctx): Sel | SynthSel =
    val id = new Tree.Ident(nme)
    if synth
    then SynthSel(this, id)(N, FlowSymbol.synthSel(nme), N, S(summon))
    else sel(id, N)
  
  def app(args: Term*)(using State) =
    App(this, Tup(args.toList.map(PlainFld(_)))(Tree.DummyTup))
      (Tree.App(Tree.Dummy, Tree.Dummy), N, FlowSymbol(""))
  
  /** Clone a resolved expression with fresh bound symbols, retaining source identifiers
    * and completed resolution. Only already-cached locations are copied.
    */
  override def mkClone(using State, Erasure): Term = Cloner(SymbolSubst.Id).term(this)
  
end Term

object Term:
  /** Compute the free variable names of a block given its statements and the
    * free vars of its result term. Processes statements right-to-left so that
    * bindings introduced by `LetDecl`, `TermDefinition`, class definitions,
    * etc. correctly shadow uses in subsequent statements. */
  private[semantics] def blkFreeVars(stats: Ls[Statement], resFree: Set[Str]): Set[Str] =
    val blockLevelBinders = Buffer.empty[Str]
    stats.foreach:
      case td: TermDefinition =>
        blockLevelBinders += td.sym.nme
      case cls: ClassLikeDef =>
        blockLevelBinders += cls.sym.nme
      case td: TypeDef =>
        blockLevelBinders += td.bsym.nme
      case _: (Import | SetConfig | RcdField | RcdSpread | Term | LetDecl | DefineVar) => ()
    (stats.foldRight(resFree): (stat, acc) =>
      stat match
        case LetDecl(sym, annotations) =>
          (acc - sym.nme) ++ annotations.iterator.flatMap(_.subTerms).flatMap(_.freeVars)
        case DefineVar(sym, rhs) =>
          acc + sym.nme ++ rhs.freeVars
        case t: Term =>
          acc ++ t.freeVars
        case _: (Import | SetConfig | RcdField | RcdSpread | TermDefinition | ClassLikeDef | TypeDef) =>
          acc ++ stat.subTerms.iterator.flatMap(_.freeVars)
    ) -- blockLevelBinders
  
  /** Free vars of a TermDefinition body, with its own params subtracted. */
  private[semantics] def termDefFreeVars(td: TermDefinition): Set[Str] =
    val paramNames = td.params.iterator.flatMap(_.allParams).map(_.sym.nme).toSet
    val bodyFree = td.body.iterator.flatMap(_.freeVars).toSet
    val signFree = td.sign.iterator.flatMap(_.freeVars).toSet
    (bodyFree ++ signFree) -- paramNames
  
  /** Free vars of a ClassLikeDef body, with constructor params subtracted. */
  private def classLikeDefFreeVars(cls: ClassLikeDef): Set[Str] =
    val paramNames = cls.paramsOpt.iterator.flatMap(_.allParams).map(_.sym.nme).toSet
    val bodyFree = cls.body.blk.freeVars
    val extFree = cls.ext.iterator.flatMap(_.freeVars).toSet
    (bodyFree ++ extFree) -- paramNames
end Term

import Term.*


extension (self: Blk)
  def mapRes(f: Term => Term) =
    Blk(self.stats, f(self.res))


case class ShowCfg(
  showErasedTypes: Bool,
  showExpansionMappings: Bool,
  showFlowSymbols: Bool,
  debug: Bool,
):
  // * Rather ugly way of collecting shown symbols during show operations
  val shownSymbols: MutSet[Symbol] = MutSet.empty
end ShowCfg

object ShowCfg:
  // * For use when displaying things for internal use (not for end users)
  val internal = ShowCfg(
    showErasedTypes = true,
    showFlowSymbols = true,
    showExpansionMappings = false,
    debug = false,
  )
end ShowCfg


sealed trait Statement extends StatementImpl


final case class LetDecl(sym: LocalVarSymbol | TermSymbol, annotations: Ls[Annot])(val toLoc: Opt[Loc]) extends Statement

/** The symbol identifies the property, independently of any local binding used
  * to evaluate its value. Computed keys also have an identity, but cannot be
  * selected statically until their key is known. Cloning preserves this identity.
  */
final case class RcdField(field: Term, rhs: Term, sym: BlockMemberSymbol)(val key: Opt[MemberKey]) extends Statement, AutoLocated:
  // The two-argument RcdField.apply sets sym.tsym and its definition before
  // constructing this node. Lowering clones reuse the same initialized symbols.
  val tsym: TermSymbol = sym.tsym.get
  require((tsym.k is RecordField) && tsym.owner.isEmpty && tsym.defn.exists(_.sym is sym))
  field match
    case Term.Lit(Tree.StrLit(name)) => require(sym.nme == name)
    case _ => ()

object RcdField:
  def apply(field: Term, rhs: Term)(using State): RcdField = make(field, rhs, false, N)
  def signature(field: Term, sign: Term)(using State): RcdField = make(field, sign, true, N)
  def signature(field: Term, sign: Term, symbol: SymbolKey)(using State): RcdField =
    make(field, sign, true, S(symbol))
  private def make(field: Term, rhs: Term, signature: Bool, symbol: Opt[SymbolKey])(using State): RcdField =
    val name = field match
      case Term.Lit(Tree.StrLit(name)) => name
      case _ => "computed field"
    val id = new Tree.Ident(name)
    id.withLocOf(field)
    val sym = new BlockMemberSymbol(name, Nil)
    val tsym = TermSymbol(RecordField, N, id, erasedType = N)
    sym.tsym = S(tsym)
    // Value-field lookup removes the synthetic definition's capture mark, leaving
    // enclosing call-site marks intact. A structural type field instead refers
    // directly to its written type: projection does not invoke a value definition.
    tsym.defn = S(TermDefinition(RecordField, sym, tsym, Nil, N,
      if signature then S(rhs) else N,
      if signature then N else S(Term.Capture(rhs, tsym)), TermDefFlags.empty, Modulefulness.none, symbol.toList.map(Annot.JsSymbol(_)(field.toLoc)), N)(field.toLoc, field.toLoc, N))
    sym.complete()
    RcdField(field, rhs, sym)(symbol.orElse(field match
      case Term.Lit(Tree.StrLit(name)) => S(name)
      case _ => N))
final case class RcdSpread(rcd: Term) extends Statement, AutoLocated

final case class DefineVar(sym: LocalSymbol | TermSymbol, rhs: Term)(val toLoc: Opt[Loc]) extends Statement

/** A global configuration change directive (`#config(...)`).
  * Records a function that modifies the current compiler configuration. */
final case class SetConfig(modify: hkmc2.Config => hkmc2.Config)(val toLoc: Opt[Loc]) extends Statement:
  override def toString: String = "#config(...)"

enum Visibility:
  case Public, Private

object Visibility:
  def of(annotations: Ls[Annot]): Visibility = annotations.collectFirst:
      case Annot.Modifier(Keyword.`private`) => Visibility.Private
      case Annot.Modifier(Keyword.`public`) => Visibility.Public
    .getOrElse(Visibility.Public)

/** `isMethod` distinguishes methods from functions. `hasResultAnnotation` records whether a
  * signature describes just the result; erasure consumes leading arrows only for full signatures.
  */
final case class TermDefFlags(isMethod: Bool, hasResultAnnotation: Bool):
  def showDbg: Str = 
    val flags = Buffer.empty[String]
    if isMethod then flags += "method "
    if hasResultAnnotation then flags += "result annotation "
    flags.mkString
  override def toString: String = "‹" + showDbg + "›"

object TermDefFlags { val empty: TermDefFlags = TermDefFlags(false, false) }

/**
 * A case class representing the modulefulness of a declaration.
 *
 * @param msym if None, the declaration is non-moduful; if Some of
 * symbol, the declaration is moduleful and the symbol is the symbol of
 * the module's type
 */
final case class Modulefulness(msym: Opt[ModuleOrObjectSymbol])(val modified: Bool):
  
  def isModuleful: Bool = msym.isDefined
  
  /**
   * Return Some of the module definition if it is moduleful; None
   * otherwise.
   */
  def mdef: Opt[ModuleOrObjectDef] = msym match
    case S(msym) => msym.defn match
      case S(defn: ModuleOrObjectDef) => S(defn)
      case N => lastWords(s"no definition for module symbol $msym")
    case N => N

object Modulefulness:
  
  def ofSign(sign: Option[Term])(modified: Bool) = 
    sign.flatMap(_.symbol) match
      case S(sym: BlockMemberSymbol) if modified => sym.asMod match
        case S(sym) => 
          Modulefulness(S(sym))(modified)
        case N =>
          Modulefulness(N)(modified)
      case _ =>
        Modulefulness(N)(modified)
  
  val none = Modulefulness(N)(false)

final case class TermDefinition(
    k: TermDefKind, // * The only reason we store it here in addition to tsym.k is for refining patmats
    sym: BlockMemberSymbol,
    tsym: TermSymbol,
    params: Ls[ParamList],
    tparams: Opt[Ls[Param]],
    sign: Opt[Term],
    body: Opt[Term],
    flags: TermDefFlags,
    modulefulness: Modulefulness,
    annotations: Ls[Annot],
    companion: Opt[CompanionSymbol],
)(val toLoc: Opt[Loc], val headerLoc: Opt[Loc],
  // Lexical binding site, as ModuleOrObjectDef.path; absent for synthetic definitions.
  val scope: Opt[SrcScope],
) extends CompanionValue:
  require(k is tsym.k)
  def bsym: BlockMemberSymbol = sym
  val owner = tsym.owner
  /** Only function bodies are wrapped by AsyncLowering; annotations on other
    * definitions are ignored with a warning and must not change their interface.
    */
  def asyncAnnotation: Opt[Annot.Async] =
    if (k is syntax.Fun) && body.nonEmpty then annotations.collectFirst:
      case annotation: Annot.Async => annotation
    else N
  /** A result annotation denotes the whole result; a separate function signature
    * includes the arrows corresponding to the definition's written parameter lists.
    */
  def resultSignature: Opt[Term] =
    def strip(sign: Term, count: Int): Term = (sign, count) match
      case (Term.Forall(_, _, body), _) => strip(body, count)
      case (Term.FunTy(_, rhs, _), n) if n > 0 => strip(rhs, n - 1)
      case _ => sign
    sign.map: sign =>
      if (k is syntax.Fun) && !flags.hasResultAnnotation then strip(sign, params.length)
      else sign
  lazy val mayRaiseEffects: Bool =
    annotations.forall:
      case Annot.Pure() => false
      case _ => true
  def extraAnnotations: Ls[Annot] = annotations.filter:
    case Annot.Modifier(Keyword.`declare` | Keyword.`abstract`) => false
    case _ => true
  
  def companionClass: Opt[ClassSymbol] = companion match
    case S(sym: ClassSymbol) if sym.defn.isDefined => S(sym)
    case _ => N

final case class HandlerTermDefinition(
  resumeSym: VarSymbol,
  td: TermDefinition
)

object ObjBody:
  
  def extractMembers(blk: Term.Blk): Ls[ErrorReport] \/ Map[Str, BlockMemberSymbol] =
    val (errs, mems) = blk.stats.collect:
      case td: TermDefinition => td.sym -> td
      case td: ClassLikeDef => td.bsym -> td
      case td: TypeDef => td.bsym -> td
    .groupBy(_._1.nme)
    .partitionMap: (nme, syms) =>
      if syms.map(_._1).distinct.tail.nonEmpty then L:
        (msg"Duplicate definition of member named '${nme}'." -> N) ::
        syms.map(_._2).map(msg"Defined at: " -> _.toLoc)
      else R:
        nme -> syms.head._1
    
    val memMap = mems.toMap
    val aliasEntries = mems.toList.flatMap: (nme, sym) =>
      sym.sourceAliases.filter(_ =/= nme).map(_ -> sym)
    val aliasConflicts = aliasEntries.groupMap(_._1)(_._2).collect:
      case (alias, syms) if syms.distinct.sizeCompare(1) > 0 =>
        ErrorReport(msg"Duplicate definition of member alias '${alias}'." -> N :: Nil)
      case (alias, sym :: _) if memMap.get(alias).exists(_ isnt sym) =>
        ErrorReport(msg"Member alias '${alias}' conflicts with an existing member." -> N :: Nil)

    if errs.nonEmpty then
      L(errs.map(ErrorReport(_)).toList)
    else if aliasConflicts.nonEmpty then
      L(aliasConflicts.toList)
    else
      R(memMap ++ aliasEntries)

case class ObjBody(blk: Term.Blk):
  
  lazy val members: Map[Str, BlockMemberSymbol] =
    ObjBody.extractMembers(blk) match
      case L(errs) => lastWords:
        errs.map(_.mainMsg).mkString("\n")
      case R(mems) =>
        mems
  
  lazy val (methods, nonMethods) = blk.stats.partitionMap:
    case td: TermDefinition if td.k is syntax.Fun => L(td)
    case s => R(s)
  
  lazy val publicFlds: Ls[TermDefinition] = nonMethods.collect:
    case td: TermDefinition if td.k.isInstanceOf[syntax.Val] => td
  
  // override def toString: String = statmts.mkString("{ ", "; ", " }")
  // override def toString: String = blk.showDbg

end ObjBody


/** `sym` is a `BlockMemberSymbol` or a `VarSymbol` when the import is made by the user
  * and can be referred to by name (it's either the BMS of the imported module
  * or the VarSymbol of the alias, in an aliased import `import "..." as alias`),
  * in which case it is a `BlockMemberSymbol` when importing files explicitly
  * and a `TermSymbol` when the import is made implicitly by the compiler (eg, importing "Predef").
  * Note that the `file` Path may not represent a real file; eg when importing "fs". */
case class Import(sym: ImportSymbol, str: Str, file: io.Path)(val toLoc: Opt[Loc]) extends Statement


/** Declaration spans come from the syntax that introduced them, never from semantic
  * subterms: those omit names and may contain synthesized or unrelated source terms.
  * Rewrites preserve the original span; declarations without source syntax use `N`.
  */
sealed abstract class Declaration extends Located:
  val toLoc: Opt[Loc]
  val sym: Symbol
  
  /** Whether this declares a class, a pattern, an object, or a pattern
    * parameter. Only these can be in patterns constructor position. */
  def isPatternConstructor: Bool = this match
    case _: (TermDefinition | TypeDef | TyParam) => false
    case d: ModuleOrObjectDef => d.kind isnt Mod
    case _: (PatternDef | ClassDef) => true
    case p: Param => p.flags.pat

sealed abstract class Definition extends Declaration, Statement, PossiblyErroneous:
  val annotations: Ls[Annot]
  def bsym: BlockMemberSymbol
  /** The span of this definition's header: its modifiers (such as `declare`), keyword, name,
    * type and value parameter lists, result annotation, and parent clause, but neither its
    * annotations (such as `@foo`) nor its body or right-hand side (see `syntax.TypeOrTermDef.headLoc`).
    * Diagnostics that cite the definition as a witness, such as arity errors, should use
    * this rather than `toLoc`, which spans the whole definition, including its body.
    * A class constructor's header is that of its class; synthesized definitions,
    * such as the fields generated from class parameters, use their source location. */
  def headerLoc: Opt[Loc]
  def visibility: Visibility = Visibility.of(annotations)
  def hasDeclareModifier: Opt[Annot.Modifier] = Annot.declareModifierOf(annotations)
  def hasStagedModifier: Opt[Annot.Modifier] = annotations.collectFirst:
    case mod @ Annot.Modifier(Keyword.`staged`) => mod
  def describeRef: Str = this match
    case td: TermDefinition => s"term '${td.sym.nme}'"
    case cls: ClassDef => s"class '${cls.sym.nme}'"
    case mod: ModuleOrObjectDef =>
      if mod.kind is Mod then s"module '${mod.sym.nme}'"
      else s"object '${mod.sym.nme}'"
    case td: TypeDef => s"type '${td.bsym.nme}'"
    case pat: PatternDef => s"pattern '${pat.sym.nme}'"

sealed trait CompanionValue extends Definition

type CompanionSymbol = ModuleOrObjectSymbol | TypeAliasSymbol | ClassSymbol
type ClassCompanionSymbol = ModuleOrObjectSymbol | TypeAliasSymbol
type ModuleCompanionSymbol = TypeAliasSymbol | ClassSymbol


sealed abstract class TypeLikeDef extends Definition:
  val kind: ObjDefKind
  val bsym: BlockMemberSymbol
  val tparams: Ls[TyParam]
  val annotations: Ls[Annot]

sealed abstract class ClassLikeDef extends TypeLikeDef:
  val owner: Opt[InnerSymbol]
  val kind: ClsLikeKind
  val sym: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol
  val bsym: BlockMemberSymbol
  val ctorSym: Opt[ClassCtorSymbol]
  val tparams: Ls[TyParam]
  val paramsOpt: Opt[ParamList]
  val auxParams: Ls[ParamList]
  val ext: Opt[New]
  val body: ObjBody
  val companion: Opt[CompanionSymbol]
  val annotations: Ls[Annot]
  def classCompanion = companion match
    case S(sym: ClassSymbol) => S(sym)
    case _ => N
  def moduleCompanion = companion match
    case S(sym: ModuleOrObjectSymbol) => S(sym)
    case _ => N
  def extraAnnotations(using Ctx): Ls[Annot] = annotations.filter:
    case Annot.Modifier(Keyword.`declare` | Keyword.`abstract` | Keyword.`data`) => false
    case _: Annot.Bufferable if kind is Cls => false
    case _ => true


case class ModuleOrObjectDef(
  owner: Opt[InnerSymbol], 
  sym: ModuleOrObjectSymbol, 
  bsym: BlockMemberSymbol,
  tparams: Ls[TyParam], 
  paramsOpt: Opt[ParamList], 
  auxParams: Ls[ParamList], 
  ext: Opt[New],
  kind: ClsLikeKind,
  body: ObjBody,
  companion: Opt[ModuleCompanionSymbol],
  annotations: Ls[Annot],
)(
  val path: SrcScope,
  val toLoc: Opt[Loc],
  val headerLoc: Opt[Loc],
) extends ClassLikeDef, CompanionValue:
  val ctorSym: Option[ClassCtorSymbol] = N

case class PatternDef(
    owner: Opt[InnerSymbol],
    sym: PatternSymbol,
    bsym: BlockMemberSymbol,
    tparams: Ls[TyParam],
    /** All parameters. */
    parameters: Ls[Param],
    /** The pattern parameters, for example, `T` in
     *  `pattern Nullable(pattern T) = null | T`. */
    patternParams: Ls[Param],
    /** The extraction parameters, for example, `x` in
     *  `pattern PairLike(x, y) = [x, y] | Pair(x, y)`. */
    extractionParams: Ls[Param],
    /** The elaborated pattern on the right-hand side, for example,
     *  `[x, y] | Pair(x, y)` in `pattern PairLike(x, y) = [x, y] | Pair(x, y)`.
     */
    pattern: Pattern,
    annotations: Ls[Annot],
)(val toLoc: Opt[Loc], val headerLoc: Opt[Loc]) extends ClassLikeDef:
  self =>
  val kind: ClsLikeKind = Pat
  val ext: Opt[New] = N
  /** Each pattern definition should contain two methods: `unapply` and
   *  `unapplyStringPrefix`, which are generated in `Lowering`. Hence, there
   *  is no need to make `body` a parameter. */
  val body: ObjBody = ObjBody(Blk(Nil, Term.Lit(syntax.Tree.UnitLit(false))))
  /** Pattern definitions do not need parameter lists. */
  val paramsOpt: Opt[ParamList] = N
  val auxParams: Ls[ParamList] = Nil
  val companion: Opt[CompanionSymbol] = N // TODO support
  val ctorSym: Option[ClassCtorSymbol] = N


sealed abstract class ClassDef extends ClassLikeDef:
  val kind: ClsLikeKind
  val sym: ClassSymbol
  val bsym: BlockMemberSymbol
  val ctorSym: Opt[ClassCtorSymbol]
  val tparams: Ls[TyParam]
  val paramsOpt: Opt[ParamList]
  val auxParams: Ls[ParamList]
  val body: ObjBody
  val companion: Opt[ClassCompanionSymbol]
  val annotations: Ls[Annot]
  /** The modifiers of the class's constructor declarations, as in `private constructor(x)`.
    * The class's parameter lists, whether written in its head or in constructor declarations,
    * form a single constructor, so a modifier written on any of these declarations applies to
    * the whole constructor. This is the case even for a bare `private constructor` declaration,
    * which adds no parameter list. */
  val ctorAnnotations: Ls[Annot]
  /** The span of the `constructor(...)` declarations in the class body that declare
    * parameter lists, if any. These parameter lists extend the class's constructor
    * beyond those written in its header, which `headerLoc` covers. Since they are written
    * in the body, only diagnostics about the constructor's parameters, such as arity errors,
    * cite this location, in addition to `headerLoc`. */
  val ctorLoc: Opt[Loc]
  def isData: Opt[Annot.Modifier] = annotations.collectFirst:
    case mod @ Annot.Modifier(Keyword.`data`) => mod
  /** The modifier making the class's constructor private, if any: only the class and its
    * companion can then refer to the constructor or instantiate the class (see NewResolverState.checkAccess). */
  def privateCtor: Opt[Annot.Modifier] = ctorAnnotations.collectFirst:
    case mod @ Annot.Modifier(Keyword.`private`) => mod
  override def extraAnnotations(using Ctx): Ls[Annot] = super.extraAnnotations.filter:
    case Annot.Modifier(Keyword.`data`) => false
    case _ => true

object ClassDef:
  def apply(
      owner: Opt[InnerSymbol],
      kind: ClsLikeKind,
      sym: InnerSymbol,
      bsym: BlockMemberSymbol,
      ctorSym: Opt[ClassCtorSymbol],
      tparams: Ls[TyParam],
      params: Ls[ParamList],
      ext: Opt[New],
      body: ObjBody,
      annotations: Ls[Annot],
      comp: Opt[ClassCompanionSymbol],
      auxCtorParams: Ls[ParamList],
      ctorAnnotations: Ls[Annot],
  )(toLoc: Opt[Loc], headerLoc: Opt[Loc], ctorLoc: Opt[Loc]): ClassDef =
    params match
      case ps :: pss => Parameterized(owner, kind, sym.asInstanceOf// TODO: improve
        , bsym, S(ctorSym.getOrElse(lastWords("Parameterized classes should have a ctor symbol.")))
        , tparams, ps, pss ::: auxCtorParams, ext, body, comp, annotations, ctorAnnotations)(toLoc, headerLoc, ctorLoc)
      case Nil => Plain(owner, kind, sym.asInstanceOf// TODO: improve
        , bsym
        , tparams, ext, body, comp, annotations, auxParams = auxCtorParams, ctorSym = ctorSym,
        ctorAnnotations = ctorAnnotations)(toLoc, headerLoc, ctorLoc)
  
  def unapply(cls: ClassDef): Opt[(ClassSymbol, Ls[TyParam], Opt[ParamList], ObjBody)] =
    S((cls.sym, cls.tparams, cls.paramsOpt, cls.body))
  
  case class Parameterized(
      owner: Opt[InnerSymbol],
      kind: ClsLikeKind,
      sym: ClassSymbol,
      bsym: BlockMemberSymbol,
      ctorSym: S[ClassCtorSymbol],
      tparams: Ls[TyParam],
      params: ParamList,
      auxParams: Ls[ParamList],
      ext: Opt[New],
      body: ObjBody,
      companion: Opt[ClassCompanionSymbol],
      annotations: Ls[Annot],
      ctorAnnotations: Ls[Annot],
  )(val toLoc: Opt[Loc], val headerLoc: Opt[Loc], val ctorLoc: Opt[Loc]) extends ClassDef:
    val paramsOpt: Opt[ParamList] = S(params)
  
  case class Plain(
      owner: Opt[InnerSymbol],
      kind: ClsLikeKind,
      sym: ClassSymbol,
      bsym: BlockMemberSymbol,
      tparams: Ls[TyParam],
      ext: Opt[New],
      body: ObjBody,
      companion: Opt[ClassCompanionSymbol],
      annotations: Ls[Annot],
      auxParams: List[ParamList],
      ctorSym: Opt[ClassCtorSymbol],
      ctorAnnotations: Ls[Annot],
  )(val toLoc: Opt[Loc], val headerLoc: Opt[Loc], val ctorLoc: Opt[Loc]) extends ClassDef:
    val paramsOpt: Opt[ParamList] = N
  
end ClassDef


case class TypeDef(
  sym: TypeAliasSymbol,
  bsym: BlockMemberSymbol,
  tparams: Ls[TyParam],
  rhs: Opt[Term],
  companion: Opt[CompanionValue],
  annotations: Ls[Annot],
)(val toLoc: Opt[Loc], val headerLoc: Opt[Loc]) extends TypeLikeDef:
  val kind: ObjDefKind = Als


// TODO Store optional source locations for the flags instead of booleans
/** `opt` marks an optional parameter (`y?`) or an optional function type parameter (`Int?`),
  * whose argument may be omitted by callers, in which case the parameter is `null`.
  * Unlike the other flags, which are prefix modifiers, it is written as a postfix `?`,
  * so it is not part of `show` and is printed by `showOptMarker` after the name instead.
  * `droppable` marks a parameter (`drop y`) or function type parameter (`drop Int`) whose argument
  * is always passed but which implementations may ignore, such as the index passed by `Array#map`
  * to its callback. Resolution permits callbacks to omit these parameters;
  * code generation already ignores extra arguments (see `Runtime.checkArgs`). */
final case class FldFlags(mut: Bool, spec: Bool, pat: Bool, isVal: Bool, opt: Bool, droppable: Bool):
  def show(addSpace: Bool = false): Str =
    val flags = Buffer.empty[String]
    if mut then flags += "mut"
    if spec then flags += "spec"
    if pat then flags += "pattern"
    if isVal then flags += "val"
    if droppable then flags += "drop"
    flags.mkString(" ") + (if addSpace && flags.nonEmpty then " " else "")
  def showOptMarker: Str = if opt then "?" else ""
  override def toString: String = "‹" + show(false) + showOptMarker + "›"

object FldFlags:
  val empty: FldFlags = FldFlags(false, false, false, false, false, false)
  /** The number of required (i.e., non-optional) parameters at the start of a parameter list.
    * Elaboration reports required parameters following optional ones; these are counted as optional,
    * since arguments are assigned to parameters positionally. */
  def requiredPrefixLength(flags: Ls[FldFlags]): Int = flags.indexWhere(_.opt) match
    case -1 => flags.length
    case n => n
  object benign:
    // * Some flags like `mut` and `module` are "benign" in the sense that they don't affect code-gen
    def unapply(flags: FldFlags): Bool =
      !flags.spec


enum IfLikeForm:
  case ReturningIf, ImperativeIf, While
  def isImperative: Bool = this match
    case ReturningIf => false
    case ImperativeIf | While => true
  def headStr: Str = this match
    case ReturningIf => "if"
    case ImperativeIf => "if"
    case While => "while"
  def midStr: Str = if isImperative then "do" else "then"


sealed abstract class Elem extends AutoLocated:
  def subTerms: Ls[Term] = this match
    case Fld(_, term, asc) => term :: asc.toList
    case Spd(_, term, _) => term :: Nil
  def show(using Scope, ShowCfg, Raise): Document
  def showDbg(using DebugPrinter): Str
object Elem:
  given Conversion[Term, Elem] = PlainFld(_)
final case class Fld(flags: FldFlags, term: Term, asc: Opt[Term]) extends Elem, FldImpl
object PlainFld:
  def apply(term: Term) = Fld(FldFlags.empty, term, N)
  def unapply(fld: Fld): Opt[Term] = S(fld.term)
/** `droppable` marks the rest parameter of a function type, as in `(Int, drop ...Array[Int]) -> Int`,
  * whose arguments implementations may ignore (see `FldFlags.droppable`). */
final case class Spd(k: SpreadKind, term: Term, droppable: Bool) extends Elem:
  private def dropStr = if droppable then "drop " else ""
  def show(using Scope, ShowCfg, Raise): Document = dropStr :: k.str :: term.show
  def showDbg(using DebugPrinter): Str = dropStr + k.str + term.showDbg
  def children: Vector[Located] = Vector.single(term)

final case class TyParam(flags: FldFlags, vce: Opt[Bool], sym: VarSymbol)(val toLoc: Opt[Loc]) extends Declaration:
  
  def showDbg(using DebugPrinter): Str =
    vce.fold("")(if _ then "out " else "in ") + "‹" + flags.show + "›" + sym.showDbg


object Param:
  def simple(sym: VarSymbol) = Param(FldFlags.empty, sym, N, Modulefulness.none)(sym.toLoc)

final case class Param(flags: FldFlags, sym: VarSymbol, sign: Opt[Term], modulefulness: Modulefulness)
(val toLoc: Opt[Loc]) extends Declaration:
  var fldSym: Opt[MemberSymbol] = N
  
  val flow: FlowSymbol = sym

  // * This field is filled in during flow analysis;
  // * it is not meant to be maintained afterwards (so it does not need to be copied around).
  var signType: Opt[Type] = N
  
  def withSignTypeOf(p: Param): this.type =
    signType = p.signType
    this
  
  def subTerms: Ls[Term] = sign.toList
  
  
  def show(using Scope, ShowCfg, Raise): Document =
    doc"${flags.show(true)}${sym.showName}${flags.showOptMarker}${sign.fold(doc"")(": " :: _.show)}"
  
  def showDbg(using DebugPrinter): Str =
    flags.show(true) + sym.showDbg + flags.showOptMarker + sign.fold("")(": " + _.showDbg)

/** A variadic parameter, as in `fun f(x, ...xs, y, z)`, which receives the arguments passed between
  * the leading parameters (`x`) and the `trailing` ones (`y` and `z`). The trailing parameters are
  * always required. When there are no trailing parameters, the variadic parameter is a rest parameter.
  * Lowering desugars trailing parameters into a rest parameter (see `Lowering.setupFunctionDef`). */
final case class Variadic[+P](param: P, trailing: Ls[P]):
  def map[Q](f: P => Q): Variadic[Q] = Variadic(f(param), trailing.map(f))
  def allParams: Ls[P] = param :: trailing

/** `params` are the leading parameters, which may end with optional parameters. */
final case class ParamList(flags: ParamListFlags, params: Ls[Param], variadic: Opt[Variadic[Param]])
(val toLoc: Opt[Loc]) extends Located:
  def foreach(f: Param => Unit): Unit = allParams.foreach(f)
  def trailingParams: Ls[Param] = variadic.fold(Nil)(_.trailing)
  /** The number of required leading parameters, which precede all optional parameters. */
  lazy val leadingRequiredCount: Int = FldFlags.requiredPrefixLength(params.map(_.flags))
  /** The minimum number of arguments: the required leading and trailing parameters. */
  def paramCountLB: Int = leadingRequiredCount + trailingParams.length
  /** The maximum number of arguments, when there is no variadic parameter. */
  def paramCountMax: Int = params.length + trailingParams.length
  def hasOptParams: Bool = leadingRequiredCount < params.length
  def paramCountUB: Bool = variadic.isEmpty
  lazy val allParams: Ls[Param] = params ::: variadic.fold(Nil)(_.allParams)
  lazy val paramSyms = allParams.map(_.sym)
  def subTerms: Ls[Term] = allParams.flatMap(_.subTerms)
  def show(using Scope, ShowCfg, Raise): Document =
    flags.show
    :: doc"(" :: (
      params.map(_.show)
      :::
      variadic.toList.flatMap(v => doc"...${v.param.show}" :: v.trailing.map(_.show))
    ).mkDocument(", ")
    :: doc")"
  def showDbg(using DebugPrinter): Str = flags.showDbg
    + (params.map(_.showDbg) ++ variadic.toList.flatMap(v => ("..." + v.param.showDbg) :: v.trailing.map(_.showDbg)))
      .mkString("(", ", ", ")")
object ParamList:
  /** A source parameter list with no trailing parameters after its variadic parameter. */
  def withRest(flags: ParamListFlags, params: Ls[Param], restParam: Opt[Param])(toLoc: Opt[Loc]): ParamList =
    ParamList(flags, params, restParam.map(Variadic(_, Nil)))(toLoc)
object PlainParamList:
  def apply(params: Ls[Param])(toLoc: Opt[Loc]) =
    ParamList(ParamListFlags.empty, params, N)(toLoc)
  def unapply(pl: ParamList): Opt[Ls[Param]] = pl match
    case ParamList(ParamListFlags.empty, params, N) => S(params)
    case _ => N

final case class ParamListFlags(ctx: Bool):
  def show: Str = (if ctx then "ctx " else "")
  def showDbg: Str = (if ctx then "ctx " else "")
  override def toString: String = "‹" + showDbg + "›"

/** A subtyping direction. */
enum SubDir:
  case Sub, Sup
  def showDbg: Str = this match
    case Sub => "<:"
    case Sup => ":>"

/** A subtyping constraint. */
final case class SubConstraint(lhs: Term, rhs: Term, dir: SubDir) extends AutoLocated:
  override protected def children: Vector[Located] = Vector(lhs, rhs)
  def showDbg(using DebugPrinter): Str = s"${lhs.showDbg} ${dir.showDbg} ${rhs.showDbg}"
  def subTerms: Ls[Term] = List(lhs, rhs)

object ParamListFlags:
  val empty = ParamListFlags(false)


/**
 * Unwrapper that unwraps a term until it is no longer an App.
 */
object Apps:
  def unapply(t: Term): S[(Term, Ls[Term])] = t match
    case Term.App(Apps(base, args), arg) => S(base, args :+ arg)
    case t => S(t, Nil)

