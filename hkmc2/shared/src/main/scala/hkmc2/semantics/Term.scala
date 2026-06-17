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


final case class QuantVar(sym: VarSymbol, ub: Opt[Term], lb: Opt[Term])

enum Annot extends AutoLocated:
  case Untyped
  case Modifier(mod: Keyword)
  case Trm(trm: Term)
  // NOTE: The presence of TailRec and TailCall annotations does not affect whether a function is optimized or not;
  // it only affects whether a warning is thrown if the function/call is not actually tail-recursive.
  case TailRec
  case TailCall
  case Inline
  // Whether the function is guaranteed to not raise effects.
  case MayNotRaiseEffects
  case Config(modify: hkmc2.Config => hkmc2.Config)
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
  case Affine(whichParamList: Int)
  
  def symbol: Opt[Symbol] = this match
    case Trm(trm) => trm.symbol
    case _ => N
  
  def subTerms: Vector[Term] = this match
    case Trm(trm) => Vector.single(trm)
    case _: Modifier | Untyped | TailRec | TailCall | Inline
      | MayNotRaiseEffects | _: Config | _: Affine => Vector.empty
  
  def children: Vector[Located] = this match
    case Trm(trm) => Vector.single(trm)
    // case Modifier(kw) => Vector.single(kw) // TODO: make `kw` a `Keywrd`
    case _: Modifier | Untyped | TailRec | TailCall | Inline
      | MayNotRaiseEffects | _: Config | _: Affine => Vector.empty
  
  def show(using Scope, ShowCfg, Raise): Document = this match
    case Untyped => doc"@untyped"
    case Inline => doc"@inline"
    case TailRec => doc"@tailrec"
    case TailCall => doc"@tailcall"
    case Affine(n) => doc"@affine($n)"
    case Modifier(mod) => doc"@${mod.name}"
    case MayNotRaiseEffects => doc"@mayNotRaiseEffects"
    case Trm(trm) => doc"@${trm.show}"
    case Config(_) => doc"@config(...)"
  
  def mkClone(using State): Annot = this match
    case Untyped => Untyped
    case Modifier(mod) => Modifier(mod)
    case Trm(trm) => Trm(trm.mkClone)
    case TailRec => TailRec
    case TailCall => TailCall
    case Inline => Inline
    case MayNotRaiseEffects => MayNotRaiseEffects
    case c: Config => c
    case a: Affine => a

object Annot:
  
  val Private = Modifier(Keyword.`private`)
  
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
  var isErroneous: Bool = false // * to avoid reporting follow-on errors after a flow/resolution error
end AnySel

object AnySel:
  def unapply(t: AnySelTerm): S[(Term, Tree.Ident, Opt[Term])] = t match
    case Term.Sel(lhs, id) => S((lhs, id, N))
    case Term.SynthSel(lhs, id) => S((lhs, id, N))
    case Term.SelProj(lhs, cls, proj) => S((lhs, proj, S(cls)))
end AnySel

type Resolvable = Term & ResolvableImpl

sealed trait ResolvableImpl:
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
      case t: Term.Ref => t.copy()(t.tree, t.refNum, t.typ)
      case t: Term.App => t.copy()(t.tree, t.typ, t.resSym)
      case t: Term.TyApp => t.copy()(t.typ)
      case t: Term.Sel => t.copy()(t.sym, t.resSym, t.typ, t.originalCtx)
      case t: Term.SynthSel => t.copy()(t.sym, t.resSym, t.typ, t.originalCtx)
      case t: Term.LeadingDotSel => t.copy()(t.originalCtx)
      case t: Term.SelProj => t.copy()(t.sym, t.resSym, t.typ, t.originalCtx)
      case t: Term.New => t.copy()(t.typ)
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
      case t: Term.Ref => t.copy()(t.tree, t.refNum, S(typ))
      case t: Term.App => t.copy()(t.tree, S(typ), t.resSym)
      case t: Term.TyApp => t.copy()(S(typ))
      case t: Term.Sel => t.copy()(t.sym, t.resSym, S(typ), t.originalCtx)
      case t: Term.SynthSel => t.copy()(t.sym, t.resSym, S(typ), t.originalCtx)
      case _: Term.LeadingDotSel => lastWords(s"Cannot attach a type to leading dot selection: ${this.showDbg}")
      case t: Term.SelProj => t.copy()(t.sym, t.resSym, S(typ), t.originalCtx)
      case t: Term.New => t.copy()(S(typ))
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
    // `expansion.isDefined`: Ideally, if a term is already expanded,
    // one should look at the term's expansion and expand it again. This
    // check is to prevent one from mistakenly overriding an expansion
    // without looking at the instantiation.
    //
    // `expansion.get =/= newExpansion`: Waiting for @Luyu to revamp the
    // desugaring stage so that no same term occurs in different places.
    if this.expansion.isDefined && this.expansion.get =/= expansion then
      lastWords(s"Cannot expand the term ${this} multiple times (to different expansions ${expansion.get}).")
    
    this.expansion = S(expansion)
    this
    
  def resolve: this.type = expand(N)
  def dontResolve: this.type = this // TODO rm
  
  /**
   * A helper function to create a resolved term for this term.
   */
  def resolved(sym: DefinitionSymbol[?]): Term.Resolved =
    Term.Resolved(this, sym)(typ = resolvedTyp)
  
  def hasExpansion = expansion.isDefined
  
  def defn: Opt[Definition] = resolvedSym match
    case S(sym: BlockMemberSymbol) => N
    case S(sym: DefinitionSymbol[?]) => sym.defn
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
        else S(defn.tparams.map(tp => Param(FldFlags.empty, tp.sym, N, Modulefulness.none))), 
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
        else S(defn.tparams.map(tp => Param(FldFlags.empty, tp.sym, N, Modulefulness.none))), 
        N, // TODO: handle class-like definitions with signatures
        TermDefFlags.empty, // TODO: handle class-like definitions with flags
        Modulefulness.none, // TODO: handle modulefulness for class-like definitions
        defn,
      ))

trait LeadingDotSelImpl(using State):
  self: Term.LeadingDotSel =>
  val resSym: FlowSymbol = FlowSymbol.lds(self.nme.name)
  var resolvedTargets: Ls[flow.SelectionTarget.CompanionMember] = Nil // * filled during flow analysis

case class SrcScope(outer: Elaborator.OuterCtx, parent: Opt[SrcScope]):
  
  /** Computes the outermost scope from which the current scope can still be accessed.
    * For instance, from [scp2] here, [scp1] is the outermost accessible base:
    *     [scp0]
    *     fun foo =
    *       [scp1]
    *       module Foo with
    *         module Bar with
    *           [scp2]
    * and the path is Foo :: Bar :: Nil.
    * [scp0] cannot access [scp2] because there is a function (Function outer) on the way.
    * The same would happen for:
    *     [scp0]
    *     if ... then // LocalScope also blocks access to [scp1] and [scp2]
    *       [scp1]
    *       module Foo with
    *         module Bar with
    *           [scp2]
    */
  lazy val outermostAcessibleBase: (SrcScope, Ls[InnerSymbol]) =
      import Elaborator.OuterCtx.*
      outer match
      case InnerScope(inner) =>
        parent match
        case N => (this, inner :: Nil)
        case S(par) =>
          val (base, path) = par.outermostAcessibleBase
          (base, inner :: path)
      case _: (Function | LocalScope) | LambdaOrHandlerBlock | NonReturnContext =>
        (this, Nil)

object SrcScope:
  given s: Ctx => SrcScope = summon[Ctx].scope

enum Term extends Statement:
  case Error()
  case UnitVal()
  case Missing // Placeholder terms that were not elaborated due to the "lightweight" elaboration mode `Mode.Light`
  case Lit(lit: Literal)
  /** A term that wraps another term, indicating that the symbol of the inner term is resolved.
    * This is mainly used to disambiguate overloaded definitions. */
  case Resolved(t: Term, sym: DefinitionSymbol[?])
    (val typ: Opt[Type]) extends Term, ResolvableImpl
  case Ref(sym: Symbol)
    (val tree: Tree.Ident, val refNum: Int, val typ: Opt[Type]) extends Term, ResolvableImpl
  case App(lhs: Term, rhs: Term)
    (val tree: Tree.App, val typ: Opt[Type], val resSym: FlowSymbol) extends Term, ResolvableImpl
  case TyApp(lhs: Term, targs: Ls[Term])
    (val typ: Opt[Type]) extends Term, ResolvableImpl
  case Sel(prefix: Term, nme: Tree.Ident)
    (val sym: Opt[MemberSymbol], val resSym: FlowSymbol, val typ: Opt[Type], val originalCtx: Opt[SrcScope])
    extends Term, AnySel
  case SynthSel(prefix: Term, nme: Tree.Ident)
    (val sym: Opt[MemberSymbol], val resSym: FlowSymbol, val typ: Opt[Type], val originalCtx: Opt[SrcScope])
    extends Term, AnySel
  case SelProj(prefix: Term, cls: Term, nme: Tree.Ident)
    (val sym: Opt[MemberSymbol], val resSym: FlowSymbol, val typ: Opt[Type], val originalCtx: Opt[SrcScope])
    extends Term, AnySel
  case DynSel(prefix: Term, fld: Term, arrayIdx: Bool)
  case Tup(fields: Ls[Elem])(val tree: Tree.Tup)
  case Mut(underlying: Tup | Rcd | New | DynNew)
  case CtxTup(fields: Ls[Elem])(val tree: Tree.Tup)
  case IfLike(kw: Keyword.SplitLike, form: IfLikeForm, split: SimpleSplit)
  /** `If` expressions synthesized by the pattern compiler. It should only be
   *  created and used in `Lowering`. One must make sure that all terms in the
   *  split are correctly resolved. In the future, we might look for a way to
   *  remove `SynthIf` by generating IR `Match` blocks directly. */
  case SynthIf(split: Split)
  case Lam(params: ParamList, body: Term)
  case FunTy(lhs: Term, rhs: Term, eff: Opt[Term])
  case Forall(tvs: Ls[QuantVar], outer: Opt[VarSymbol], body: Term)
  case Constrained(constraints: Ls[SubConstraint], body: Term)
  case WildcardTy(in: Opt[Term], out: Opt[Term])
  case Blk(stats: Ls[Statement], res: Term) extends Term, BlkImpl
  case Rcd(mut: Bool, stats: Ls[Statement])
  case Quoted(body: Term)
  case Unquoted(body: Term)
  case New(cls: Term, args: Ls[Term], rft: Opt[ClassSymbol -> ObjBody])
    (val typ: Opt[Type]) extends Term, ResolvableImpl
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
    derivedClsSym: ClassSymbol, defs: Ls[HandlerTermDefinition], body: Term)
  case LeadingDotSel(nme: Tree.Ident)(
      val originalCtx: Opt[SrcScope]
    ) (using State) extends Term, ResolvableImpl, LeadingDotSelImpl
  
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
    case res: Resolved => S(res.sym)
    case Ref(sym) => S(sym)
    case sel: Sel => sel.sym
    case sel: SynthSel => sel.sym
    case sel: SelProj => sel.sym
    case TyApp(lhs = lhs) => lhs.symbol
    case _ => N
  
  /**
   * The symbol representing the evaluation result of the term. This
   * symbol is resolved during the resolution stage.
   */
  def resolvedSym: Opt[Symbol] = expanded match
    case res: Resolved => S(res.sym)
    case ref: Ref => ref.symbol
    case sel: Sel => sel.sym
    case sel: SynthSel => sel.sym
    case sel: SelProj => sel.sym
    case app: TyApp => app.lhs.resolvedSym
    case _ => N
  
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
    case Lam(params, body) =>
      val paramNames = params.allParams.iterator.map(_.sym.nme).toSet
      body.freeVars -- paramNames
    case Blk(stats, res) =>
      Term.blkFreeVars(stats, res.freeVars)
    case IfLike(_, _, split) => split.freeVars
    case SynthIf(split) => split.freeVars
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
    case Error | Missing | _: Lit | _: UnitVal | _: LeadingDotSel | _: Continue => Set.empty
    case Break(_, result, value) => value.iterator.flatMap(_.freeVars).toSet + result.nme
    case _ => subTerms.iterator.flatMap(_.freeVars).toSet

  def sel(id: Tree.Ident, sym: Opt[MemberSymbol])(using State, Elaborator.Ctx): Sel =
    Sel(this, id)(sym, FlowSymbol.sel(id.name), N, S(summon))
  def selNoSym(nme: Str, synth: Bool = false)(using State, Elaborator.Ctx): Sel | SynthSel =
    val id = new Tree.Ident(nme)
    if synth
    then SynthSel(this, id)(N, FlowSymbol.synthSel(nme), N, S(summon))
    else sel(id, N)
  
  def app(args: Term*)(using State) =
    App(this, Tup(args.toList.map(PlainFld(_)))(Tree.DummyTup))
      (Tree.App(Tree.Dummy, Tree.Dummy), N, FlowSymbol(""))
  
  override def mkClone(using State): Term = 
    val that = this match
      case Error() => Error()
      case UnitVal() => UnitVal()
      case Missing => Missing
      case Lit(Tree.StrLit(value)) => Lit(Tree.StrLit(value))
      case Lit(Tree.IntLit(value)) => Lit(Tree.IntLit(value))
      case Lit(Tree.DecLit(value)) => Lit(Tree.DecLit(value))
      case Lit(Tree.BoolLit(value)) => Lit(Tree.BoolLit(value))
      case Lit(Tree.UnitLit(value)) => Lit(Tree.UnitLit(value))
      case term @ Resolved(t, sym) => Resolved(t.mkClone, sym)(term.typ)
      case term @ Ref(sym) => Ref(sym)(Tree.Ident(term.tree.name), term.refNum, term.typ)
      case term @ App(lhs, rhs) => App(lhs.mkClone, rhs.mkClone)(term.tree, term.typ, term.resSym)
      case term @ TyApp(lhs, targs) => TyApp(lhs.mkClone, targs.map(_.mkClone))(term.typ)
      case term @ Sel(prefix, nme) => Sel(prefix.mkClone, Tree.Ident(nme.name))(term.sym, term.resSym, term.typ, term.originalCtx)
      case term @ SynthSel(prefix, nme) => SynthSel(prefix.mkClone, Tree.Ident(nme.name))(term.sym, term.resSym, term.typ, term.originalCtx)
      case term @ LeadingDotSel(nme) => LeadingDotSel(Tree.Ident(nme.name))(term.originalCtx)
      case DynSel(prefix, fld, arrayIdx) => DynSel(prefix.mkClone, fld.mkClone, arrayIdx)
      case term @ Tup(fields) => Tup(fields.map {
        case f: Fld => f.copy(term = f.term.mkClone, asc = f.asc.map(_.mkClone))
        case s: Spd => s.copy(term = s.term.mkClone)
      })(term.tree)
      case Mut(underlying) => Mut(underlying.mkClone.asInstanceOf[Tup | Rcd | New | DynNew])
      case term @ CtxTup(fields) => CtxTup(fields.map {
        case f: Fld => f.copy(term = f.term.mkClone, asc = f.asc.map(_.mkClone))
        case s: Spd => s.copy(term = s.term.mkClone)
      })(term.tree)
      case IfLike(kw, form, split) => IfLike(kw, form, split.mkClone)
      case SynthIf(split) => SynthIf(split.mkClone)
      case Lam(params, body) => Lam(params, body.mkClone)
      case FunTy(lhs, rhs, eff) => FunTy(lhs.mkClone, rhs.mkClone, eff.map(_.mkClone))
      case Forall(tvs, outer, body) => Forall(tvs, outer, body.mkClone)
      case Constrained(constraints, body) => Constrained(constraints, body.mkClone)
      case WildcardTy(in, out) => WildcardTy(in.map(_.mkClone), out.map(_.mkClone))
      case blk: Blk => blk.mkBlkClone
      case Rcd(mut, stats) => Rcd(mut, stats.map(_.mkClone))
      case Quoted(body) => Quoted(body.mkClone)
      case Unquoted(body) => Unquoted(body.mkClone)
      case term @ New(cls, args, rft) =>
        New(cls.mkClone, args.map(_.mkClone), rft.map { case (cs, ob) => cs -> ObjBody(ob.blk.mkBlkClone) })(term.typ)
      case DynNew(cls, args) => DynNew(cls.mkClone, args.map(_.mkClone))
      case term @ SelProj(prefix, cls, proj) =>
        SelProj(prefix.mkClone, cls.mkClone, Tree.Ident(proj.name))(term.sym, term.resSym, term.typ, term.originalCtx)
      case Asc(term, ty) => Asc(term.mkClone, ty.mkClone)
      case CompType(lhs, rhs, pol) => CompType(lhs.mkClone, rhs.mkClone, pol)
      case Neg(rhs) => Neg(rhs.mkClone)
      case Region(name, body) => Region(name, body.mkClone)
      case RegRef(reg, value) => RegRef(reg.mkClone, value.mkClone)
      case Assgn(lhs, rhs) => Assgn(lhs.mkClone, rhs.mkClone)
      case Drop(trm) => Drop(trm.mkClone)
      case Deref(ref) => Deref(ref.mkClone)
      case SetRef(ref, value) => SetRef(ref.mkClone, value.mkClone)
      case Ret(result) => Ret(result.mkClone)
      case Throw(result) => Throw(result.mkClone)
      case Label(label, result, body, hasNonLocalContinueDispatch) => Label(label, result, body.mkClone, hasNonLocalContinueDispatch)
      case Break(label, result, value) => Break(label, result, value.map(_.mkClone))
      case Continue(label) => Continue(label)
      case Try(body, finallyDo) => Try(body.mkClone, finallyDo.mkClone)
      case Annotated(annot, target) => Annotated(annot, target.mkClone)
      case Handle(lhs, rhs, args, derivedClsSym, defs, body) =>
        Handle(lhs, rhs.mkClone, args.map(_.mkClone), derivedClsSym, defs, body.mkClone)
    (this, that) match
      case (self: Resolvable, that: Resolvable) if self.expansion.isDefined =>
        that.expand(self.expansion.get.map(_.mkClone))
      case _ =>
        that
  
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
    showFlowSymbols = true,
    showExpansionMappings = false,
    debug = false,
  )
end ShowCfg


sealed trait Statement extends AutoLocated, ProductWithExtraInfo:
  
  def mkClone(using State): Statement = this match
    case t: Term => lastWords(s"overridden implementation")
    case d: Definition => ???
    case imp: Import => Import(imp.sym, imp.str, imp.file)
    case LetDecl(sym, annotations) => LetDecl(sym, annotations.map(_.mkClone))
    case RcdField(field, rhs) => RcdField(field.mkClone, rhs.mkClone)
    case RcdSpread(rcd) => RcdSpread(rcd.mkClone)
    case DefineVar(sym, rhs) => DefineVar(sym, rhs.mkClone)
    case sc: SetConfig => sc
  
  def describe: Str =
    val desc = this match
      case Error() => "‹error›"
      case UnitVal() => "unit value"
      case Lit(lit) => lit.describeLit
      case Ref(sym) => "reference"
      case App(lhs, rhs) => "application"
      case TyApp(lhs, targs) => "type application"
      case Sel(pre, nme) => "selection"
      case SynthSel(pre, nme) => "selection"
      case DynSel(o, f, _) => "dynamic selection"
      case Tup(fields) => "tuple literal"
      case CtxTup(fields) => "contextual tuple literal"
      case IfLike(_, IfLikeForm.ReturningIf, body) => "`if` expression"
      case IfLike(_, IfLikeForm.ImperativeIf, body) => "`if` statement"
      case IfLike(_, IfLikeForm.While, body) => "`while` statement"
      case SynthIf(split) => "synthetic `if` expression"
      case Lam(params, body) => "function literal"
      case FunTy(lhs, rhs, eff) => "function type"
      case Forall(tvs, outer, body) => "universal quantification"
      case Constrained(constraints, body) => "constrained type"
      case WildcardTy(in, out) => "wildcard type"
      case Blk(stats, res) => "block"
      case Quoted(term) => "quoted term"
      case Unquoted(term) => "unquoted term"
      case New(cls, args, rft) => "object creation"
      case SelProj(pre, cls, proj) => "field selection"
      case Asc(term, ty) => "type ascription"
      case CompType(lhs, rhs, pol) => if pol then "alternation" else "composition"
      case Neg(rhs) => "negation type"
      case Region(name, body) => "region expression"
      case RegRef(reg, value) => "reference creation"
      case Assgn(lhs, rhs) => "assignment"
      case SetRef(ref, value) => "mutable reference assignment"
      case Drop(ref) => "drop"
      case Deref(ref) => "dereference"
      case Throw(e) => "throw"
      case Label(label, _, _, _) => s"label '${label.nme}'"
      case Break(label, _, _) => s"break to label '${label.nme}'"
      case Continue(label) => s"continue to label '${label.nme}'"
      case Annotated(annotation, target) => "annotation"
      case Ret(res) => "return"
      case Try(body, finallyDo) => "try expression"
      case Missing => "missing"
      case LeadingDotSel(name) => "leading dot selection"
      case Resolved(t, sym) => t.describe
      case s => TODO(s)
    this match
      case self: Resolvable => self.resolvedTyp match
        case S(typ) => s"${desc} of type ${typ.show}"
        case N => desc
      case _ => desc
  
  def extraInfo(using DebugPrinter): Str = this match
    case r: Resolvable if r.resolvedSym.isDefined || r.resolvedTyp.isDefined => (
        r.resolvedSym.map(s => s"sym=${s.showAsPlain}") ::
        r.resolvedTyp.map(s => s"typ=${s.showDbg}") :: Nil
      ).flatten.mkString(",")
    case r: SelProj => r.symbol.mkString
    case _ => ""
  
  def subStatements: Vector[Statement] = this match
    case Blk(stats, res) => stats.toVector :+ res
    case _ => subTerms
  def subTerms: Vector[Term] = this match
    case Error() | Missing | _: Lit | _: Ref | _: UnitVal => Vector.empty
    case Resolved(t, sym) => Vector.single(t)
    case App(lhs, rhs) => Vector.double(lhs, rhs)
    case RcdField(lhs, rhs) => Vector.double(lhs, rhs)
    case RcdSpread(bod) => Vector.single(bod)
    case FunTy(lhs, rhs, eff) => Vector.double(lhs, rhs) ++ eff.toVector
    case TyApp(pre, tarsg) => pre +: tarsg.toVector
    case Sel(pre, _) => Vector.single(pre)
    case SynthSel(pre, _) => Vector.single(pre)
    case DynSel(o, f, _) => Vector.double(o, f)
    case Tup(fields) => fields.flatMap(_.subTerms).toVector
    case Mut(und) => Vector.single(und)
    case CtxTup(fields) => fields.flatMap(_.subTerms).toVector
    case IfLike(_, _, split) => split.subTerms
    case SynthIf(split) => split.subTerms
    case Lam(params, body) => params.allParams.iterator.flatMap(_.sign).toVector :+ body
    case Blk(stats, res) => stats.flatMap(_.subTerms).toVector :+ res
    case Rcd(mut, stats) => stats.flatMap(_.subTerms).toVector
    case Quoted(term) => Vector.single(term)
    case Unquoted(term) => Vector.single(term)
    case New(cls, args, rft) => (cls +: args.toVector) ++ rft.toVector.flatMap(_._2.blk.subTerms)
    case DynNew(cls, args) => cls +: args.toVector
    case SelProj(pre, cls, _) => Vector.double(pre, cls)
    case Asc(term, ty) => Vector.double(term, ty)
    case Ret(res) => Vector.single(res)
    case Throw(res) => Vector.single(res)
    case Label(_, _, body, _) => Vector.single(body)
    case Break(_, _, value) => value.toVector
    case Continue(_) => Vector.empty
    case Forall(_, _, body) => Vector.single(body)
    case Constrained(constraints, body) => constraints.flatMap(_.subTerms).toVector :+ body
    case WildcardTy(in, out) => in.toVector ++ out.toVector
    case CompType(lhs, rhs, _) => Vector.double(lhs, rhs)
    case LetDecl(sym, annotations) => annotations.flatMap(_.subTerms).toVector
    case DefineVar(sym, rhs) => Vector.single(rhs)
    case Region(_, body) => Vector.single(body)
    case RegRef(reg, value) => Vector.double(reg, value)
    case Assgn(lhs, rhs) => Vector.double(lhs, rhs)
    case SetRef(lhs, rhs) => Vector.double(lhs, rhs)
    case Drop(term) => Vector.single(term)
    case Deref(term) => Vector.single(term)
    case TermDefinition(_, _, _, pss, tps, sign, body, _, _, annotations, _) =>
      pss.toVector.flatMap(_.subTerms) ++ tps.getOrElse(Nil).flatMap(_.subTerms).toVector ++ sign.toVector ++ body.toVector ++ annotations.flatMap(_.subTerms).toVector
    case cls: ClassDef =>
      (cls.paramsOpt.toVector.flatMap(_.subTerms) :+ cls.body.blk) ++ cls.annotations.flatMap(_.subTerms).toVector
    case mod: ModuleOrObjectDef =>
      ( mod.paramsOpt.toVector.flatMap(_.subTerms) :+ mod.body.blk) ++ mod.annotations.flatMap(_.subTerms).toVector
    case td: TypeDef =>
      td.rhs.toVector ++ td.annotations.flatMap(_.subTerms).toVector
    case pat: PatternDef =>
      (pat.paramsOpt.toVector.flatMap(_.subTerms) :+ pat.body.blk) ++ pat.annotations.flatMap(_.subTerms).toVector
    case Import(sym, str, pth) => Vector.empty
    case Try(body, finallyDo) => Vector.single(body) ++ Vector.single(finallyDo)
    case Handle(lhs, rhs, args, derivedClsSym, defs, bod) => (rhs +: args.toVector) ++ defs.flatMap(_.td.subTerms).toVector :+ bod
    case Neg(e) => Vector.single(e)
    case Annotated(ann, target) => ann.subTerms ++ Vector.single(target)
    case LeadingDotSel(nme) => Vector.empty
    case SetConfig(_) => Vector.empty
  
  // private def treeOrSubterms(t: Tree, t: Term): Ls[Located] = t match
  private def treeOrSubterms(t: Tree): Vector[Located] = t match
    case Tree.DummyApp | Tree.DummyTup => subTerms
    case _ => Vector.single(t)
  
  protected def children: Vector[Located] = this match
    case t: Lit => Vector.single(t.lit.asTree)
    case t: Ref => treeOrSubterms(t.tree)
    case t: Tup => treeOrSubterms(t.tree)
    case l: Lam => Vector.double(l.params, l.body)
    case t: App => treeOrSubterms(t.tree)
    case IfLike(_, _, split) => Vector.single(split)
    case SynthIf(split) => Vector.single(split)
    case SynthSel(pre, nme) => Vector.double(pre, nme)
    case Sel(pre, nme) => Vector.double(pre, nme)
    case SelProj(prefix, cls, proj) => Vector.triple(prefix, cls, proj)
    case _ =>
      subTerms // TODO more precise (include located things that aren't terms)
  
  def show(using Scope, ShowCfg, Raise): Document =
    def res: Document = this match
      case lit: Lit => lit.lit.idStr
      case r: Ref =>
        r.sym match
        case _: BuiltinSymbol => r.sym.nme
        case _ => r.sym.showName
      case sel: Sel =>
        if summon[ShowCfg].showFlowSymbols
        then doc"${sel.prefix.show}.${sel.sym.fold(doc"${sel.nme.name}‹?›")(_.showName)}"
        else doc"${sel.prefix.show}.${sel.nme.name}"
      case sel: SynthSel =>
        if summon[ShowCfg].showFlowSymbols
        then doc"⟨${sel.prefix.show}.⟩${sel.sym.fold(doc"${sel.nme.name}‹?›")(_.showName)}"
        else doc"${sel.prefix.show}.${sel.nme.name}"
      case Resolved(trm, sym) =>
        trm.show
      case app: App =>
        doc"${app.lhs.show}${app.rhs.showAsParams}${
          if summon[ShowCfg].showFlowSymbols
          then
            summon[ShowCfg].shownSymbols.add(app.resSym)
            "‹" :: app.resSym.showPlainName :: "›"
          else ""
        }"
      case lam: Lam => doc"${lam.params.show} => ${lam.body.show}"
      case nw: New => doc"new ${nw.cls.show}${nw.args.map(_.showAsParams).mkDocument()}${
        nw.rft.fold(doc"")(doc" with " :: _._2.blk.show)}"
      case tup: Tup => bracketed("[", "]", insertBreak = true):
        tup.fields.map(_.show).mkDocument(doc", # ")
      case blk: Blk => braced:
        doc" # " :: (blk.stats :::
            blk.res.match
            case Lit(Tree.UnitLit(false)) => Nil
            case res => res :: Nil
          ).map(_.show).mkDocument(doc", # ")
      case ld: LetDecl =>
        (ld.annotations.map(_.show) ::: doc"let ${ld.sym.showName}" :: Nil).mkDocument()
      case df: DefineVar =>
        doc"${df.sym.showName} = ${df.rhs.show}"
      case td: TermDefinition =>
          td.annotations.map(_.show).mkDocument()
          :: doc"${td.k.str} ${td.sym.showName}"
          :: (if td.tparams.isEmpty then doc""
            else doc"[${td.tparams.get.map(_.sym.showName).mkDocument(", ")}]")
          :: td.params.map(_.show).mkDocument()
          :: td.sign.fold(doc"")(s => doc": ${s.show}")
          :: (if summon[ShowCfg].showFlowSymbols then doc" ‹${td.bsym.flow.showName}›" else doc"")
          :: td.body.fold(doc"")(b => doc" = ${b.show}")
      case cld: ClassLikeDef =>
          cld.annotations.map(_.show).mkDocument()
          :: doc"${cld.kind.str} ${cld.sym.nme}"
          :: (if cld.tparams.isEmpty then doc""
            else doc"[${cld.tparams.map(_.sym.showName).mkDocument(", ")}]")
          :: cld.paramsOpt.map(_.show).toList.mkDocument()
          :: cld.auxParams.map(_.show).mkDocument()
          :: doc" ${cld.body.blk.show}"
      case imp: Import =>
        doc"import ${"\""}.../${imp.file.last}${"\""} as ${imp.sym.showName}"
      case LeadingDotSel(name) => doc"_?_.${name.name}"
      case Error() => doc"‹error›"
      case _ =>
        doc"TODO[show:${getClass.getSimpleName}](${toString})"
    this match
    case t: Resolvable => t.expansion match
      case S(S(exp)) =>
        val rhs = exp.show(using summon, summon[ShowCfg].copy(showExpansionMappings = false))
        if summon[ShowCfg].showExpansionMappings then
          if exp === t then rhs
          // ^ Some expansions only modify meta-data, such as types and symbols;
          //    we don't print them for conciseness
          else res :: doc"{ ~> " :: rhs :: doc" }"
        else exp.show
      case _ => res
    case _ => res
  
  def size: Int = this match
    case Lit(Tree.StrLit(str)) => str.size / 4 + 1
    case _ => subTerms.iterator.map(_.size).sum + 1
  
  def showDbg(using DebugPrinter): Str = this match
    case r: Ref => r.sym.showAsPlain
    case r: Resolved =>
      s"${r.showPlain}‹${r.sym}›"
    case trm: Term =>
      // s"$showPlain‹${trm.symbol.getOrElse("")}›"
      s"$showPlain${trm.symbol.fold("")("‹"+_+"›")}"
    case _ =>
      showPlain

  def showAsParams(using Scope, ShowCfg, Raise): Document = this match
    case tup: Tup => doc"(${tup.fields.map(_.show).mkDocument(", ")})"
    case _ => doc"(...$show)"
  
  def showDbgAsParams(using DebugPrinter): Str = this match
    case tup: Tup => s"(${tup.fields.map(_.showDbg).mkString(", ")})"
    case _ => s"(...$showDbg)"
  
  def showPlain(using DebugPrinter): Str = this match
    case Term.UnitVal() => "()"
    case Lit(lit) => lit.idStr
    case Resolved(t, sym) => t.showPlain
    case r @ Ref(symbol) => symbol.toString + symbol.getState.dbgRefNum(r.refNum)
    case App(lhs, rhs) => s"${lhs.showDbg}${rhs.showDbgAsParams}"
    case RcdField(lhs, rhs) => s"${lhs.showDbg}: ${rhs.showDbg}"
    case RcdSpread(bod) => s"...${bod.showDbg}"
    case FunTy(lhs: Tup, rhs, eff) =>
      s"${lhs.fields.map(_.showDbg).mkString(", ")} ->${
        eff.map(e => s"{${e.showDbg}}").getOrElse("")} ${rhs.showDbg}"
    case FunTy(lhs, rhs, eff) =>
      s"(...${lhs.showDbg}) ->${eff.map(e => s"{${e.showDbg}}").getOrElse("")} ${rhs.showDbg}"
    case TyApp(lhs, targs) => s"${lhs.showDbg}[${targs.mkString(", ")}]"
    case Forall(tvs, outer, body) => s"forall ${tvs.mkString(", ")}${outer.map(v => s", outer $v").mkString}: ${body.toString}"
    case Constrained(constraints, body) => s"[${constraints.map(_.showDbg).mkString(", ")}] => ${body.showDbg}"
    case WildcardTy(in, out) => s"in ${in.map(_.toString).getOrElse("⊥")} out ${out.map(_.toString).getOrElse("⊤")}"
    case Sel(pre, nme) => s"${pre.showDbg}.${nme.name}"
    case SynthSel(pre, nme) => s"(${pre.showDbg}.)${nme.name}"
    case DynSel(pre, fld, _) => s"${pre.showDbg}[${fld.showDbg}]"
    case IfLike(kw, _, split) => s"${kw.name} { ${split.showDbg} }"
    case SynthIf(split) => s"if { ${split.showDbg} }"
    case Lam(params, body) => s"λ${params.showDbg}. ${body.showDbg}"
    case Blk(stats, res) =>
      (stats.map(_.showDbg + "; ") :+ (res match { case Lit(Tree.UnitLit(false)) => "" case x => x.showDbg + " " }))
      .mkString("{ ", "", "}")
    case Rcd(mut, stats) =>
      (if mut then "mut " else "") + stats.map(_.showDbg + "; ").mkString("{ ", "", "}")
    case Quoted(term) => s"""code"${term.showDbg}""""
    case Unquoted(term) => s"$${${term.showDbg}}"
    case New(cls, args, rft) =>
      s"new ${cls.showDbg}${args.map(_.showDbgAsParams).mkString}${rft.fold("")(r => s"{ ${r._2.blk.showDbg} }")}"
    case DynNew(cls, args) =>
      s"new! ${cls.showDbg}${args.map(_.showDbgAsParams).mkString}"
    case SelProj(pre, cls, proj) => s"${pre.showDbg}.${cls.showDbg}#${proj.name}"
    case Asc(term, ty) => s"${term.toString}: ${ty.toString}"
    case LetDecl(sym, _) => s"let ${sym}"
    case DefineVar(sym, rhs) => s"${sym} = ${rhs.showDbg}"
    case Handle(lhs, rhs, args, derivedClsSym, defs, bod) =>
      s"handle ${lhs} = ${rhs}(${args.mkString(", ")}) ${defs} in ${bod}"
    case Region(name, body) => s"region ${name.nme} in ${body.showDbg}"
    case RegRef(reg, value) => s"(${reg.showDbg}).ref ${value.showDbg}"
    case Assgn(lhs, rhs) => s"${lhs.showDbg} := ${rhs.showDbg}"
    case SetRef(lhs, rhs) => s"${lhs.showDbg} := ${rhs.showDbg}"
    case Drop(term) => s"drop $term"
    case Deref(term) => s"!$term"
    case Neg(ty) => s"~${ty.showDbg}"
    case CompType(lhs, rhs, pol) => s"${lhs.showDbg} ${if pol then "|" else "&"} ${rhs.showDbg}"
    case Error() => "<error>"
    case Tup(fields) => fields.map(_.showDbg).mkString("[", ", ", "]")
    case Mut(und) => s"mut ${und.showDbg}"
    case CtxTup(fields) => fields.map(_.showDbg).mkString("‹using›[", ", ", "]")
    case TermDefinition(k, sym, tsym, pss, tps, sign, body, flags, _, _, _) =>
      s"${flags.showDbg}${k.str} ${sym}${
        tps.map(_.map(_.showDbg)).mkStringOr(", ", "[", "]")
      }${
        pss.map(_.showDbg).mkString("")
      }${sign.fold("")(": "+_.showDbg)}${
        body match
          case S(x) => " = " + x.showDbg
          case N => ""
        }"
    case cls: ClassLikeDef =>
      s"${cls.kind} ${cls.sym.nme}${
        cls.tparams.map(_.showDbg).mkStringOr(", ", "[", "]")}${
        cls.paramsOpt.fold("")(_.toString)} ${cls.body}"
    case Import(sym, str, file) => s"import $str from ${file}"
    case Annotated(ann, target) => s"@${ann} ${target.showDbg}"
    case Throw(res) => s"throw ${res.showDbg}"
    case Label(label, _, body, _) => s"do ${label.nme}: ${body.showDbg}"
    case Break(label, _, value) => s"${label.nme}.break${value.fold("")(v => s" ${v.showDbg}")}"
    case Continue(label) => s"${label.nme}.continue"
    case Try(body, finallyDo) => s"try ${body.showDbg} finally ${finallyDo.showDbg}"
    case Ret(res) => s"return ${res.showDbg}"
    case TypeDef(sym, _, tparams, rhs, _, _) =>
      s"type ${sym}${tparams.mkStringOr(", ", "[", "]")} = ${rhs.fold("")(x => x.showDbg)}"
    case Missing => "missing"
    case LeadingDotSel(nme) => s"_?_.${nme.name}"
    case SetConfig(_) => "#config(...)"

final case class LetDecl(sym: LocalVarSymbol | TermSymbol, annotations: Ls[Annot]) extends Statement

final case class RcdField(field: Term, rhs: Term) extends Statement
final case class RcdSpread(rcd: Term) extends Statement

final case class DefineVar(sym: LocalSymbol | TermSymbol, rhs: Term) extends Statement

/** A global configuration change directive (`#config(...)`).
  * Records a function that modifies the current compiler configuration. */
final case class SetConfig(modify: hkmc2.Config => hkmc2.Config) extends Statement

enum Visibility:
  case Public, Private

/**
 * isMethod: if the term is a method (as opposed to a function)
 */
final case class TermDefFlags(isMethod: Bool):
  def showDbg: Str = 
    val flags = Buffer.empty[String]
    if isMethod then flags += "method "
    flags.mkString
  override def toString: String = "‹" + showDbg + "›"

object TermDefFlags { val empty: TermDefFlags = TermDefFlags(false) }

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
) extends CompanionValue:
  require(k is tsym.k)
  def bsym: BlockMemberSymbol = sym
  val owner = tsym.owner
  def visibility: Visibility = annotations
    .collectFirst:
      case Annot.Modifier(Keyword.`private`) => Visibility.Private
      case Annot.Modifier(Keyword.`public`) => Visibility.Public
    .getOrElse(Visibility.Public)
  lazy val mayRaiseEffects: Bool =
    annotations.forall:
      case Annot.MayNotRaiseEffects => false
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
    
    if errs.nonEmpty then
      L(errs.map(ErrorReport(_)).toList)
    else
      R(mems.toMap)

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
case class Import(sym: ImportSymbol, str: Str, file: io.Path) extends Statement


sealed abstract class Declaration:
  val sym: Symbol
  
  /** Whether this declares a class, a pattern, an object, or a pattern
    * parameter. Only these can be in patterns constructor position. */
  def isPatternConstructor: Bool = this match
    case _: (TermDefinition | TypeDef | TyParam) => false
    case d: ModuleOrObjectDef => d.kind isnt Mod
    case _: (PatternDef | ClassDef) => true
    case p: Param => p.flags.pat

sealed abstract class Definition extends Declaration, Statement:
  val annotations: Ls[Annot]
  def bsym: BlockMemberSymbol
  def hasDeclareModifier: Opt[Annot.Modifier] = annotations.collectFirst:
    case mod @ Annot.Modifier(Keyword.`declare`) => mod
  def hasStagedModifier: Opt[Annot.Modifier] = annotations.collectFirst:
    case mod @ Annot.Modifier(Keyword.`staged`) => mod

sealed trait CompanionValue extends Definition

type CompanionSymbol = ModuleOrObjectSymbol | TypeAliasSymbol | ClassSymbol
type ClassCompanionSymbol = ModuleOrObjectSymbol | TypeAliasSymbol
type ModuleCompanionSymbol = TypeAliasSymbol | ClassSymbol


sealed abstract class TypeLikeDef extends Definition:
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
    case Annot.Trm(trm: SynthSel) if
      (kind is Cls) &&
        (trm.sym.contains(ctx.builtins.annotations.bufferable) ||
        trm.sym.contains(ctx.builtins.annotations.buffered)) => false
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
  val path: SrcScope
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
) extends ClassLikeDef:
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
  def isData: Opt[Annot.Modifier] = annotations.collectFirst:
    case mod @ Annot.Modifier(Keyword.`data`) => mod
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
  ): ClassDef =
    params match
      case ps :: pss => Parameterized(owner, kind, sym.asInstanceOf// TODO: improve
        , bsym, S(ctorSym.getOrElse(lastWords("Parameterized classes should have a ctor symbol.")))
        , tparams, ps, pss ::: auxCtorParams, ext, body, comp, annotations)
      case Nil => Plain(owner, kind, sym.asInstanceOf// TODO: improve
        , bsym
        , tparams, ext, body, comp, annotations, auxParams = auxCtorParams, ctorSym = ctorSym)
  
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
  ) extends ClassDef:
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
  ) extends ClassDef:
    val paramsOpt: Opt[ParamList] = N
  
end ClassDef


case class TypeDef(
  sym: TypeAliasSymbol,
  bsym: BlockMemberSymbol,
  tparams: Ls[TyParam],
  rhs: Opt[Term],
  companion: Opt[CompanionValue],
  annotations: Ls[Annot],
) extends TypeLikeDef


// TODO Store optional source locations for the flags instead of booleans
final case class FldFlags(mut: Bool, spec: Bool, pat: Bool, isVal: Bool):
  def show: Str = 
    val flags = Buffer.empty[String]
    if mut then flags += "mut"
    if spec then flags += "spec"
    if pat then flags += "pattern"
    if isVal then flags += "val"
    flags.mkString(" ")
  override def toString: String = "‹" + show + "›"

object FldFlags:
  val empty: FldFlags = FldFlags(false, false, false, false)
  object benign:
    // * Some flags like `mut` and `module` are "benign" in the sense that they don't affect code-gen
    def unapply(flags: FldFlags): Bool =
      !flags.spec


enum IfLikeForm:
  case ReturningIf, ImperativeIf, While
  def isImperative: Bool = this match
    case ReturningIf => false
    case ImperativeIf | While => true


sealed abstract class Elem:
  def subTerms: Ls[Term] = this match
    case Fld(_, term, asc) => term :: asc.toList
    case Spd(_, term) => term :: Nil
  def show(using Scope, ShowCfg, Raise): Document
  def showDbg(using DebugPrinter): Str
object Elem:
  given Conversion[Term, Elem] = PlainFld(_)
final case class Fld(flags: FldFlags, term: Term, asc: Opt[Term]) extends Elem, FldImpl
object PlainFld:
  def apply(term: Term) = Fld(FldFlags.empty, term, N)
  def unapply(fld: Fld): Opt[Term] = S(fld.term)
final case class Spd(k: SpreadKind, term: Term) extends Elem:
  def show(using Scope, ShowCfg, Raise): Document = k.str :: term.show
  def showDbg(using DebugPrinter): Str = k.str + term.showDbg

final case class TyParam(flags: FldFlags, vce: Opt[Bool], sym: VarSymbol) extends Declaration:
  
  // * For variance analysis
  var isCovariant: Bool = true
  var isContravariant: Bool = true
  
  def showDbg: Str =
    // (if isContravariant then "in " else "") +
    // (if isCovariant then "out " else "") +
    (if isCovariant then
      if isContravariant then "" else "out "
      else if isContravariant then "in " else "in out ") +
    flags.show + sym


object Param:
  def simple(sym: VarSymbol) = Param(FldFlags.empty, sym, N, Modulefulness.none)

final case class Param(flags: FldFlags, sym: VarSymbol, sign: Opt[Term], modulefulness: Modulefulness)
extends Declaration, AutoLocated:
  var fldSym: Opt[MemberSymbol] = N
  
  val flow: FlowSymbol = sym

  // * This field is filled in during flow analysis;
  // * it is not meant to be maintained afterwards (so it does not need to be copied around).
  var signType: Opt[Type] = N
  
  def withSignTypeOf(p: Param): this.type =
    signType = p.signType
    this
  
  def subTerms: Ls[Term] = sign.toList
  
  override protected def children: Vector[Located] = sym +: sign.toVector
  
  def show(using Scope, ShowCfg, Raise): Document =
    doc"${flags.show}${sym.showName}${sign.fold(doc"")(": " :: _.show)}"
  
  def showDbg(using DebugPrinter): Str = flags.show + sym + sign.fold("")(": " + _.showDbg)

final case class ParamList(flags: ParamListFlags, params: Ls[Param], restParam: Opt[Param])
extends AutoLocated:
  override protected def children: Vector[Located] = params.toVector ++ restParam
  def foreach(f: Param => Unit): Unit = (params.iterator ++ restParam).foreach(f)
  def paramCountLB: Int = params.length
  def paramCountUB: Bool = restParam.isEmpty
  lazy val paramSyms = params.map(_.sym) ++ restParam.map(_.sym)
  lazy val allParams = params ++ restParam.toList
  def subTerms: Ls[Term] = params.flatMap(_.subTerms) ++ restParam.toList.flatMap(_.subTerms)
  def show(using Scope, ShowCfg, Raise): Document =
    flags.show
    :: doc"(" :: (
      params.map(_.show)
      :::
      restParam.map(p => doc"...${p.show}").toList
    ).mkDocument(", ")
    :: doc")"
  def showDbg(using DebugPrinter): Str = flags.showDbg
    + (params.map(_.showDbg) ++ restParam.toList.map("..." + _.showDbg)).mkString("(", ", ", ")")
object PlainParamList:
  def apply(params: Ls[Param]) =
    ParamList(ParamListFlags.empty, params, N)
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


trait FldImpl extends AutoLocated:
  self: Fld =>
  def children: Vector[Located] = self.term +: self.asc.toVector
  def show(using Scope, ShowCfg, Raise): Document = flags.show :: self.term.show
  def showDbg(using DebugPrinter): Str = flags.show + self.term.showDbg
  def describe: Str =
    (if self.flags.spec then "specialized " else "") +
    (if self.flags.mut then "mutable " else "") +
    self.term.describe

/**
 * Unwrapper that unwraps a term until it is no longer an App.
 */
object Apps:
  def unapply(t: Term): S[(Term, Ls[Term])] = t match
    case Term.App(Apps(base, args), arg) => S(base, args :+ arg)
    case t => S(t, Nil)


trait BlkImpl:
  this: Blk =>
  def mkBlkClone(using State): Blk = Blk(stats.map(_.mkClone), res.mkClone)
  def showTopLevel(using Scope, ShowCfg, Raise): Document =
    (stats ::: (res match
      case Lit(Tree.UnitLit(false)) => Nil
      case res => res :: Nil)).map(_.show).mkDocument(doc", # ")


