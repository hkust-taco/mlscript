package hkmc2
package semantics

import scala.collection.mutable.Buffer

import mlscript.utils.*, shorthands.*
import syntax.*

import Elaborator.State
import hkmc2.typing.Type
import hkmc2.semantics.Elaborator.{Ctx, ctx}


final case class QuantVar(sym: VarSymbol, ub: Opt[Term], lb: Opt[Term])

enum Annot extends AutoLocated:
  case Untyped
  case Modifier(mod: Keyword)
  case Trm(trm: Term)
  
  def symbol: Opt[Symbol] = this match
    case Trm(trm) => trm.symbol
    case _ => N
  
  def subTerms: Ls[Term] = this match
    case Trm(trm) => trm :: Nil
    case _: Modifier | Untyped => Nil
  
  def children: Ls[Located] = this match
    case Trm(trm) => trm :: Nil
    case _: Modifier | Untyped => Nil
  
  def mkClone(using State): Annot = this match
    case Untyped => Untyped
    case Modifier(mod) => Modifier(mod)
    case Trm(trm) => Trm(trm.mkClone)

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

  def duplicate: this.type =
    this.match
      case t: Term.Ref => t.copy()(t.tree, t.refNum, t.typ)
      case t: Term.App => t.copy()(t.tree, t.typ, t.resSym)
      case t: Term.TyApp => t.copy()(t.typ)
      case t: Term.Sel => t.copy()(t.sym, t.typ)
      case t: Term.SynthSel => t.copy()(t.sym, t.typ)
    .withLocOf(this)
    .asInstanceOf
  
  def withSym(sym: FieldSymbol): this.type = 
    this.match
      case t: Term.Sel => t.copy()(S(sym), t.typ)
      case t: Term.SynthSel => t.copy()(S(sym), t.typ)
      case _ => lastWords(s"Cannot attach a symbol to a non-selection term: ${this.show}")
    .withLocOf(this)
    .asInstanceOf
  
  def withTyp(typ: Type): this.type = 
    this.match
      case t: Term.Ref => t.copy()(t.tree, t.refNum, S(typ))
      case t: Term.App => t.copy()(t.tree, S(typ), t.resSym)
      case t: Term.TyApp => t.copy()(S(typ))
      case t: Term.Sel => t.copy()(t.sym, S(typ))
      case t: Term.SynthSel => t.copy()(t.sym, S(typ))
    .withLocOf(this)
    .asInstanceOf
  
  override def show: Str = expansion match
    case S(S(expansion)) => showDbg + "{~>" + expansion.show + "}"
    case _ => showDbg
  
  def expandedIn[T](in: Term => T): T =
    in(expanded)
  
  def expandedResolvableIn[T](in: Resolvable => T): T =
    expanded match
      case r: Resolvable => in(r)
      case t => lastWords(s"Expected a resolvable term, but got ${t.show}.")

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
      lastWords(s"Cannot expand the term ${this.show} multiple times (to different expansions ${expansion.get.show}).")
    
    this.expansion = S(expansion)
    this
    
  def resolve: this.type = expand(N)
  def dontResolve: this.type = this // TODO rm
  
  def hasExpansion = expansion.isDefined
  
  def defn: Opt[Definition] = resolvedSym match
    case S(sym: MemberSymbol[?]) => sym.defn
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

enum Term extends Statement:
  case Error
  case UnitVal()
  case Missing // Placeholder terms that were not elaborated due to the "lightweight" elaboration mode `Mode.Light`
  case Lit(lit: Literal)
  case Ref(sym: Symbol)
    (val tree: Tree.Ident, val refNum: Int, val typ: Opt[Type]) extends Term, ResolvableImpl
  case App(lhs: Term, rhs: Term)
    (val tree: Tree.App, val typ: Opt[Type], val resSym: FlowSymbol) extends Term, ResolvableImpl
  case TyApp(lhs: Term, targs: Ls[Term])
    (val typ: Opt[Type]) extends Term, ResolvableImpl
  case Sel(prefix: Term, nme: Tree.Ident)
    (val sym: Opt[FieldSymbol], val typ: Opt[Type]) extends Term, ResolvableImpl
  case SynthSel(prefix: Term, nme: Tree.Ident)
    (val sym: Opt[FieldSymbol], val typ: Opt[Type]) extends Term, ResolvableImpl
  case DynSel(prefix: Term, fld: Term, arrayIdx: Bool)
  case Tup(fields: Ls[Elem])(val tree: Tree.Tup)
  case Mut(underlying: Tup | Rcd | New | DynNew)
  case CtxTup(fields: Ls[Elem])(val tree: Tree.Tup)
  case IfLike(kw: Keyword.`if`.type | Keyword.`while`.type, split: SimpleSplit)
  /** `If` expressions synthesized by the pattern compiler. It should only be
   *  created and used in `Lowering`. One must make sure that all terms in the
   *  split are correctly resolved. In the future, we might look for a way to
   *  remove `SynthIf` by generating IR `Match` blocks directly. */
  case SynthIf(split: Split)
  case Lam(params: ParamList, body: Term)
  case FunTy(lhs: Term, rhs: Term, eff: Opt[Term])
  case Forall(tvs: Ls[QuantVar], outer: Opt[VarSymbol], body: Term)
  case WildcardTy(in: Opt[Term], out: Opt[Term])
  case Blk(stats: Ls[Statement], res: Term) extends Term, BlkImpl
  case Rcd(mut: Bool, stats: Ls[Statement])
  case Quoted(body: Term)
  case Unquoted(body: Term)
  case New(cls: Term, args: Ls[Term], rft: Opt[ClassSymbol -> ObjBody])
  case DynNew(cls: Term, args: Ls[Term])
  case SelProj(prefix: Term, cls: Term, proj: Tree.Ident)(val sym: Opt[FieldSymbol])
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
  case Try(body: Term, finallyDo: Term)
  case Annotated(annot: Annot, target: Term)
  case Handle(lhs: LocalSymbol, rhs: Term, args: List[Term],
    derivedClsSym: ClassSymbol, defs: Ls[HandlerTermDefinition], body: Term)
  
  def expanded: Term = this match
    case t: Resolvable => t.expansion match
      case S(S(t)) => t.expanded
      case S(N) => this
      case N => this
    case _ => this
  
  /**
   * The prelinminary symbol for the term that is resolved during
   * elaboration. 
   */
  lazy val symbol: Opt[Symbol] = this match
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
    case ref: Ref => ref.symbol
    case sel: Sel => sel.sym
    case sel: SynthSel => sel.sym
    case sel: SelProj => sel.sym
    case app: TyApp => app.lhs.resolvedSym
    case _ => N
  
  def resolvedTyp: Opt[Type] = expanded match
    case ref: Ref => ref.typ
    case app: App => app.typ
    case app: TyApp => app.typ
    case sel: Sel => sel.typ
    case sel: SynthSel => sel.typ
    case _ => N
  
  def sel(id: Tree.Ident, sym: Opt[FieldSymbol]): Sel =
    Sel(this, id)(sym, N)
  def selNoSym(nme: Str, synth: Bool = false): Sel | SynthSel =
    val id = new Tree.Ident(nme)
    if synth
    then SynthSel(this, id)(N, N)
    else sel(id, N)
  
  def app(args: Term*)(using State) =
    App(this, Tup(args.toList.map(PlainFld(_)))(Tree.DummyTup))
      (Tree.App(Tree.Dummy, Tree.Dummy), N, FlowSymbol(""))
  
  override def mkClone(using State): Term = this match
    case Error => Error
    case UnitVal() => UnitVal()
    case Missing => Missing
    case Lit(Tree.StrLit(value)) => Lit(Tree.StrLit(value))
    case Lit(Tree.IntLit(value)) => Lit(Tree.IntLit(value))
    case Lit(Tree.DecLit(value)) => Lit(Tree.DecLit(value))
    case Lit(Tree.BoolLit(value)) => Lit(Tree.BoolLit(value))
    case Lit(Tree.UnitLit(value)) => Lit(Tree.UnitLit(value))
    case term @ Ref(sym) => Ref(sym)(Tree.Ident(term.tree.name), term.refNum, term.typ)
    case term @ Sel(prefix, nme) => Sel(prefix.mkClone, Tree.Ident(nme.name))(term.sym, term.typ)
    case term @ App(lhs, rhs) => App(lhs.mkClone, rhs.mkClone)(term.tree, term.typ, term.resSym)
    case term @ TyApp(lhs, targs) => TyApp(lhs.mkClone, targs.map(_.mkClone))(term.typ)
    case term @ SynthSel(prefix, nme) => SynthSel(prefix.mkClone, Tree.Ident(nme.name))(term.sym, term.typ)
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
    case IfLike(kw, split) => IfLike(kw, split)
    case SynthIf(split) => SynthIf(split.mkClone)
    case Lam(params, body) => Lam(params, body.mkClone)
    case FunTy(lhs, rhs, eff) => FunTy(lhs.mkClone, rhs.mkClone, eff.map(_.mkClone))
    case Forall(tvs, outer, body) => Forall(tvs, outer, body.mkClone)
    case WildcardTy(in, out) => WildcardTy(in.map(_.mkClone), out.map(_.mkClone))
    case blk: Blk => blk.mkBlkClone
    case Rcd(mut, stats) => Rcd(mut, stats.map(_.mkClone))
    case Quoted(body) => Quoted(body.mkClone)
    case Unquoted(body) => Unquoted(body.mkClone)
    case New(cls, args, rft) =>
      New(cls.mkClone, args.map(_.mkClone), rft.map { case (cs, ob) => cs -> ObjBody(ob.blk.mkBlkClone) })
    case DynNew(cls, args) => DynNew(cls.mkClone, args.map(_.mkClone))
    case term @ SelProj(prefix, cls, proj) =>
      SelProj(prefix.mkClone, cls.mkClone, Tree.Ident(proj.name))(term.sym)
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
    case Try(body, finallyDo) => Try(body.mkClone, finallyDo.mkClone)
    case Annotated(annot, target) => Annotated(annot, target.mkClone)
    case Handle(lhs, rhs, args, derivedClsSym, defs, body) =>
      Handle(lhs, rhs.mkClone, args.map(_.mkClone), derivedClsSym, defs, body.mkClone)
  
  
end Term

import Term.*


extension (self: Blk)
  def mapRes(f: Term => Term) =
    Blk(self.stats, f(self.res))


sealed trait Statement extends AutoLocated, ProductWithExtraInfo:
  
  def mkClone(using State): Statement = this match
    case t: Term => lastWords(s"overridden implementation")
    case d: Definition => ???
    case imp: Import => Import(imp.sym, imp.str, imp.file)
    case LetDecl(sym, annotations) => LetDecl(sym, annotations.map(_.mkClone))
    case RcdField(field, rhs) => RcdField(field.mkClone, rhs.mkClone)
    case RcdSpread(rcd) => RcdSpread(rcd.mkClone)
    case DefineVar(sym, rhs) => DefineVar(sym, rhs.mkClone)
  
  def describe: Str =
    val desc = this match
      case Error => "‹error›"
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
      case IfLike(Keyword.`if`, body) => "`if` expression"
      case IfLike(Keyword.`while`, body) => "`while` expression"
      case SynthIf(split) => "synthetic `if` expression"
      case Lam(params, body) => "function literal"
      case FunTy(lhs, rhs, eff) => "function type"
      case Forall(tvs, outer, body) => "universal quantification"
      case WildcardTy(in, out) => "wildcard type"
      case Blk(stats, res) => "block"
      case Quoted(term) => "quoted term"
      case Unquoted(term) => "unquoted term"
      case New(cls, args, rft) => "object creation"
      case SelProj(pre, cls, proj) => "field selection"
      case Asc(term, ty) => "type ascription"
      case CompType(lhs, rhs, pol) => "composed type"
      case Neg(rhs) => "negation type"
      case Region(name, body) => "region expression"
      case RegRef(reg, value) => "reference creation"
      case Assgn(lhs, rhs) => "assignment"
      case SetRef(ref, value) => "mutable reference assignment"
      case Drop(ref) => "drop"
      case Deref(ref) => "dereference"
      case Throw(e) => "throw"
      case Annotated(annotation, target) => "annotation"
      case Ret(res) => "return"
      case Try(body, finallyDo) => "try expression"
      case s => TODO(s)
    this match
      case self: Resolvable => self.resolvedTyp match
        case S(typ) => s"${desc} of type ${typ.show}"
        case N => desc
      case _ => desc
  
  def extraInfo: Str = this match
    case r: Resolvable if r.resolvedSym.isDefined || r.resolvedTyp.isDefined => (
        r.resolvedSym.map(s => s"sym=${s}") ::
        r.resolvedTyp.map(s => s"typ=${s.showDbg}") :: Nil
      ).flatten.mkString(",")
    case r: SelProj => r.symbol.mkString
    case _ => ""
  
  def subStatements: Ls[Statement] = this match
    case Blk(stats, res) => stats ::: res :: Nil
    case _ => subTerms
  def subTerms: Ls[Term] = this match
    case Error | Missing | _: Lit | _: Ref | _: UnitVal => Nil
    case App(lhs, rhs) => lhs :: rhs :: Nil
    case RcdField(lhs, rhs) => lhs :: rhs :: Nil
    case RcdSpread(bod) => bod :: Nil
    case FunTy(lhs, rhs, eff) => lhs :: rhs :: eff.toList
    case TyApp(pre, tarsg) => pre :: tarsg
    case Sel(pre, _) => pre :: Nil
    case SynthSel(pre, _) => pre :: Nil
    case DynSel(o, f, _) => o :: f :: Nil
    case Tup(fields) => fields.flatMap(_.subTerms)
    case Mut(und) => und :: Nil
    case CtxTup(fields) => fields.flatMap(_.subTerms)
    case IfLike(_, split) => split.subTerms
    case SynthIf(split) => split.subTerms
    case Lam(params, body) => body :: Nil
    case Blk(stats, res) => stats.flatMap(_.subTerms) ::: res :: Nil
    case Rcd(mut, stats) => stats.flatMap(_.subTerms)
    case Quoted(term) => term :: Nil
    case Unquoted(term) => term :: Nil
    case New(cls, args, rft) => cls :: args ::: rft.toList.flatMap(_._2.blk.subTerms)
    case DynNew(cls, args) => cls :: args
    case SelProj(pre, cls, _) => pre :: cls :: Nil
    case Asc(term, ty) => term :: ty :: Nil
    case Ret(res) => res :: Nil
    case Throw(res) => res :: Nil
    case Forall(_, _, body) => body :: Nil
    case WildcardTy(in, out) => in.toList ++ out.toList
    case CompType(lhs, rhs, _) => lhs :: rhs :: Nil
    case LetDecl(sym, annotations) => annotations.flatMap(_.subTerms)
    case DefineVar(sym, rhs) => rhs :: Nil
    case Region(_, body) => body :: Nil
    case RegRef(reg, value) => reg :: value :: Nil
    case Assgn(lhs, rhs) => lhs :: rhs :: Nil
    case SetRef(lhs, rhs) => lhs :: rhs :: Nil
    case Drop(term) => term :: Nil
    case Deref(term) => term :: Nil
    case TermDefinition(_, _, _, pss, tps, sign, body, res, _, _, annotations, _) =>
      pss.toList.flatMap(_.subTerms) ::: tps.getOrElse(Nil).flatMap(_.subTerms) ::: sign.toList ::: body.toList ::: annotations.flatMap(_.subTerms)
    case cls: ClassDef =>
      cls.paramsOpt.toList.flatMap(_.subTerms) ::: cls.body.blk :: cls.annotations.flatMap(_.subTerms)
    case mod: ModuleOrObjectDef =>
      mod.paramsOpt.toList.flatMap(_.subTerms) ::: mod.body.blk :: mod.annotations.flatMap(_.subTerms)
    case td: TypeDef =>
      td.rhs.toList ::: td.annotations.flatMap(_.subTerms)
    case pat: PatternDef =>
      pat.paramsOpt.toList.flatMap(_.subTerms) ::: pat.body.blk :: pat.annotations.flatMap(_.subTerms)
    case Import(sym, str, pth) => Nil
    case Try(body, finallyDo) => body :: finallyDo :: Nil
    case Handle(lhs, rhs, args, derivedClsSym, defs, bod) => rhs :: args ::: defs.flatMap(_.td.subTerms) ::: bod :: Nil
    case Neg(e) => e :: Nil
    case Annotated(ann, target) => ann.subTerms ::: target :: Nil
  
  // private def treeOrSubterms(t: Tree, t: Term): Ls[Located] = t match
  private def treeOrSubterms(t: Tree): Ls[Located] = t match
    case Tree.DummyApp | Tree.DummyTup => subTerms
    case _ => t :: Nil
  
  protected def children: Ls[Located] = this match
    case t: Lit => t.lit.asTree :: Nil
    case t: Ref => treeOrSubterms(t.tree)
    case t: Tup => treeOrSubterms(t.tree)
    case l: Lam => l.params.paramSyms.map(_.id) ::: l.body :: Nil
    case t: App => treeOrSubterms(t.tree)
    case IfLike(_, split) => split :: Nil
    case SynthIf(split) => split :: Nil
    case SynthSel(pre, nme) => pre :: nme :: Nil
    case Sel(pre, nme) => pre :: nme :: Nil
    case SelProj(prefix, cls, proj) => prefix :: cls :: proj :: Nil
    case _ =>
      subTerms // TODO more precise (include located things that aren't terms)
  
  def show: Str = showDbg // TODO use Document
  
  def showDbg: Str = this match
    case r: Ref =>
      showPlain
    case trm: Term =>
      // s"$showPlain‹${trm.symbol.getOrElse("")}›"
      s"$showPlain${trm.symbol.fold("")("‹"+_+"›")}"
    case _ =>
      showPlain
  
  def showAsParams: Str = this match
    case tup: Tup => s"(${tup.fields.map(_.showDbg).mkString(", ")})"
    case _ => s"(...$showDbg)"
  
  def showPlain: Str = this match
    case Term.UnitVal() => "()"
    case Lit(lit) => lit.idStr
    case r @ Ref(symbol) => symbol.toString + symbol.getState.dbgRefNum(r.refNum)
    case App(lhs, rhs) => s"${lhs.showDbg}${rhs.showAsParams}"
    case RcdField(lhs, rhs) => s"${lhs.showDbg}: ${rhs.showDbg}"
    case RcdSpread(bod) => s"...${bod.showDbg}"
    case FunTy(lhs: Tup, rhs, eff) =>
      s"${lhs.fields.map(_.showDbg).mkString(", ")} ->${
        eff.map(e => s"{${e.showDbg}}").getOrElse("")} ${rhs.showDbg}"
    case FunTy(lhs, rhs, eff) =>
      s"(...${lhs.showDbg}) ->${eff.map(e => s"{${e.showDbg}}").getOrElse("")} ${rhs.showDbg}"
    case TyApp(lhs, targs) => s"${lhs.showDbg}[${targs.mkString(", ")}]"
    case Forall(tvs, outer, body) => s"forall ${tvs.mkString(", ")}${outer.map(v => s", outer $v").mkString}: ${body.toString}"
    case WildcardTy(in, out) => s"in ${in.map(_.toString).getOrElse("⊥")} out ${out.map(_.toString).getOrElse("⊤")}"
    case Sel(pre, nme) => s"${pre.showDbg}.${nme.name}"
    case SynthSel(pre, nme) => s"(${pre.showDbg}.)${nme.name}"
    case DynSel(pre, fld, _) => s"${pre.showDbg}[${fld.showDbg}]"
    case IfLike(kw, split) => s"${kw.name} { ${split.showDbg} }"
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
      s"new ${cls.showDbg}${args.map(_.showAsParams).mkString}${rft.fold("")(r => s"{ ${r._2.blk.showDbg} }")}"
    case DynNew(cls, args) =>
      s"new! ${cls.showDbg}${args.map(_.showAsParams).mkString}"
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
    case Error => "<error>"
    case Tup(fields) => fields.map(_.showDbg).mkString("[", ", ", "]")
    case Mut(und) => s"mut ${und.showDbg}"
    case CtxTup(fields) => fields.map(_.showDbg).mkString("‹using›[", ", ", "]")
    case TermDefinition(k, sym, tsym, pss, tps, sign, body, res, flags, _, _, _) =>
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
    case Try(body, finallyDo) => s"try ${body.showDbg} finally ${finallyDo.showDbg}"
    case Ret(res) => s"return ${res.showDbg}"
    case TypeDef(sym, _, tparams, rhs, _, _) =>
      s"type ${sym}${tparams.mkStringOr(", ", "[", "]")} = ${rhs.fold("")(x => x.showDbg)}"
    case Missing => "missing"

final case class LetDecl(sym: LocalSymbol, annotations: Ls[Annot]) extends Statement

final case class RcdField(field: Term, rhs: Term) extends Statement
final case class RcdSpread(rcd: Term) extends Statement

final case class DefineVar(sym: LocalSymbol, rhs: Term) extends Statement

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
    resSym: FlowSymbol,
    flags: TermDefFlags,
    modulefulness: Modulefulness,
    annotations: Ls[Annot],
    companion: Opt[CompanionSymbol],
) extends CompanionValue:
  require(k is tsym.k)
  val owner = tsym.owner
  def extraAnnotations: Ls[Annot] = annotations.filter:
    case Annot.Modifier(Keyword.`declare` | Keyword.`abstract`) => false
    case _ => true

final case class HandlerTermDefinition(
  resumeSym: VarSymbol,
  td: TermDefinition
)

case class ObjBody(blk: Term.Blk):
  
  lazy val members: Map[Str, FieldSymbol] = blk.stats.collect:
    case td: TermDefinition => td.sym.nme -> td.sym
    case td: ClassLikeDef => td.sym.nme -> td.sym
    case td: TypeDef => td.sym.nme -> td.sym
  .toMap
  
  lazy val (methods, nonMethods) = blk.stats.partitionMap:
    case td: TermDefinition if td.k is syntax.Fun => L(td)
    case s => R(s)
  lazy val publicFlds: Ls[TermDefinition] = nonMethods.collect:
    case td: TermDefinition if td.k.isInstanceOf[syntax.Val] => td
  
  // override def toString: String = statmts.mkString("{ ", "; ", " }")
  override def toString: String = blk.showDbg


/** Note that the `file` Path may not represent a real file; eg when importing "fs". */
case class Import(sym: Symbol, str: Str, file: os.Path) extends Statement


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
  val sym: MemberSymbol[? <: ClassLikeDef] & InnerSymbol
  val bsym: BlockMemberSymbol
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
) extends ClassLikeDef, CompanionValue

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


sealed abstract class ClassDef extends ClassLikeDef:
  val kind: ClsLikeKind
  val sym: ClassSymbol
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
      tparams: Ls[TyParam],
      params: Ls[ParamList],
      ext: Opt[New],
      body: ObjBody,
      annotations: Ls[Annot],
      comp: Opt[ClassCompanionSymbol],
  ): ClassDef =
    params match
      case ps :: pss => Parameterized(owner, kind, sym.asInstanceOf// TODO: improve
        , bsym
        , tparams, ps, pss, ext, body, comp, annotations)
      case Nil => Plain(owner, kind, sym.asInstanceOf// TODO: improve
        , bsym
        , tparams, ext, body, comp, annotations)
  
  def unapply(cls: ClassDef): Opt[(ClassSymbol, Ls[TyParam], Opt[ParamList], ObjBody)] =
    S((cls.sym, cls.tparams, cls.paramsOpt, cls.body))
  
  case class Parameterized(
      owner: Opt[InnerSymbol],
      kind: ClsLikeKind,
      sym: ClassSymbol,
      bsym: BlockMemberSymbol,
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
      annotations: Ls[Annot]
  ) extends ClassDef:
    val paramsOpt: Opt[ParamList] = N
    val auxParams: List[ParamList] = Nil
  
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


sealed abstract class Elem:
  def subTerms: Ls[Term] = this match
    case Fld(_, term, asc) => term :: asc.toList
    case Spd(_, term) => term :: Nil
  def showDbg: Str
object Elem:
  given Conversion[Term, Elem] = PlainFld(_)
final case class Fld(flags: FldFlags, term: Term, asc: Opt[Term]) extends Elem, FldImpl
object PlainFld:
  def apply(term: Term) = Fld(FldFlags.empty, term, N)
  def unapply(fld: Fld): Opt[Term] = S(fld.term)
final case class Spd(eager: Bool, term: Term) extends Elem:
  def showDbg: Str = (if eager then "..." else "..") + term.showDbg

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
  var fldSym: Opt[FieldSymbol] = N
  def subTerms: Ls[Term] = sign.toList
  override protected def children: List[Located] = sym :: sign.toList
  def showDbg: Str = flags.show + sym + sign.fold("")(": " + _.showDbg)

final case class ParamList(flags: ParamListFlags, params: Ls[Param], restParam: Opt[Param])
extends AutoLocated:
  override protected def children: List[Located] = params ::: restParam.toList
  def foreach(f: Param => Unit): Unit =
    (params ++ restParam).foreach(f)
  def paramCountLB: Int = params.length
  def paramCountUB: Bool = restParam.isEmpty
  def paramSyms = params.map(_.sym) ++ restParam.map(_.sym)
  def allParams = params ++ restParam.toList
  def subTerms: Ls[Term] = params.flatMap(_.subTerms) ++ restParam.toList.flatMap(_.subTerms)
  def showDbg: Str = flags.showDbg
    + (params.map(_.showDbg) ++ restParam.toList.map("..." + _.showDbg)).mkString("(", ", ", ")")
object PlainParamList:
  def apply(params: Ls[Param]) =
    ParamList(ParamListFlags.empty, params, N)
  def unapply(pl: ParamList): Opt[Ls[Param]] = pl match
    case ParamList(ParamListFlags.empty, params, N) => S(params)
    case _ => N

final case class ParamListFlags(ctx: Bool):
  def showDbg: Str = (if ctx then "ctx " else "")
  override def toString: String = "‹" + showDbg + "›"

object ParamListFlags:
  val empty = ParamListFlags(false)


trait FldImpl extends AutoLocated:
  self: Fld =>
  def children: Ls[Located] = self.term :: self.asc.toList ::: Nil
  def showDbg: Str = flags.show + self.term.showDbg
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


