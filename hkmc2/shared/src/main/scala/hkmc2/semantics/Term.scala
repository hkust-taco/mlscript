package hkmc2
package semantics

import scala.collection.mutable.Buffer

import mlscript.utils.*, shorthands.*
import syntax.*

import Elaborator.State


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

type Resolvable = Term & ResolvableImpl

sealed trait ResolvableImpl:
  t: Term =>
  
  var iargsLs: Opt[Ls[Term.Tup]] = N
  
  override def show: Str = t.showDbg + iargsLs.map(_.map(_.showDbg))
  
  def withoutIArgs = t match
    case t: Term.Ref => t.copy()(t.tree, t.refNum, t.resSym).noIArgs
    case t: Term.App => t.copy()(t.tree, t.sym, t.resSym).noIArgs
    case t: Term.TyApp => t.copy()(t.sym).noIArgs
    case t: Term.Sel => t.copy()(t.sym).noIArgs
    case t: Term.SynthSel => t.copy()(t.sym).noIArgs
  
  def instantiate(using State): Term = iargsLs match
    case N => lastWords(s"missing implicit arguments for term ${t}")
    case S(iargsLs) => iargsLs.foldLeft(t.withoutIArgs): (t, args) => 
      Term.App(t, args)(Tree.DummyApp, N, FlowSymbol("implicit app")).noIArgs // N: todo
  
  def defn: Opt[Definition] = t.resolvedSymbol match
    case S(sym: MemberSymbol[?]) => sym.defn
    case S(sym: BlockLocalSymbol) => sym.decl match
      case S(td: Definition) => S(td)
      case _ => N
    case _ => N
  
  def termDefn: Opt[TermDefinition] = t.defn match
    case S(td: TermDefinition) => S(td)
    case _ => N
  
  def typeDefn: Opt[ClassLikeDef] = t.defn match
    case S(td: ClassLikeDef) => S(td)
    case _ => N
  
  def withIArgs(iargsLs: Ls[Term.Tup]): this.type = 
    if !(this.iargsLs.isEmpty || this.iargsLs.get == iargsLs) then
      lastWords:
        s"the implicit arguments for term ${t.showDbg} " +
        s"are already set to ${this.iargsLs.get}; " +
        s"they cannot be set to some different terms ${iargsLs}"
    this.iargsLs = S(iargsLs)
    this
  
  def noIArgs: Term = withIArgs(Nil)


enum Term extends Statement:
  case Error
  case UnitVal()
  case Missing // Placeholder terms that were not elaborated due to the "lightweight" elaboration mode `Mode.Light`
  case Lit(lit: Literal)
  case Builtin(id: Tree.Ident, nme: Str)
  case Ref(sym: Symbol)(val tree: Tree.Ident, val refNum: Int, var resSym: Opt[Symbol]) extends Term with ResolvableImpl
  case App(lhs: Term, rhs: Term)(val tree: Tree.App, var sym: Opt[FieldSymbol], val resSym: FlowSymbol) extends Term with ResolvableImpl
  case TyApp(lhs: Term, targs: Ls[Term])(var sym: Opt[Symbol]) extends Term with ResolvableImpl
  case Sel(prefix: Term, nme: Tree.Ident)(var sym: Opt[FieldSymbol]) extends Term with ResolvableImpl
  case SynthSel(prefix: Term, nme: Tree.Ident)(var sym: Opt[FieldSymbol]) extends Term with ResolvableImpl
  case DynSel(prefix: Term, fld: Term, arrayIdx: Bool)
  case Tup(fields: Ls[Elem])(val tree: Tree.Tup)
  case IfLike(kw: Keyword.`if`.type | Keyword.`while`.type, desugared: Split)
  case Lam(params: ParamList, body: Term)
  case FunTy(lhs: Term, rhs: Term, eff: Opt[Term])
  case Forall(tvs: Ls[QuantVar], outer: Opt[VarSymbol], body: Term)
  case WildcardTy(in: Opt[Term], out: Opt[Term])
  case Blk(stats: Ls[Statement], res: Term)
  case Rcd(stats: Ls[Statement])
  case Quoted(body: Term)
  case Unquoted(body: Term)
  case New(cls: Term, args: Ls[Term], rft: Opt[ClassSymbol -> ObjBody])
  case SelProj(prefix: Term, cls: Term, proj: Tree.Ident)(val sym: Opt[FieldSymbol])
  case Asc(term: Term, ty: Term)
  case CompType(lhs: Term, rhs: Term, pol: Bool)
  case Neg(rhs: Term)
  case Region(name: VarSymbol, body: Term)
  case RegRef(reg: Term, value: Term)
  case Assgn(lhs: Term, rhs: Term)
  case Deref(ref: Term)
  case SetRef(ref: Term, value: Term)
  case Ret(result: Term)
  case Throw(result: Term)
  case Try(body: Term, finallyDo: Term)
  case Annotated(annot: Annot, target: Term)
  case Handle(lhs: LocalSymbol, rhs: Term, args: List[Term],
    derivedClsSym: ClassSymbol, defs: Ls[HandlerTermDefinition], body: Term)
  
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
  def resolvedSymbol: Opt[Symbol] = this match
    case ref: Ref => ref.resSym
    case sel: Sel => sel.sym
    case sel: SynthSel => sel.sym
    case sel: SelProj => sel.sym
    case app: App => app.sym
    case tyApp: TyApp => tyApp.sym
    case _ => N
  
  def sel(id: Tree.Ident, sym: Opt[FieldSymbol]): Sel =
    Sel(this, id)(sym)
  def selNoSym(nme: Str, synth: Bool = false): Sel | SynthSel =
    val id = new Tree.Ident(nme)
    if synth
    then SynthSel(this, id)(N)
    else sel(id, N)
  
  def app(args: Term*)(using State) =
    App(this, Tup(args.toList.map(PlainFld(_)))(Tree.DummyTup))
      (Tree.App(Tree.Dummy, Tree.Dummy), N, FlowSymbol(""))
  
  def describe: Str = this match
    case Error => "<error>"
    case Lit(lit) => lit.describeLit
    case Ref(sym) => "reference"
    case App(lhs, rhs) => "application"
    case TyApp(lhs, targs) => "type application"
    case Sel(pre, nme) => "selection"
    case SynthSel(pre, nme) => "selection"
    case Tup(fields) => "tuple literal"
    case IfLike(Keyword.`if`, body) => "`if` expression"
    case IfLike(Keyword.`while`, body) => "`while` expression"
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
    case Deref(ref) => "dereference"
    case Throw(e) => "throw"
    case Annotated(annotation, target) => "annotation"
    case Ret(res) => "return"
end Term

import Term.*


extension (self: Blk)
  def mapRes(f: Term => Term) =
    Blk(self.stats, f(self.res))


sealed trait Statement extends AutoLocated with ProductWithExtraInfo:
  
  def extraInfo: Str = this match
    case ref: Ref if ref.resSym.isEmpty => ""
    case r: Resolvable => r.resolvedSymbol.mkString
    case r: SelProj => r.symbol.mkString
    case _ => ""
  
  def subStatements: Ls[Statement] = this match
    case Blk(stats, res) => stats ::: res :: Nil
    case _ => subTerms
  def subTerms: Ls[Term] = this match
    case Error | _: Lit | _: Ref | _: Builtin | _: UnitVal => Nil
    case App(lhs, rhs) => lhs :: rhs :: Nil
    case RcdField(lhs, rhs) => lhs :: rhs :: Nil
    case RcdSpread(bod) => bod :: Nil
    case FunTy(lhs, rhs, eff) => lhs :: rhs :: eff.toList
    case TyApp(pre, tarsg) => pre :: tarsg
    case Sel(pre, _) => pre :: Nil
    case SynthSel(pre, _) => pre :: Nil
    case DynSel(o, f, _) => o :: f :: Nil
    case Tup(fields) => fields.flatMap(_.subTerms)
    case IfLike(_, body) => body.subTerms
    case Lam(params, body) => body :: Nil
    case Blk(stats, res) => stats.flatMap(_.subTerms) ::: res :: Nil
    case Rcd(stats) => stats.flatMap(_.subTerms)
    case Quoted(term) => term :: Nil
    case Unquoted(term) => term :: Nil
    case New(cls, args, rft) => cls :: args ::: rft.toList.flatMap(_._2.blk.subTerms)
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
    case Deref(term) => term :: Nil
    case TermDefinition(_, k, _, pss, tps, sign, body, res, _, _, annotations) =>
      pss.toList.flatMap(_.subTerms) ::: tps.getOrElse(Nil).flatMap(_.subTerms) ::: sign.toList ::: body.toList ::: annotations.flatMap(_.subTerms)
    case cls: ClassDef =>
      cls.paramsOpt.toList.flatMap(_.subTerms) ::: cls.body.blk :: cls.annotations.flatMap(_.subTerms)
    case mod: ModuleDef =>
      mod.paramsOpt.toList.flatMap(_.subTerms) ::: mod.body.blk :: mod.annotations.flatMap(_.subTerms)
    case td: TypeDef =>
      td.rhs.toList ::: td.annotations.flatMap(_.subTerms)
    case pat: PatternDef =>
      pat.paramsOpt.toList.flatMap(_.subTerms) ::: pat.body.blk :: pat.annotations.flatMap(_.subTerms)
    case Import(sym, pth) => Nil
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
    case IfLike(kw, desug) => desug :: Nil
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
  def showPlain: Str = this match
    case Term.UnitVal() => "()"
    case Lit(lit) => lit.idStr
    case r @ Ref(symbol) => symbol.toString+"#"+r.refNum
    case App(lhs, tup: Tup) => s"${lhs.showDbg}(${tup.fields.map(_.showDbg).mkString(", ")})"
    case App(lhs, rhs) => s"${lhs.showDbg}(...${rhs.showDbg})"
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
    case IfLike(kw, body) => s"${kw.name} { ${body.showDbg} }"
    case Lam(params, body) => s"λ${params.showDbg}. ${body.showDbg}"
    case Blk(stats, res) =>
      (stats.map(_.showDbg + "; ") :+ (res match { case Lit(Tree.UnitLit(false)) => "" case x => x.showDbg + " " }))
      .mkString("( ", "", ")")
    case Rcd(stats) =>
      (stats.map(_.showDbg + "; "))
      .mkString("{ ", "", "}")
    case Quoted(term) => s"""code"${term.showDbg}""""
    case Unquoted(term) => s"$${${term.showDbg}}"
    case New(cls, args, rft) =>
      s"new ${cls.toString}(${args.mkString(", ")})${rft.fold("")(r => s"{ ${r._2.blk.showDbg} }")}"
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
    case Deref(term) => s"!$term"
    case Neg(ty) => s"~${ty.showDbg}"
    case CompType(lhs, rhs, pol) => s"${lhs.showDbg} ${if pol then "|" else "&"} ${rhs.showDbg}"
    case Error => "<error>"
    case Tup(fields) => fields.map(_.showDbg).mkString("[", ", ", "]")
    case TermDefinition(_, k, sym, pss, tps, sign, body, res, flags, _, _) => s"${flags} ${k.str} ${sym}${
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
    case Import(sym, file) => s"import ${sym} from ${file}"
    case Annotated(ann, target) => s"@${ann} ${target.showDbg}"
    case Throw(res) => s"throw ${res.showDbg}"
    case Try(body, finallyDo) => s"try ${body.showDbg} finally ${finallyDo.showDbg}"
    case Ret(res) => s"return ${res.showDbg}"
    case TypeDef(sym, tparams, rhs, _, _) =>
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
    if isMethod then flags += "method"
    flags.mkString(" ")
  override def toString: String = "‹" + showDbg + "›"

object TermDefFlags { val empty: TermDefFlags = TermDefFlags(false) }

/**
 * A case class representing the modulefulness of a declaration.
 *
 * @param msym if None, the declaration is non-moduful; if Some of
 * symbol, the declaration is moduleful and the symbol is the symbol of
 * the module's type
 */
final case class Modulefulness(msym: Opt[MemberSymbol[?]])(val modified: Bool):
  
  def isModuleful: Bool = msym.isDefined
  
  /**
   * Return Some of the module definition if it is moduleful; None
   * otherwise.
   */
  def mdef: Opt[ModuleDef] = msym match
    case S(msym) => msym.defn match
      case S(defn: ModuleDef) => S(defn)
      case _ => lastWords(s"no module definition for moduleful symbol $msym")
    case N => N

object Modulefulness:
  
  def ofSign(sign: Option[Term])(modified: Bool) = 
    sign.flatMap(_.symbol) match
      case S(sym: BlockMemberSymbol) if modified => sym.modTree.collect(_.symbol) match
        case S(value: MemberSymbol[?]) => 
          Modulefulness(S(value))(modified)
        case _ =>
          Modulefulness(S(sym))(modified)
      case _ =>
        Modulefulness(N)(modified)
  
  val none = Modulefulness(N)(false)

final case class TermDefinition(
    owner: Opt[InnerSymbol],
    k: TermDefKind,
    sym: BlockMemberSymbol,
    params: Ls[ParamList],
    tparams: Opt[Ls[Param]],
    sign: Opt[Term],
    body: Opt[Term],
    resSym: FlowSymbol,
    flags: TermDefFlags,
    modulefulness: Modulefulness,
    annotations: Ls[Annot],
) extends CompanionValue:
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
    case td @ TermDefinition(k = (_: syntax.Val)) => td
  
  // override def toString: String = statmts.mkString("{ ", "; ", " }")
  override def toString: String = blk.showDbg


case class Import(sym: Symbol, file: Str) extends Statement


sealed abstract class Declaration:
  val sym: Symbol

sealed abstract class Definition extends Declaration with Statement:
  val annotations: Ls[Annot]
  def isDeclare: Opt[Annot.Modifier] = annotations.collectFirst:
    case mod @ Annot.Modifier(Keyword.`declare`) => mod

sealed trait CompanionValue extends Definition


sealed abstract class TypeLikeDef extends Definition:
  val tparams: Ls[TyParam]
  val annotations: Ls[Annot]

sealed abstract class ClassLikeDef extends TypeLikeDef:
  val owner: Opt[InnerSymbol]
  val kind: ClsLikeKind
  val sym: MemberSymbol[? <: ClassLikeDef] & InnerSymbol
  val bsym: BlockMemberSymbol
  val tparams: Ls[TyParam]
  val paramsOpt: Opt[ParamList]
  val ext: Opt[New]
  val body: ObjBody
  val annotations: Ls[Annot]
  def extraAnnotations: Ls[Annot] = annotations.filter:
    case Annot.Modifier(Keyword.`declare` | Keyword.`abstract` | Keyword.`data`) => false
    case _ => true


case class ModuleDef(
  owner: Opt[InnerSymbol], 
  sym: ModuleSymbol, 
  bsym: BlockMemberSymbol,
  tparams: Ls[TyParam], 
  paramsOpt: Opt[ParamList], 
  ext: Opt[New],
  kind: ClsLikeKind,
  body: ObjBody,
  annotations: Ls[Annot],
) extends ClassLikeDef with CompanionValue

case class PatternDef(
    owner: Opt[InnerSymbol],
    sym: PatternSymbol,
    bsym: BlockMemberSymbol,
    tparams: Ls[TyParam],
    paramsOpt: Opt[ParamList],
    body: ObjBody,
    annotations: Ls[Annot],
) extends ClassLikeDef:
  self =>
  val kind: ClsLikeKind = Pat
  val ext: Opt[New] = N


sealed abstract class ClassDef extends ClassLikeDef:
  val kind: ClsLikeKind
  val sym: ClassSymbol
  val tparams: Ls[TyParam]
  val paramsOpt: Opt[ParamList]
  val body: ObjBody
  val companion: Opt[CompanionValue]
  val annotations: Ls[Annot]
  def isData: Opt[Annot.Modifier] = annotations.collectFirst:
    case mod @ Annot.Modifier(Keyword.`data`) => mod
  override def extraAnnotations: Ls[Annot] = super.extraAnnotations.filter:
    case Annot.Modifier(Keyword.`data`) => false
    case _ => true

object ClassDef:
  def apply(
      owner: Opt[InnerSymbol],
      kind: ClsLikeKind,
      sym: InnerSymbol,
      bsym: BlockMemberSymbol,
      tparams: Ls[TyParam],
      paramsOpt: Opt[ParamList],
      ext: Opt[New],
      body: ObjBody,
      annotations: Ls[Annot],
  ): ClassDef =
    paramsOpt match
      case S(params) => Parameterized(owner, kind, sym.asInstanceOf// TODO: improve
        , bsym
        , tparams, params, ext, body, N, annotations)
      case N => Plain(owner, kind, sym.asInstanceOf// TODO: improve
        , bsym
        , tparams, ext, body, N, annotations)
  
  def unapply(cls: ClassDef): Opt[(ClassSymbol, Ls[TyParam], Opt[ParamList], ObjBody)] =
    S((cls.sym, cls.tparams, cls.paramsOpt, cls.body))
  
  case class Parameterized(
      owner: Opt[InnerSymbol],
      kind: ClsLikeKind,
      sym: ClassSymbol,
      bsym: BlockMemberSymbol,
      tparams: Ls[TyParam],
      params: ParamList,
      ext: Opt[New],
      body: ObjBody,
      companion: Opt[ModuleDef],
      annotations: Ls[Annot],
  ) extends ClassDef:
    val paramsOpt: Opt[ParamList] = S(params)
  
  case class Plain(
      owner: Opt[InnerSymbol],
      kind: ClsLikeKind,
      sym: ClassSymbol, bsym: BlockMemberSymbol,
      tparams: Ls[TyParam],
      ext: Opt[New],
      body: ObjBody, companion: Opt[CompanionValue],
      annotations: Ls[Annot]
  ) extends ClassDef:
    val paramsOpt: Opt[ParamList] = N
  
end ClassDef


case class TypeDef(
  sym: TypeAliasSymbol,
  tparams: Ls[TyParam],
  rhs: Opt[Term],
  companion: Opt[CompanionValue],
  annotations: Ls[Annot],
) extends TypeLikeDef


// TODO Store optional source locations for the flags instead of booleans
final case class FldFlags(mut: Bool, spec: Bool, genGetter: Bool, pat: Bool, value: Bool):
  def showDbg: Str = 
    val flags = Buffer.empty[String]
    if mut then flags += "mut"
    if spec then flags += "spec"
    if genGetter then flags += "gen"
    if pat then flags += "pattern"
    if value then flags += "val"
    flags.mkString(" ")
  override def toString: String = "‹" + showDbg + "›"

object FldFlags:
  val empty: FldFlags = FldFlags(false, false, false, false, false)
  object benign:
    // * Some flags like `mut` and `module` are "benign" in the sense that they don't affect code-gen
    def unapply(flags: FldFlags): Bool =
      !flags.spec && !flags.genGetter


sealed abstract class Elem:
  def subTerms: Ls[Term] = this match
    case Fld(_, term, asc) => term :: asc.toList
    case Spd(_, term) => term :: Nil
  def showDbg: Str
object Elem:
  given Conversion[Term, Elem] = PlainFld(_)
final case class Fld(flags: FldFlags, term: Term, asc: Opt[Term]) extends Elem with FldImpl
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
    flags.showDbg + sym


final case class Param(flags: FldFlags, sym: VarSymbol, sign: Opt[Term], modulefulness: Modulefulness) 
extends Declaration with AutoLocated:
  def subTerms: Ls[Term] = sign.toList
  override protected def children: List[Located] = sym :: sign.toList
  def showDbg: Str = flags.toString + sym + sign.fold("")(": " + _.showDbg)

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
  def showDbg: Str = flags.showDbg + (params :+ restParam.fold("")("..." + _)).mkString("(", ", ", ")")
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
  def showDbg: Str = flags.showDbg + self.term.showDbg
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
