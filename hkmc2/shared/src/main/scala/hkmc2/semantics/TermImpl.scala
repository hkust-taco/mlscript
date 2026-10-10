package hkmc2
package semantics

import scala.collection.mutable.{Buffer, Set as MutSet, LinkedHashSet}

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

import Term.*



trait Describable:
  def describe: Str


type AnyRef_ = AnyRefImpl & Term

trait AnyRefImpl:
  self: Term.Ref | Term.SimpleRef | Term.MemberRef | Term.SelfRef =>
  def tree: Tree.Ident
  def sym: Symbol

trait NewRefImpl extends AnyRefImpl:
  self: Term.SimpleRef | Term.MemberRef | Term.SelfRef =>
  def refNum: Int = 0 // TODO: track reference counts like in the old refs?

trait NewSelImpl extends NewResolvableImpl:
  self: Term.NewSel =>
  // At least one receiver permits runtime lookup without a static member symbol.
  var hasDynamicTarget: Bool = false
  // Resolution records a numeric tuple projection; lowering emits an indexed
  // access rather than looking for a nominal field symbol.
  var tupleIndex: Opt[Int] = N
  var resolvedMembers: Ls[BlockMemberSymbol] = Nil // * filled during resolution
  // Unlike a field whose value happens to be a class, C.class has a class
  // target without an ordinary member. Its receiver remains the class reference.
  def isClassValue(using Erasure): Bool =
    !isErroneous && self.cls.isEmpty && self.id.name == "class" && resolvedMembers.isEmpty &&
      !hasDynamicTarget && resolvedTargets.exists(_.isInstanceOf[ClassSymbol])
  def hasAmbiguousClass(using Erasure): Bool = hasAmbiguousClassImpl
  // Also used by the guarded symbol lookup for completed imports.
  private[semantics] def hasAmbiguousClassImpl: Bool = projectionClassesImpl.sizeCompare(1) > 0
  def projectionClasses(using Erasure): Ls[ClassSymbol] = projectionClassesImpl
  private def projectionClassesImpl: Ls[ClassSymbol] =
    self.cls.toList.flatMap: qualifier =>
      qualifier.resolvedTargets.collect { case cls: ClassSymbol => cls }.distinct

trait UnresolvedRefImpl extends NewResolvableImpl:
  self: Term.UnresolvedRef =>
  // Retain the receiver as well as the definition: two instances can expose
  // the same member symbol without denoting the same storage location.
  var resolvedMembers: Ls[(Term, BlockMemberSymbol)] = Nil
  var dynamicPrefixes: Ls[Term] = Nil


// trait FldImpl extends AutoLocated:
trait FldImpl:
  self: Fld =>
  def children: Vector[Located] = self.term +: self.asc.toVector
  def show(using Scope, ShowCfg, Raise): Document = flags.show(true) :: self.term.show
  def showDbg(using DebugPrinter): Str = flags.show(true) + self.term.showDbg
  def describe: Str =
    (if self.flags.spec then "specialized " else "") +
    (if self.flags.mut then "mutable " else "") +
    self.term.describe


trait BlkImpl:
  this: Blk =>
  def mkBlkClone(using State, Erasure): Blk = Blk(stats.map(_.mkClone), res.mkClone)
  def showTopLevel(using Scope, ShowCfg, Raise): Document =
    (stats ::: (res match
      case Lit(Tree.UnitLit(false)) => Nil
      case res => res :: Nil)).map(_.show).mkDocument(doc", # ")


trait LeadingDotSelImpl(using State):
  self: Term.LeadingDotSel =>
  val resSym: FlowSymbol = FlowSymbol.lds(self.nme.name)
  var resolvedTargets: Ls[flow.SelectionTarget.CompanionMember] = Nil // * filled during flow analysis


type AnyResolvable = Resolvable | NewResolvableImpl
// type AnyRef = Ref | SimpleRef | MemberRef

type NewResolvable = NewResolvableImpl & Term

/** Suppress follow-on diagnostics after a resolution or flow error. */
trait PossiblyErroneous:
  var isErroneous: Bool = false

trait NewResolvableImpl extends PossiblyErroneous:
  self: MemberRef | NewSel | UnresolvedRef | Super =>
  var resolvedTargets: Ls[DefinitionSymbol[?]] = Nil // * filled during flow analysis
  // val resSym: FlowSymbol = FlowSymbol.simpleRef(self.sym.name)
  // var disamb: Opt[Disambiguation] = None // * filled during flow analysis


trait StatementImpl extends Located, ProductWithExtraInfo, Describable:
  this: Statement =>
    
  def mkClone(using State, Erasure): Statement = this match
    case t: Term => lastWords(s"overridden implementation")
    case d: Definition => ???
    case imp: Import => Import(imp.sym, imp.str, imp.file)(imp.toLoc)
    case LetDecl(sym, annotations) => LetDecl(sym, annotations.map(_.mkClone))(toLoc)
    case RcdField(field, rhs, sym) => RcdField(field.mkClone, rhs.mkClone, sym)
    case RcdSpread(rcd) => RcdSpread(rcd.mkClone)
    case DefineVar(sym, rhs) => DefineVar(sym, rhs.mkClone)(toLoc)
    case sc: SetConfig => sc
  
  def describe: Str =
    val desc = this match
      case Error() => "‹error›"
      case UnitVal() => "unit value"
      case DynTy() => "dynamic type"
      case _: Rcd => "record literal"
      case Lit(lit) => lit.describeLit
      case Ref(sym) => "reference"
      case Capture(base, thru) => base.describe
      case SimpleRef(sym) => "reference"
      case MemberRef(sym) => "member reference"
      case UnresolvedRef(_, _) => "wildcard-open reference"
      case App(lhs, rhs) => "application"
      case TyApp(lhs, targs) => "type application"
      case _: Super => "super reference"
      case NewSel(pre, nme, _) => "selection"
      case Sel(pre, nme) => "selection"
      case SynthSel(pre, nme) => "selection"
      case DynSel(o, f, _, checked) => if checked then "array index" else "dynamic selection"
      case Tup(fields) => "tuple literal"
      case CtxTup(fields) => "contextual tuple literal"
      case IfLike(_, IfLikeForm.ReturningIf, body) => "`if` expression"
      case IfLike(_, IfLikeForm.ImperativeIf, body) => "`if` statement"
      case IfLike(_, IfLikeForm.While, body) => "`while` statement"
      case SynthIf(split) => "synthetic `if` expression"
      case SynthWhile(split) => "synthetic `while` expression"
      case Lam(params, body) => "function literal"
      case FunTy(lhs, rhs, eff) => "function type"
      case Forall(tvs, outer, body) => "universal quantification"
      case Constrained(constraints, body) => "constrained type"
      case WildcardTy(in, out) => "wildcard type"
      case Blk(stats, res) => "block"
      case Quoted(term) => "quoted term"
      case Unquoted(term) => "unquoted term"
      case New(cls, args, rft) => "object instantiation"
      case DynNew(cls, args) => "dynamic object instantiation"
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
      case _: Handle => "handler expression"
      case Missing => "missing"
      case LeadingDotSel(name) => "leading dot selection"
      case Resolved(t, sym) => t.describe
      case td: TermDefinition => s"term definition '${td.sym.nme}'"
      case cls: ClassDef => s"class definition '${cls.sym.nme}'"
      case mod: ModuleOrObjectDef => s"module/object definition '${mod.sym.nme}'"
      case td: TypeDef => s"type definition '${td.bsym.nme}'"
      case s => TODO(s)
    this match
      case self: Resolvable => self.resolvedTyp match
        case S(typ) => s"${desc} of type ${typ.show}"
        case N => desc
      case _ => desc
  
  def extraInfo(using DebugPrinter): Str = this match
    case s: AnySel if s.resolvedTargets.nonEmpty =>
      s"targets=${s.resolvedTargets.map(_.showAsPlain).mkString("[", ",", "]")}"
    case r: Resolvable if r.legacyResolvedSym.isDefined || r.resolvedTyp.isDefined => (
        r.legacyResolvedSym.map(s => s"sym=${s.showAsPlain}") ::
        r.resolvedTyp.map(s => s"typ=${s.showDbg}") :: Nil
      ).flatten.mkString(",")
    case r: SelProj => r.symbol.mkString
    case _ => ""
  
  def subStatements: Vector[Statement] = this match
    case Blk(stats, res) => stats.toVector :+ res
    case _ => subTerms
  def subTerms: Vector[Term] = this match
    case Error() | Missing | _: Lit | _: AnyRef_ | _: DynTy | _: UnitVal => Vector.empty
    case Capture(base, thru) => Vector.single(base)
    case Resolved(t, sym) => Vector.single(t)
    case App(lhs, rhs) => Vector.double(lhs, rhs)
    case RcdField(lhs, rhs, _) => Vector.double(lhs, rhs)
    case RcdSpread(bod) => Vector.single(bod)
    case FunTy(lhs, rhs, eff) => Vector.double(lhs, rhs) ++ eff.toVector
    case TyApp(pre, tarsg) => pre +: tarsg.toVector
    case Sel(pre, _) => Vector.single(pre)
    case SynthSel(pre, _) => Vector.single(pre)
    case Super(receiver, _, _) => Vector.single(receiver)
    case NewSel(pre, _, cls) => Vector.single(pre) ++ cls.toVector
    case UnresolvedRef(prefixes, _) => prefixes.toVector
    case DynSel(o, f, _, _) => Vector.double(o, f)
    case Tup(fields) => fields.flatMap(_.subTerms).toVector
    case Mut(und) => Vector.single(und)
    case CtxTup(fields) => fields.flatMap(_.subTerms).toVector
    case IfLike(_, _, split) => split.subTerms
    case SynthIf(split) => split.subTerms
    case SynthWhile(split) => split.subTerms
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
    case t: AnyRef_ => treeOrSubterms(t.tree)
    case t: Tup => treeOrSubterms(t.tree)
    case l: Lam => Vector.double(l.params, l.body)
    case t: App => treeOrSubterms(t.tree)
    case IfLike(_, _, split) => Vector.single(split)
    case SynthIf(split) => Vector.single(split)
    case SynthWhile(split) => Vector.single(split)
    case SynthSel(pre, nme) => Vector.double(pre, nme)
    case Sel(pre, nme) => Vector.double(pre, nme)
    case SelProj(prefix, cls, proj) => Vector.triple(prefix, cls, proj)
    case _ =>
      subTerms // TODO more precise (include located things that aren't terms)
  
  def show(using Scope, ShowCfg, Raise): Document =
    
    def showSelTargets(sel: AnySel): Document =
      val str = sel.nme.name
      val ts = sel.resolvedTargets
      ts match
      case Nil =>
        // doc"$str‹?›"
        doc"${str}ˀˀˀ"
      case t :: Nil => t.show
      case ts => doc"$str‹" :: ts.map(_.show).mkDocument(", ") :: doc"›"
    
    def res: Document = this match
      case lit: Lit => lit.lit.idStr
      case UnitVal() => doc"()"
      case DynTy() => doc"dyn"
      case r: SimpleRef =>
        r.sym match
        case _: BuiltinSymbol => r.sym.nme
        case _ => r.sym.showName
      case r: MemberRef => r.sym.showName
      case r: UnresolvedRef => doc"${r.id.name}"
      case sr: SelfRef => s"${sr.sym.showName}.this"
      case Capture(base, thru) =>
        // doc"${base.show}⟨${thru.showName}⟩"
        doc"${base.show}^${thru.showName}"
      case r: Ref =>
        r.sym match
        case _: BuiltinSymbol => r.sym.nme
        case _ => r.sym.showName
      case sup: Super => doc"super.${sup.id.name}"
      case sel: NewSel =>
        val str = sel.id.name
        val pre = sel.cls.fold(doc"${sel.prefix.show}.")(cls => doc"${sel.prefix.show}.${cls.show}#")
        if summon[ShowCfg].showFlowSymbols
        then doc"$pre${
            sel.resolvedMembers match
            case Nil if sel.resolvedTargets.nonEmpty =>
              doc"$str‹" :: sel.resolvedTargets.distinct.map(_.showName).mkDocument(", ") :: doc"›"
            case Nil => doc"${str}ˀˀˀ"
            case t :: Nil => t.showName
            case ts => doc"$str‹" :: ts.map(_.showName).mkDocument(", ") :: doc"›"
          }"
        else doc"$pre$str"
      case sel: Sel =>
        if summon[ShowCfg].showFlowSymbols
        then doc"${sel.prefix.show}.${sel.sym.fold(doc"${
          showSelTargets(sel)}")(_.showName)}"
        else doc"${sel.prefix.show}.${sel.nme.name}"
      case sel: SynthSel =>
        if summon[ShowCfg].showFlowSymbols
        then doc"⟨${sel.prefix.show}.⟩${sel.sym.fold(doc"${
          showSelTargets(sel)}")(_.showName)}"
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
        (ld.annotations.map(_.show :: " ") ::: doc"let ${ld.sym.showName}" :: Nil).mkDocument()
      case df: DefineVar =>
        doc"${df.sym.showName} = ${df.rhs.show}"
      case td: TermDefinition =>
          td.annotations.map(_.show :: " ").mkDocument()
          :: doc"${td.k.str} ${td.bsym.showName}::${td.tsym.showName}"
          :: (if td.tparams.isEmpty then doc""
            else doc"[${td.tparams.get.map(_.sym.showName).mkDocument(", ")}]")
          :: td.params.map(_.show).mkDocument()
          :: td.sign.fold(doc"")(s => doc": ${s.show}")
          :: (if summon[ShowCfg].showFlowSymbols then doc" ‹${td.bsym.flow.showName}›" else doc"")
          :: td.body.fold(doc"")(b => doc" = ${b.show}")
      case cld: ClassLikeDef =>
          cld.annotations.map(_.show :: " ").mkDocument()
          :: doc"${cld.ctorSym.fold(doc"")("fun "::_.showName::doc" # ")}${cld.kind.str} ${cld.bsym.showName}::${cld.sym.showName}"
          :: (if cld.tparams.isEmpty then doc""
            else doc"[${cld.tparams.map(_.sym.showName).mkDocument(", ")}]")
          :: cld.paramsOpt.map(_.show).toList.mkDocument()
          :: cld.auxParams.map(_.show).mkDocument()
          :: cld.ext.fold(doc"")(e => doc" extends ${e.show}")
          :: doc" ${cld.body.blk.show}"
      case imp: Import =>
        doc"import ${"\""}.../${imp.file.last}${"\""} as ${imp.sym.showName}"
      case LeadingDotSel(name) => doc"_?_.${name.name}"
      case Error() => doc"‹error›"
      case IfLike(kw, form, split) =>
        // doc"${kw.name} ${form.headStr} ${split.show}"
        given IfLikeForm = form
        doc"${form.headStr} { #{  # ${split.show} #}  # }"
        // val fs = fomr match
      case Missing => doc"‹missing›"
      case TyApp(lhs, targs) => doc"${lhs.show}[${targs.map(_.show).mkDocument(", ")}]"
      case DynSel(prefix, field, arrayIdx, _) =>
        if arrayIdx then doc"${prefix.show}.[${field.show}]"
        else doc"${prefix.show}.(${field.show})"
      case SelProj(prefix, cls, field) => doc"${prefix.show}.${cls.show}#${field.name}"
      case Mut(underlying) => doc"mut ${underlying.show}"
      case CtxTup(fields) => doc"using (${fields.map(_.show).mkDocument(", ")})"
      case SynthIf(split) => doc"if { #{  # ${split.show} #}  # }"
      case SynthWhile(split) => doc"while { #{  # ${split.show} #}  # }"
      case FunTy(lhs, rhs, eff) =>
        doc"(${lhs.showAsParams} ->${eff.fold(doc"")(e => doc"{${e.show}}")} ${rhs.show})"
      case Forall(tvs, outer, body) =>
        val variables = tvs.map: tv =>
          tv.sym.showName
            :: tv.lb.fold(doc"")(b => doc" :> ${b.show}")
            :: tv.ub.fold(doc"")(b => doc" <: ${b.show}")
        doc"forall ${variables.mkDocument(", ")}${outer.fold(doc"")(v => doc", outer ${v.showName}")}: ${body.show}"
      case Constrained(constraints, body) =>
        val bounds = constraints.map(c => doc"${c.lhs.show} ${c.dir.showDbg} ${c.rhs.show}")
        doc"[${bounds.mkDocument(", ")}] => ${body.show}"
      case WildcardTy(in, out) =>
        doc"in ${in.fold(doc"⊥")(_.show)} out ${out.fold(doc"⊤")(_.show)}"
      case Rcd(mut, stats) =>
        (if mut then doc"mut " else doc"") :: braced:
          doc" # " :: stats.map(_.show).mkDocument(doc", # ")
      case RcdField(field, rhs, _) => doc"${field.show}: ${rhs.show}"
      case RcdSpread(record) => doc"...${record.show}"
      case Quoted(body) => doc"""code"${body.show}""""
      case Unquoted(body) => doc"$${${body.show}}"
      case DynNew(cls, args) => doc"new! ${cls.show}${args.map(_.showAsParams).mkDocument()}"
      case Asc(term, ty) => doc"(${term.show}: ${ty.show})"
      case CompType(lhs, rhs, pol) => doc"(${lhs.show} ${if pol then "|" else "&"} ${rhs.show})"
      case Neg(rhs) => doc"~(${rhs.show})"
      case Region(name, body) => doc"region ${name.showName} in ${body.show}"
      case RegRef(reg, value) => doc"(${reg.show}).ref ${value.show}"
      case Assgn(lhs, rhs) => doc"${lhs.show} := ${rhs.show}"
      case SetRef(ref, value) => doc"${ref.show} := ${value.show}"
      case Drop(term) => doc"drop ${term.show}"
      case Deref(ref) => doc"!(${ref.show})"
      case Ret(result) => doc"return ${result.show}"
      case Throw(result) => doc"throw ${result.show}"
      case Label(label, _, body, _) => doc"do ${label.showName}: ${body.show}"
      case Break(label, _, value) => doc"${label.showName}.break${value.fold(doc"")(v => doc" ${v.show}")}"
      case Continue(label) => doc"${label.showName}.continue"
      case Try(body, finallyDo) => doc"try ${body.show} finally ${finallyDo.show}"
      case Annotated(annot, target) => doc"${annot.show} ${target.show}"
      case Handle(lhs, rhs, args, _, defs, body) =>
        doc"handle ${lhs.showName} = ${rhs.show}${args.map(_.showAsParams).mkDocument()} with { #{  # ${
          defs.map(_.td.show).mkDocument(doc" # ")} #}  # } in ${body.show}"
      case td: TypeDef =>
        td.annotations.map(_.show :: " ").mkDocument()
          :: doc"type ${td.bsym.showName}::${td.sym.showName}"
          :: (if td.tparams.isEmpty then doc""
            else doc"[${td.tparams.map(_.sym.showName).mkDocument(", ")}]")
          :: td.rhs.fold(doc"")(rhs => doc" = ${rhs.show}")
      case SetConfig(_) => doc"#config(...)"
    
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
  
  end show
  
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
    case Term.DynTy() => "dyn"
    case Lit(lit) => lit.idStr
    case Resolved(t, sym) => t.showPlain
    case r @ Ref(symbol) => symbol.showAsPlain
    case r @ SimpleRef(symbol) => symbol.showAsPlain
    case r @ MemberRef(symbol) => symbol.showAsPlain
    case r @ SelfRef(sym) => sym.showAsPlain
    case Capture(base, thru) => s"${base.showDbg}^${thru.showDbg}"
    case App(lhs, rhs) => s"${lhs.showDbg}${rhs.showDbgAsParams}"
    case RcdField(lhs, rhs, _) => s"${lhs.showDbg}: ${rhs.showDbg}"
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
    case Super(_, owner, id) => s"super[${owner.showDbg}].${id.name}"
    case NewSel(pre, nme, cls) => s"${pre.showDbg}.${cls.fold("")(c => s"${c.showDbg}#")}${nme.name}"
    case UnresolvedRef(_, id) => s"${id.name}‹open›"
    case DynSel(pre, fld, _, _) => s"${pre.showDbg}[${fld.showDbg}]"
    case IfLike(kw, _, split) => s"${kw.name} { ${split.showDbg} }"
    case SynthIf(split) => s"if { ${split.showDbg} }"
    case SynthWhile(split) => s"while { ${split.showDbg} }"
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
  
end StatementImpl  


