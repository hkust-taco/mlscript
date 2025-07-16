package hkmc2
package typing.supremef

import scala.language.strictEquality
import scala.collection.mutable.{LinkedHashMap => MutMap, LinkedHashSet => MutSet}

import mlscript.utils.GenHelper
import mlscript.utils.shorthands.*
import hkmc2.syntax.Tree
import hkmc2.semantics.*
import hkmc2.document.*
import Message.MessageContext
import hkmc2.syntax.Keyword

private val TopPrec = 0

private val ArrowLhsPrec = 10
private val ArrowRhsPrec = 9
private val ForallPrec = 9
private val ConstrPrec = 11

private val BindingPrec = 1
private val LamPrec = 5
private val ArgPrec = 20
private val FunPrec = 10

enum CoreTerm derives CanEqual:
  case Unit
  case Cond
  case Var(x: String)
  case Lam(x: String, body: CoreTerm)
  case App(t1: CoreTerm, t2: CoreTerm)
  case Let(bindings: List[(String, CoreTerm)], body: CoreTerm)

  def show = showImpl(TopPrec)
  private def showImpl(prec: Int): Document =
    def parens(p: Int)(d: Document): Document =
      if p < prec then doc"(${d})" else d
    this match
      case Unit => "()"
      case Cond => "cond"
      case Var(x) => x
      case Lam(x, body) =>
        doc"λ${x}. ${body.showImpl(LamPrec)}" |> parens(LamPrec)
      case App(t1, t2) =>
        doc"${t1.showImpl(FunPrec)} ${t2.showImpl(ArgPrec)}" |> parens(LamPrec)
      case Let(bindings, body) =>
        val binder = bindings.map((x, y) =>
          doc"${x} = ${y.showImpl(BindingPrec)}").mkString("; ")
        doc"let ${binder} in ${body.showImpl(TopPrec)}" |> parens(TopPrec)

sealed trait Type:
  def asVar: Option[TypeVar] = this match
    case al: TypeVar => Some(al)
    case QuantType.Base(ty) => ty.asVar
    case PosType.Var(al) => Some(al)
    case NegType.Var(al) => Some(al)
    case _ => None

  // note: we use the same outermost naming ctx to ensure consistency
  def showAsType(using NamingCtx): Document = showAsTypeImpl(TopPrec)
  def showAsTypeImpl(prec: Int)(using ctx: NamingCtx): Document = 
    def parens(p: Int)(d: Document): Document =
      if p < prec then doc"(${d})" else d
    this match
      case al: TypeVar => ctx.lookupTypeVar(al)
      case QuantType.Base(ty) => ty.showAsTypeImpl(prec)
      case QuantType.Forall(al, m, ty) => 
        doc"∀^m${m.uid} ${al.show}. ${ty.showAsTypeImpl(ForallPrec)}"
          |> parens(ForallPrec)
      case QuantType.Constr(c, ty) => 
        val cons = doc"${c.show}" |> parens(-1)
        doc"${cons} => ${ty.showAsTypeImpl(ForallPrec)}"
          |> parens(ForallPrec)
      case PosType.Unit() => "()"
      case PosType.Var(al) => al.show
      case PosType.Lam(al: TypeVar, sigma) => 
        doc"${al.show} -> ${sigma.showAsTypeImpl(ArrowRhsPrec)}"
          |> parens(ArrowLhsPrec)
      case PosType.Lam(al: NegType.Force, sigma) => 
        doc"${al.showAsTypeImpl(ArrowLhsPrec)} -> ${sigma.showAsTypeImpl(ArrowRhsPrec)}"
          |> parens(ArrowLhsPrec)
      case PosType.Mrked(al, m) =>
        if ctx.showMarks then doc"(${al.show})^m${m.uid}" else al.show
      case NegType.Var(al) => al.show
      case NegType.App(sigma, al) => 
        doc"${sigma.showAsTypeImpl(ArrowLhsPrec)} -> ${al.show}"
          |> parens(ArrowLhsPrec)
      case _: NegType.Force => "!"

  def showAsTypeLatex(using NamingCtx): Document = showAsTypeLatexImpl(TopPrec, 0)
  // newline is Some(indent) if we need to have anewline with indent level of indentation
  // indent is the current level of indentation, regardless of wether we need to break the line or not
  def showAsTypeLatexImpl(prec: Int, indent: Int)(using ctx: NamingCtx): Document =
    def parens(p: Int)(d: Document): Document =
      if p < prec then doc"(${d})" else d
    def varAsLatex(v: String): Document =
      // we assmue that v match [a-Z]*[0-9]*
      val firstDigitIndex = v.indexWhere(_.isDigit) match
        case -1 => v.length()
        case i => i
      val name = v.substring(0, firstDigitIndex) match
        case "α" => doc"\alpha"
        case other => doc"$other"
      val subscript = v.substring(firstDigitIndex)
      doc"$$${name}_{${subscript}}$$"
    this match
      case al: TypeVar => varAsLatex(ctx.lookupTypeVar(al))
      case QuantType.Base(ty) => ty.showAsTypeLatexImpl(prec, indent)
      case QuantType.Forall(al, mrk, ty) =>
        val rest = ty match
          case _: (QuantType.Base | QuantType.Forall) => ty.showAsTypeLatexImpl(ForallPrec, indent)
          case _: QuantType.Constr =>
            doc"\n${"  "*(indent+1)}${ty.showAsTypeLatexImpl(ForallPrec, indent+1)}"
        doc"$$\forall^{${mrk.uid}}$$${al.showLatex}.$rest"
      case QuantType.Constr(c, ty) =>
        val rest = ty.showAsTypeLatexImpl(ForallPrec, indent)
        doc"${c.showLatex(indent)} $$\implies$$\n${"  "*indent}$rest"
      case PosType.Unit() => doc"$$\tyUnit$$"
      case PosType.Var(al) => al.showLatex
      case PosType.Lam(al, sigma) =>
        val rhs = sigma match
          case _: (QuantType.Base | QuantType.Forall) => sigma.showAsTypeLatexImpl(ArrowRhsPrec, indent)
          case _: QuantType.Constr =>
            doc"\n${"  "*(indent+1)}${sigma.showAsTypeLatexImpl(ArrowRhsPrec, indent+1)}"
        al match
          case a: TypeVar => doc"${a.showLatex} $$\rightarrow$$ $rhs"
          case a: NegType.Force => doc"${a.showAsTypeLatexImpl(ArrowLhsPrec, indent)} $$\rightarrow$$ $rhs"
      case PosType.Mrked(al, m) =>
        if ctx.showMarks then doc"${al.showLatex}$$^{${m.uid}}$$" else al.showLatex
      case NegType.Var(al) => al.showLatex
      case NegType.App(sigma, al) =>
        doc"${sigma.showAsTypeLatexImpl(ArrowLhsPrec, indent)} $$\rightarrow$$ ${al.showLatex}"
      case _:NegType.Force => doc"$$\bullet$$"

  def showAsTerm(using ctx: NamingCtx) = showAsTermImpl(TopPrec)
  def showAsTermImpl(prec: Int)(using ctx: NamingCtx): Document =
    def parens(p: Int)(d: Document): Document =
      if p < prec then doc"(${d})" else d
    def getOutermostNonConstr(sigma: QuantType)
      : (List[Constraint], QuantType) = sigma match
      case _: QuantType.Base => (Nil, sigma)
      case _: QuantType.Forall => (Nil, sigma)
      case QuantType.Constr(c, ty) =>
        val (cons, sigma1) = getOutermostNonConstr(ty)
        (c :: cons, sigma1)
    this match
      case al: TypeVar => ctx.lookupTypeVar(al)
      case QuantType.Base(ty) => ty.showAsTermImpl(prec)
      case QuantType.Forall(_, _, ty) => ty.showAsTermImpl(prec)
      // find the outermost non-constr sigma
      case QuantType.Constr(c, ty) =>
        val (cons, sigma) = getOutermostNonConstr(ty)
        val bindings = (c :: cons).map(_.showAsTerm).mkString("; ")
        doc"let ${bindings} in ${sigma.showAsTermImpl(TopPrec)}"
          |> parens(TopPrec)

      case PosType.Unit() => "()"
      case PosType.Var(al) => al.show
      case PosType.Lam(al: TypeVar, sigma) =>
        doc"λ${al.show} -> ${sigma.showAsTermImpl(LamPrec)}"
          |> parens(LamPrec)
      case PosType.Lam(al: NegType.Force, sigma) =>
        doc"λ${al.showAsTermImpl(LamPrec)} -> ${sigma.showAsTermImpl(LamPrec)}"
          |> parens(LamPrec)
      case PosType.Mrked(al, m) => al.show
      case _ => "???"

// m
class Mark(val uid: Int) extends Ordered[Mark] derives CanEqual:
  override def compare(that: Mark): Int = uid - that.uid

// c
class Constraint(val lb: QuantType, val ub: NegType, val mrks: List[Mark])
  derives CanEqual:
  def refresh(using InferenceCtx, Map[Int, TypeVar]) =
    Constraint(lb.refresh, ub.refresh, mrks)

  def canonicalize(using CanonicalizeCtx) =
    Constraint(lb.canonicalize, ub.canonicalize, Nil)

  def withMrks(newMrks: List[Mark]) = Constraint(lb, ub, newMrks)

  def show(using ctx: NamingCtx) =
    val s = if ctx.showMarks && !mrks.isEmpty then
      mrks.map(m => f"m${m.uid}").mkString("[", ",","]") else ""
    doc"${lb.showAsTypeImpl(TopPrec)} ≤${s} ${ub.showAsTypeImpl(TopPrec)}"

  def showLatex(using ctx: NamingCtx)(indent: Int) =
    val s = if ctx.showMarks && !mrks.isEmpty then
      mrks.map(m => f"${m.uid}").mkString("", ",","") else ""
    (lb, ub) match
      case (_, _: NegType.Var) =>
        val lhs = ub.showAsTypeLatexImpl(TopPrec, indent)
        val rhs = lb.showAsTypeLatexImpl(TopPrec, indent+1)
        doc"${lhs} $$\geq^{${s}}$$ ${rhs}"
      case (QuantType.Base(_:(PosType.Mrked | PosType.Var)), _) =>
        val lhs = lb.showAsTypeLatexImpl(TopPrec, indent)
        val rhs = ub.showAsTypeLatexImpl(TopPrec, indent+1)
        doc"${lhs} $$\leq^{${s}}$$ (${rhs})"
      case (_, _) =>
        val lhs = lb.showAsTypeLatexImpl(TopPrec, indent)
        val rhs = ub.showAsTypeLatexImpl(TopPrec, indent+1)
        doc"(${lhs}) $$\leq^{${s}}$$ (${rhs})"

  def showAsTerm(using ctx: NamingCtx): Document = 
    def parens(p: Int)(d: Document): Document =
      if p < BindingPrec then doc"(${d})" else d
    val (beta, rhs) = ub match
      case NegType.Var(al) => (al, doc"${lb.showAsTermImpl(BindingPrec)}")
      case NegType.App(sigma, al) => (al,
        doc"${lb.showAsTermImpl(FunPrec)} ${sigma.showAsTermImpl(ArgPrec)}"
          |> parens(BindingPrec))
      case NegType.Force(_) => return doc"•"
    doc"${beta.show} = ${rhs}"

// α, β
class TypeVar(val prefix: String, val uid: Int) extends Type:
  def refresh(using ctx: InferenceCtx, mapping: Map[Int, TypeVar]) =
    mapping.getOrElse(uid, this)

  def canonicalize(using ctx: CanonicalizeCtx): TypeVar =
    ctx.mapping.get(uid).map(new TypeVar("γ", _)).getOrElse(this)

  def show(using NamingCtx) = showAsTypeImpl(TopPrec)

  def showLatex(using NamingCtx): Document = showAsTypeLatexImpl(TopPrec, 0)

  override def equals(that: Any) = that match
    case al: TypeVar => uid == al.uid
    case _ => false

  override def hashCode() = uid

// σ
enum QuantType extends Type derives CanEqual:
  case Base(ty: PosType)
  case Forall(al: TypeVar, mrk: Mark, ty: QuantType)
  case Constr(c: Constraint, ty: QuantType)

  def canonicalize(using ctx: CanonicalizeCtx): QuantType = this match
    case Base(ty) => Base(ty.canonicalize)
    case Constr(c, ty) => Constr(c.canonicalize, ty.canonicalize)
    case Forall(al, m, ty) =>
      ctx.counter += 1
      ctx.mapping.addOne((al.uid, -ctx.counter))
      Forall(al.canonicalize, m, ty.canonicalize)

  def refresh(using ctx: InferenceCtx, mapping: Map[Int, TypeVar])
    : QuantType = this match
    case Base(ty) => Base(ty.refresh)
    case Constr(c, ty) => Constr(c.refresh, ty.refresh)
    case Forall(al, m, ty) =>
      given mapping1: Map[Int, TypeVar] =
        mapping + (al.uid -> ctx.getFreshTv(al.prefix))
      Forall(mapping1(al.uid), m, ty.refresh)

// τ^+
enum PosType extends Type derives CanEqual:
  case Unit()
  case Var(al: TypeVar)
  case Lam(al: TypeVar | NegType.Force, sigma: QuantType)
  case Mrked(al: TypeVar, m: Mark)

  def canonicalize(using ctx: CanonicalizeCtx): PosType = this match
    case Unit() => Unit()
    case Var(al) => Var(al.canonicalize)
    case Lam(al: TypeVar, sigma) => Lam(al.canonicalize, sigma.canonicalize)
    case Lam(al: NegType.Force, sigma) => Lam(al, sigma.canonicalize)
    case Mrked(al, m) => Var(al.canonicalize)

  def refresh(using InferenceCtx, Map[Int, TypeVar]): PosType = this match
    case Unit() => Unit()
    case Var(al) => Var(al.refresh)
    case Lam(al: TypeVar, sigma) => Lam(al.refresh, sigma.refresh)
    case Lam(al: NegType.Force, sigma) => Lam(al, sigma.refresh)
    case Mrked(al, m) => Mrked(al.refresh, m)

// τ^-
enum NegType extends Type derives CanEqual:
  case Var(al: TypeVar)
  case App(sigma: QuantType, al: TypeVar)
  case Force(toplevel: Boolean)

  def canonicalize(using ctx: CanonicalizeCtx): NegType = this match
    case Var(al) => Var(al.canonicalize)
    case App(sigma, al) => App(sigma.canonicalize, al.canonicalize)
    case x => x


  def refresh(using InferenceCtx, Map[Int, TypeVar]): NegType = this match
    case Var(al) => Var(al.refresh)
    case App(sigma, al) => App(sigma.refresh, al.refresh)
    case x => x

object QuantType:
  def fromVar(al: TypeVar) = QuantType.Base(PosType.Var(al))

type CtxElem = (TypeVar, Mark) | Constraint

class Typer(using Raise):
  def checkWellFormed(term: CoreTerm) = checkWellFormedImpl(term)(using Set())
  def fromTerm(term: Term): CoreTerm = 
    val res = term match
      case Term.Blk(stats, res) =>
        def getBindings(stats: List[Statement])
          : List[(String, CoreTerm)] = stats match
          case LetDecl(_, _) :: ss => getBindings(ss)
          case (d: TermDefinition) :: ss if d.body.isDefined =>
            (d.sym.nme, fromTerm(d.body.get)) :: getBindings(ss)
          case DefineVar(sym, t) :: ss =>
            (sym.nme, fromTerm(t)) :: getBindings(ss)
          case t :: ss =>
            raise(ErrorReport(msg"invalid term ${t.toString}" -> t.toLoc::Nil))
            getBindings(ss)
          case Nil => Nil
        fromTerm(res) match
          case CoreTerm.Let(bindings, body) =>
            CoreTerm.Let(getBindings(stats) ++ bindings, body)
          case x => CoreTerm.Let(getBindings(stats), x)
      case Term.IfLike(_: Keyword.`if`.type, Split.Let(s, cond, Split.Cons(Branch(_, _, Split.Else(t1)), Split.Else(t2)))) =>
        CoreTerm.App(CoreTerm.App(CoreTerm.App(CoreTerm.Cond, fromTerm(cond)), fromTerm(t1)), fromTerm(t2))
      case Term.Lit(Tree.UnitLit(_)) => CoreTerm.Unit
      case Term.UnitVal() => CoreTerm.Unit
      case Term.Lam(ParamList(flags, p :: ps, rest), body) =>
        val body1 = fromTerm(Term.Lam(ParamList(flags, ps, rest), body))
        CoreTerm.Lam(p.sym.nme, body1)
      case Term.Lam(ParamList(_, Nil, _), body) => fromTerm(body)
      case Term.App(lhs, Term.Tup(Fld(_, rhs, _) :: Nil)) =>
        CoreTerm.App(fromTerm(lhs), fromTerm(rhs))
      case Term.Ref(sym) => CoreTerm.Var(sym.nme)
      case _ =>
        val m = msg"invalid term ${term.toString}"
        raise(ErrorReport(m -> term.toLoc :: Nil))
        CoreTerm.Unit
    res match
      case CoreTerm.Let(Nil, body) => body
      case _ => res

  def checkWellFormedImpl(term: CoreTerm)(using ctx: Set[String])
    : Unit = term match
    case CoreTerm.Unit => ()
    case CoreTerm.Cond => ()
    case CoreTerm.Var(x) => if !ctx.contains(x) then
      raise(ErrorReport( msg"invalid scope ${x}" -> None :: Nil))
    case CoreTerm.Lam(x, body) =>
      if ctx.contains(x) then
        raise(ErrorReport( msg"invalid scope ${x}" -> None :: Nil))
      checkWellFormedImpl(body)(using ctx + x)
    case CoreTerm.App(t1, t2) =>
      checkWellFormedImpl(t1); checkWellFormedImpl(t2)
    case CoreTerm.Let(bindings, body) =>
      val variables = Set.from(bindings.map(_._1))
      val intersections = ctx.intersect(variables)
      if !intersections.isEmpty then
        val first = bindings.find((x, _) => intersections.contains(x)).get
        raise(ErrorReport( msg"invalid scope ${first._1}" -> None :: Nil))
      given Set[String] = ctx ++ variables
      for (_, t) <- bindings do checkWellFormedImpl(t)
      checkWellFormedImpl(body)

  def wrap(pair: (PosType, List[CtxElem])): QuantType =
    quantify(pair._2, pair._1)
  def quantify(constraints: List[CtxElem], ty: PosType)
    : QuantType = constraints match
    case (al: TypeVar, m) :: cons => QuantType.Forall(al, m, quantify(cons, ty))
    case (c: Constraint) :: cons => QuantType.Constr(c, quantify(cons, ty))
    case _ => QuantType.Base(ty)

  def inferType(term: CoreTerm)
    (using ctx: InferenceCtx): (PosType, List[CtxElem]) = term match
    case CoreTerm.Unit => (PosType.Unit(), Nil)
    case CoreTerm.Cond => 
      val al = ctx.getFreshTv("α")
      (PosType.Lam(NegType.Force(false), QuantType.Base(PosType.Lam(al, QuantType.Base(PosType.Lam(al, QuantType.fromVar(al)))))),
        (al, ctx.getFreshMrk) :: Nil)
    case CoreTerm.Var(x) =>
      (PosType.Mrked(ctx.mappings(x), ctx.getFreshMrk), Nil)
    case CoreTerm.Lam(x, body) =>
      val al = ctx.getFreshTv(x)
      (PosType.Lam(al, wrap(inferType(body)(using ctx.scoped(Map(x-> al)))))
        , (al, ctx.getFreshMrk) :: Nil)
    case CoreTerm.App(t1, t2) =>
      val al = ctx.getFreshTv("α")
      val (typos1, cctx) = inferType(t1)
      val lhs = QuantType.Base(typos1)
      val rhs = NegType.App(wrap(inferType(t2)), al)
      (PosType.Var(al), cctx ++ ((al, ctx.getFreshMrk) :: (Constraint(lhs, rhs, Nil)) :: Nil))
    case CoreTerm.Let(bindings, body) =>
      val vars = Set.from(bindings.map(_._1))
      val mapping = Map.from(vars.iterator.map(name => (name, ctx.getFreshTv(name))))
      given InferenceCtx = ctx.scoped(mapping)
      val constraints = bindings.map((x, t) =>
        Constraint(wrap(inferType(t)), NegType.Var(mapping(x)), Nil))
      val (ty, dctx) = inferType(body)
      (ty, List.from(mapping.map(_._2).map((_, ctx.getFreshMrk))) ++ constraints ++ dctx)


def unify(ty1: Type, ty2: Type)
  (using bv: Set[Int], naming: NamingCtx, rai: Raise): List[Constraint] =
  (ty1, ty2) match
  case (al: TypeVar, be: TypeVar) =>
    val alBounded = bv.contains(al.uid)
    val beBounded = bv.contains(be.uid)
    if al.uid == be.uid then List.empty
    else if alBounded && beBounded then List.empty
    else
      Constraint(QuantType.fromVar(al), NegType.Var(be), Nil) :: 
      Constraint(QuantType.fromVar(be), NegType.Var(al), Nil) :: Nil
  case (QuantType.Base(a), QuantType.Base(b)) => unify(a, b)
  case (QuantType.Forall(a, _, s1), QuantType.Forall(b, _, s2)) =>
    unify(s1, s2)(using (bv + a.uid + b.uid))
  case (QuantType.Constr(c1, s1), QuantType.Constr(c2, s2)) =>
    unifyConstr(c1, c2) ++ unify(s1, s2)
  case (PosType.Unit(), PosType.Unit()) => List.empty
  case (PosType.Var(al), PosType.Var(be)) => unify(al, be)
  case (PosType.Lam(al, s1), PosType.Lam(be, s2)) => unify(al, be) ++ unify(s1, s2)
  case (PosType.Mrked(al, _), PosType.Mrked(be, _)) => unify(al, be)
  case (NegType.Var(al), NegType.Var(be)) => unify(al, be)
  case (NegType.App(s1, al), NegType.App(s2, be)) => unify(s1, s2) ++ unify(al, be)
  case _ =>
    val a = ty1.showAsType.toString
    val b = ty2.showAsType.toString
    raise(ErrorReport(msg"attempt to unify ${a} with ${b}" -> None::Nil))
    List.empty

def unifyConstr(c1: Constraint, c2: Constraint)
  (using bv: Set[Int], naming: NamingCtx, rai: Raise): List[Constraint] =
  unify(c1.lb, c2.lb) ++ unify(c1.ub, c2.ub)

class CtxSolver(var unresolved: List[CtxElem])(using rai: Raise, naming: NamingCtx, ctx: InferenceCtx):
  var upperBounds = MutMap.empty[TypeVar, MutMap[(NegType, Set[Mark]), NegType]]
  var lowerBounds = MutMap.empty[TypeVar, MutMap[(QuantType, Set[Mark]), QuantType]]
  // note: resolved is stored in reversed order
  type ResolvedElem = CtxElem | (List[Mark], TypeVar, QuantType)
  var resolved = List.empty[ResolvedElem]
  var quantCache = MutMap.empty[Set[Mark], QuantType.Forall]
  var results = MutSet.empty[PosType]

  def showFront(using NamingCtx) = unresolved match
    case (al: TypeVar, _) :: _ => al.show
    case (c: Constraint) :: _ => c.show
    case _ => ""

  def showFrontLatex(using NamingCtx) = unresolved match
    case (al: TypeVar, _) :: _ => al.showLatex
    case (c: Constraint) :: _ => c.showLatex(0)
    case _ => ""

  def step = unresolved match
    case (al: TypeVar, m) :: cons =>
      resolved = (al, m) :: resolved
      unresolved = cons
      ("C-Promote", Some(al), List.empty[Constraint])
    case (c: Constraint) :: cons =>
      val res = handleCon(c)
      if res._2.isDefined then resolved = res._2.get :: resolved
      unresolved = res._3 ++ cons
      res
    case _ => ("", Option.empty[ResolvedElem], List.empty[Constraint])

  def handleCon(c: Constraint)
    : (String, Option[ResolvedElem], List[Constraint]) = (c.lb, c.ub) match
    case (QuantType.Constr(c1, sigma), pi: (NegType.App | NegType.Force)) =>
      ("C-Constr", None, List(c1.withMrks(c.mrks),
                              Constraint(sigma, pi, c.mrks)))
    case (QuantType.Base(PosType.Var(al)), ty) =>
      val canonical = ty.canonicalize(using CanonicalizeCtx(0, MutMap.empty))
      // check if we can skip
      if upperBounds.getOrElseUpdate(al, MutMap.empty)
          .contains((canonical, c.mrks.toSet)) then
        ("C-Skip", None, List.empty)
      else
        val lbs = lowerBounds.getOrElseUpdate(al, MutMap.empty)
        // if ty is a type var, install lower bounds
        ty.asVar.map(ub => lowerBounds.getOrElseUpdate(ub, MutMap.empty)
          .addOne((QuantType.fromVar(al), c.mrks.toSet), QuantType.fromVar(al)))
        upperBounds.getOrElseUpdate(al, MutMap.empty).addOne((ty, c.mrks.toSet), canonical)
        given Map[Int, TypeVar] = Map.empty
        ("C-Var1", Some(c), lbs.iterator
          .map((key, lb) => Constraint(lb.refresh, ty, key._2.toList ++ c.mrks)).toList)
    case (sigma, NegType.Var(al)) =>
      val canonical = sigma.canonicalize(using CanonicalizeCtx(0, MutMap.empty))
      if lowerBounds.getOrElseUpdate(al, MutMap.empty).contains((canonical, c.mrks.toSet)) then
        ("C-Skip", None, List.empty)
      else
        val ubs = upperBounds.getOrElseUpdate(al, MutMap.empty)
        // if sigma is a type var, install upper bounds
        sigma.asVar.map(lb => upperBounds.getOrElseUpdate(lb, MutMap.empty)
          .addOne((NegType.Var(al), c.mrks.toSet), NegType.Var(al)))
        lowerBounds.getOrElseUpdate(al, MutMap.empty).addOne((canonical, c.mrks.toSet), sigma)
        given Map[Int, TypeVar] = Map.empty
        // note that we avoid cases where ub = al, which may happen?
        ("C-Var2", Some(c),  ubs.iterator
          .map((key, ub) => Constraint(sigma, ub.refresh, c.mrks ++ key._2)).toList)

    case (QuantType.Base(PosType.Lam(al, sigma)), NegType.App(sigma1, beta)) =>
      val a = al match
        case alpha: TypeVar => NegType.Var(alpha)
        case bullet: NegType.Force => bullet
      val c1 = Constraint(sigma1, a, c.mrks)
      val c2 = Constraint(sigma, NegType.Var(beta), c.mrks)
      ("C-Fun", None, List(c1, c2))

    case (QuantType.Base(PosType.Mrked(al, m)), _: (NegType.App | NegType.Force)) =>
      ("C-Unwrap", None,
        List(Constraint(QuantType.fromVar(al), c.ub, m :: c.mrks)))

    case (QuantType.Forall(al, m, sigma), pi: (NegType.App | NegType.Force)) =>
      val marks = Set.from(c.mrks.iterator.concat(Some(m)))
      quantCache.get(marks) match
      case None =>
        quantCache += marks -> QuantType.Forall(al, m, sigma)
        ("C-Forall1", Some((al, m)), List(Constraint(sigma, pi, c.mrks)))
      case Some(old) =>
        val eqConstr = unify(c.lb, old)(using Set.empty[Int])
        ("C-Forall2", None, eqConstr ++ List(Constraint(old.ty, pi, c.mrks)))

    case (QuantType.Base(x: PosType.Lam), NegType.Force(top)) => 
      if top then results += x
      ("C-FunForce", None, Nil)
    case (QuantType.Base(x: PosType.Unit), NegType.Force(top)) =>
      if top then results += x
      ("C-UnitForce", None, Nil)

    // e.g. application where lhs is a unit
    case _ => ("C-Err", None, Nil)

class InferenceCtx(var root: Option[InferenceCtx],
                   val mappings: Map[String, TypeVar]):
  var mrkUid = 0
  var tvUid = 0

  def scoped(maps: Map[String, TypeVar]) = InferenceCtx(
    if root.isEmpty then Some(this) else root, mappings ++ maps)

  def getFreshMrk =
    val r = getRoot
    r.mrkUid += 1
    Mark(r.mrkUid)

  def getFreshTv(prefix: String = "α") =
    val r = getRoot
    r.tvUid += 1
    new TypeVar(prefix, r.tvUid)

  private def getRoot = root match
    case Some(r) => r
    case None => this

class NamingCtx(val showMarks: Boolean):
  private var varmapping = MutMap.empty[Int, String]
  private var usedNames = MutSet.empty[String]
  private var uid = 0
  def lookupTypeVar(al: TypeVar) =
    varmapping.getOrElseUpdate(al.uid, getUniqueName(al.prefix))
  def getUniqueName(prefix: String) =
    val name = if usedNames.contains(prefix) then
      var counter = 0
      while usedNames.contains(f"${prefix}${counter}") do counter += 1
      f"${prefix}${counter}"
    else
      prefix
    usedNames.add(name)
    name

class CanonicalizeCtx(var counter: Int, var mapping: MutMap[Int, Int])

