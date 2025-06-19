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
      case QuantType.Forall(al, ty) => 
        doc"∀${al.show}. ${ty.showAsTypeImpl(ForallPrec)}"
          |> parens(ForallPrec)
      case QuantType.Constr(c, ty) => 
        val cons = doc"${c.show}" |> parens(ConstrPrec)
        doc"${cons} => ${ty.showAsTypeImpl(ForallPrec)}"
          |> parens(ForallPrec)
      case PosType.Unit() => "()"
      case PosType.Var(al) => al.show
      case PosType.Lam(al, sigma) => 
        doc"${al.show} -> ${sigma.showAsTypeImpl(ArrowRhsPrec)}"
          |> parens(ArrowLhsPrec)
      case PosType.Mrked(al, m) =>
        if ctx.showMarks then doc"(${al.show})^m${m.uid}" else al.show
      case NegType.Var(al) => al.show
      case NegType.App(sigma, al) => 
        doc"${sigma.showAsTypeImpl(ArrowLhsPrec)} -> ${al.show}"
          |> parens(ArrowLhsPrec)

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
      case QuantType.Forall(_, ty) => ty.showAsTermImpl(prec)
      // find the outermost non-constr sigma
      case QuantType.Constr(c, ty) =>
        val (cons, sigma) = getOutermostNonConstr(ty)
        val bindings = (c :: cons).map(_.showAsTerm).mkString("; ")
        doc"let ${bindings} in ${sigma.showAsTermImpl(TopPrec)}"
          |> parens(TopPrec)

      case PosType.Unit() => "()"
      case PosType.Var(al) => al.show
      case PosType.Lam(al, sigma) =>
        doc"λ${al.show} -> ${sigma.showAsTermImpl(LamPrec)}"
          |> parens(LamPrec)
      case PosType.Mrked(al, m) => al.show
      case _ => "???"

// m
class Mark(val uid: Int) derives CanEqual
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

  def showAsTerm(using ctx: NamingCtx) = 
    def parens(p: Int)(d: Document): Document =
      if p < BindingPrec then doc"(${d})" else d
    val (beta, rhs) = ub match
      case NegType.Var(al) => (al, doc"${lb.showAsTermImpl(BindingPrec)}")
      case NegType.App(sigma, al) => (al,
        doc"${lb.showAsTermImpl(FunPrec)} ${sigma.showAsTermImpl(ArgPrec)}"
          |> parens(BindingPrec))
    doc"${beta.show} = ${rhs}"

// α, β
class TypeVar(val prefix: String, val uid: Int) extends Type:
  def refresh(using ctx: InferenceCtx, mapping: Map[Int, TypeVar]) =
    mapping.getOrElse(uid, this)

  def canonicalize(using ctx: CanonicalizeCtx): TypeVar =
    ctx.mapping.get(uid).map(new TypeVar("γ", _)).getOrElse(this)

  def show(using NamingCtx) = showAsTypeImpl(TopPrec)

  override def equals(that: Any) = that match
    case al: TypeVar => uid == al.uid
    case _ => false

  override def hashCode() = uid

// σ
enum QuantType extends Type derives CanEqual:
  case Base(ty: PosType)
  case Forall(al: TypeVar, ty: QuantType)
  case Constr(c: Constraint, ty: QuantType)

  def canonicalize(using ctx: CanonicalizeCtx): QuantType = this match
    case Base(ty) => Base(ty.canonicalize)
    case Constr(c, ty) => Constr(c.canonicalize, ty.canonicalize)
    case Forall(al, ty) =>
      ctx.counter += 1
      ctx.mapping.addOne((al.uid, -ctx.counter))
      Forall(al.canonicalize, ty.canonicalize)

  def refresh(using ctx: InferenceCtx, mapping: Map[Int, TypeVar])
    : QuantType = this match
    case Base(ty) => Base(ty.refresh)
    case Constr(c, ty) => Constr(c.refresh, ty.refresh)
    case Forall(al, ty) =>
      given mapping1: Map[Int, TypeVar] =
        mapping + (al.uid -> ctx.getFreshTv(al.prefix))
      Forall(mapping1(al.uid), ty.refresh)

// τ^+
enum PosType extends Type derives CanEqual:
  case Unit()
  case Var(al: TypeVar)
  case Lam(al: TypeVar, sigma: QuantType)
  case Mrked(al: TypeVar, m: Mark)

  def canonicalize(using ctx: CanonicalizeCtx): PosType = this match
    case Unit() => Unit()
    case Var(al) => Var(al.canonicalize)
    case Lam(al, sigma) => Lam(al.canonicalize, sigma.canonicalize)
    case Mrked(al, m) => Var(al.canonicalize)

  def refresh(using InferenceCtx, Map[Int, TypeVar]): PosType = this match
    case Unit() => Unit()
    case Var(al) => Var(al.refresh)
    case Lam(al, sigma) => Lam(al.refresh, sigma.refresh)
    case Mrked(al, m) => Mrked(al.refresh, m)

// τ^-
enum NegType extends Type derives CanEqual:
  case Var(al: TypeVar)
  case App(sigma: QuantType, al: TypeVar)

  def canonicalize(using ctx: CanonicalizeCtx): NegType = this match
    case Var(al) => Var(al.canonicalize)
    case App(sigma, al) => App(sigma.canonicalize, al.canonicalize)


  def refresh(using InferenceCtx, Map[Int, TypeVar]): NegType = this match
    case Var(al) => Var(al.refresh)
    case App(sigma, al) => App(sigma.refresh, al.refresh)

object QuantType:
  def fromVar(al: TypeVar) = QuantType.Base(PosType.Var(al))

type CtxElem = TypeVar | Constraint

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
    case (al: TypeVar) :: cons => QuantType.Forall(al, quantify(cons, ty))
    case (c: Constraint) :: cons => QuantType.Constr(c, quantify(cons, ty))
    case _ => QuantType.Base(ty)

  def inferType(term: CoreTerm)
    (using ctx: InferenceCtx): (PosType, List[CtxElem]) = term match
    case CoreTerm.Unit => (PosType.Unit(), Nil)
    case CoreTerm.Var(x) =>
      (PosType.Mrked(ctx.mappings(x), ctx.getFreshMrk), Nil)
    case CoreTerm.Lam(x, body) =>
      val al = ctx.getFreshTv(x)
      (PosType.Lam(al, wrap(inferType(body)(using ctx.scoped(Map(x-> al)))))
        , al :: Nil)
    case CoreTerm.App(t1, t2) =>
      val al = ctx.getFreshTv("α")
      val (typos1, cctx) = inferType(t1)
      val lhs = QuantType.Base(typos1)
      val rhs = NegType.App(wrap(inferType(t2)), al)
      (PosType.Var(al), cctx ++ (al :: (Constraint(lhs, rhs, Nil)) :: Nil))
    case CoreTerm.Let(bindings, body) =>
      val vars = Set.from(bindings.map(_._1))
      val mapping = Map.from(vars.map(name => (name, ctx.getFreshTv(name))))
      given InferenceCtx = ctx.scoped(mapping)
      val constraints = bindings.map((x, t) =>
        Constraint(wrap(inferType(t)), NegType.Var(mapping(x)), Nil))
      val (ty, dctx) = inferType(body)
      (ty, List.from(mapping.map(_._2)) ++ constraints ++ dctx)


class CtxSolver(var unresolved: List[CtxElem])(using ctx: InferenceCtx):
  var upperBounds = MutMap.empty[TypeVar, MutSet[NegType]]
  var lowerBounds = MutMap.empty[TypeVar, MutSet[QuantType]]
  // note: resolved is stored in reversed order
  type ResolvedElem = CtxElem | (List[Mark], TypeVar, QuantType)
  var resolved = List.empty[ResolvedElem]
  var quantCache = MutMap.empty[(Set[Mark], TypeVar), QuantType]
  // var quantCache = MutMap.empty[(Set[Mark], QuantType), QuantType]

  def showFront(using NamingCtx) = unresolved match
    case (al: TypeVar) :: _ => al.show
    case (c: Constraint) :: _ => c.show
    case _ => ""

  def step = unresolved match
    case (al: TypeVar) :: cons =>
      resolved = al :: resolved
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
    case (QuantType.Constr(c1, sigma), pi: NegType.App) =>
      ("C-Constr", None, List(c1.withMrks(c.mrks),
                              Constraint(sigma, pi, c.mrks)))
    case (QuantType.Base(PosType.Var(al)), ty) =>
      // check if we can skip
      if upperBounds.getOrElseUpdate(al, MutSet.empty).contains(ty) then
        ("C-Skip", None, List.empty)
      else
        val lbs = lowerBounds.getOrElseUpdate(al, MutSet.empty)
        // if ty is a type var, install lower bounds
        ty.asVar.map(ub => lowerBounds.getOrElseUpdate(ub, MutSet.empty)
          .addAll(lbs).add(QuantType.fromVar(al)))
        // install transitive upper bound for our lower bounds (including al)
        for lb <- lbs.flatMap(_.asVar).concat(Some(al)) do
          upperBounds.getOrElseUpdate(lb, MutSet.empty).add(ty)
        given Map[Int, TypeVar] = Map.empty
        // note that we avoid cases where lb = al, which may happen?
        ("C-App", Some(c), lbs.iterator.filter(_ != QuantType.fromVar(al))
          .map(lb => Constraint(lb.refresh, ty, c.mrks)).toList)
        // ("C-App", Some(c), lbs.iterator.filter(_ != QuantType.fromVar(al))
        //   .map(lb => Constraint(lb, ty, c.mrks)).toList)
    case (sigma, NegType.Var(al)) =>
      if lowerBounds.getOrElseUpdate(al, MutSet.empty).contains(sigma) then
        ("C-Skip", None, List.empty)
      else
        val ubs = upperBounds.getOrElseUpdate(al, MutSet.empty)
        // if sigma is a type var, install upper bounds
        sigma.asVar.map(lb => upperBounds.getOrElseUpdate(lb, MutSet.empty)
          .addAll(ubs).add(NegType.Var(al)))
        // install transitive lower bound for our upper bounds (including al)
        for ub <- ubs.flatMap(_.asVar).concat(Some(al)) do
          lowerBounds.getOrElseUpdate(ub, MutSet.empty).add(sigma)
        given Map[Int, TypeVar] = Map.empty
        // note that we avoid cases where ub = al, which may happen?
        ("C-App2", Some(c),  ubs.iterator.filter(_ != NegType.Var(al))
          .map(ub => Constraint(sigma, ub.refresh, c.mrks)).toList)
        // ("C-App2", Some(c),  ubs.iterator.filter(_ != NegType.Var(al))
        //   .map(ub => Constraint(sigma, ub, c.mrks)).toList)

    case (QuantType.Base(PosType.Lam(al, sigma)), NegType.App(sigma1, beta)) =>
      val c1 = Constraint(sigma1, NegType.Var(al), c.mrks)
      val c2 = Constraint(sigma, NegType.Var(beta), c.mrks)
      ("C-Fun", None, List(c1, c2))

    case (QuantType.Base(PosType.Mrked(al, m)), pi: NegType.App) =>
      ("C-Unwrap", None,
        List(Constraint(QuantType.fromVar(al), pi, m :: c.mrks)))

    case (QuantType.Forall(al, sigma), pi: NegType.App) =>
      // val canonicalSigma = sigma.canonicalize(
      //   using CanonicalizeCtx(1, MutMap((al.uid -> -1))))
      quantCache.get((Set.from(c.mrks), al)) match
      case Some(sigma1) =>
        ("C-Forall1", None, List(Constraint(sigma1, pi, c.mrks)))
      case None =>
        quantCache += (Set.from(c.mrks), al) -> sigma
        ("C-Forall2", Some(al), List(Constraint(sigma, pi, c.mrks)))
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

