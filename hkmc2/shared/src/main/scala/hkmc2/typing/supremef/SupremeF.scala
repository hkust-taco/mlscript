package hkmc2
package typing.supremef

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.syntax.*
import hkmc2.semantics.*
import hkmc2.document.*

import Message.MessageContext
import Elaborator.State
import Scope.scope

// import syntax.Literal

/* 
sealed abstract class Type

object Type:
  
  case class Lit(lit: Literal)
  // case class Ref(ref: Term.Ref)
  case class Ref(sym: Symbol)
  
end Type
*/


private val TopPrec = 0

private val ArrowLhsPrec = 10
private val ArrowRhsPrec = 9
private val ForallPrec = 9
// private val ConstrPrec = 11

private val LamPrec = 5
private val ArgPrec = 20
private val FunPrec = 10


sealed trait Type:
  
  def children: List[Type] = this match
    case QuantType.Base(ty) => ty :: Nil
    case QuantType.Forall(_, ty) => ty :: Nil
    case QuantType.Constr(cst, ty) => cst.in :: cst.out :: ty :: Nil
    case PosType.Inf(_) => Nil
    case PosType.Lit(_) => Nil
    case PosType.Lam(_, bod) => bod :: Nil
    case NegType.Inf(_) => Nil
    case NegType.App(lhs, rhs) => lhs :: Nil
  
  lazy val infVars: Set[InfSymbol] =
    this match
    case QuantType.Forall(inf, ty) => ty.infVars - inf
    case PosType.Inf(sym) => Set.single(sym)
    case PosType.Lam(par, bod) => bod.infVars + par
    case NegType.Inf(sym) => Set.single(sym)
    case NegType.App(lhs, rhs) => lhs.infVars + rhs
    case _ => children.iterator.flatMap(_.infVars).toSet
  
  def showAsType(using Scope): Document = showAsTypeImpl(TopPrec)
  def showAsTypeImpl(prec: Int)(using Scope): Document =
    def parens(p: Int)(d: Document): Document =
      if p < prec then doc"(${d})"
      else d
    this match
    case QuantType.Base(ty) => ty.showAsTypeImpl(prec)
    case QuantType.Forall(inf, ty) => doc"∀${inf.show}. ${ty.showAsTypeImpl(ForallPrec)}" |> parens(ForallPrec)
    case QuantType.Constr(c, ty) => doc"(${c.show}) => #{  # ${ty.showAsTypeImpl(ForallPrec)} #} " |> parens(ForallPrec)
    case PosType.Inf(sym) => sym.show
    case PosType.Lit(lit) => lit.idStr
    case PosType.Lam(par, bod) =>
      // doc"(${par.show}) => ${bod.showAsTypeImpl})"
      // doc"${par.show} # -> # ${bod.showAsTypeImpl}"
      doc"${par.show} -> ${bod.showAsTypeImpl(ArrowRhsPrec)}" |> parens(ArrowLhsPrec)
    // case NegType.Inf(sym) => scope.lookup(sym).getOrElse(scope.allocateName(sym, sym.nme))
    case NegType.Inf(sym) => sym.show
    case NegType.App(lhs, rhs) =>
      // doc"λ${lhs.showAsTypeImpl}. ${rhs.show}"
      // doc"${lhs.showAsTypeImpl} # -> # ${rhs.show}"
      doc"${lhs.showAsTypeImpl(ArrowLhsPrec)} -> ${rhs.show}" |> parens(ArrowLhsPrec)
  
  def showAsTerm(using Scope): Document = showAsTermImpl(TopPrec)
  def showAsTermImpl(prec: Int)(using Scope): Document =
    def parens(p: Int)(d: Document): Document =
      if p < prec then doc"(${d})"
      else d
    this match
    case QuantType.Base(ty) => ty.showAsTermImpl(prec)
    case QuantType.Forall(inf, ty) => ty.showAsTermImpl(prec)
    case QuantType.Constr(c, ty) => doc"${c.showAsTerm(prec)(ty)}"
    case PosType.Err => doc"‹error›"
    case PosType.Inf(sym) => sym.show
    case PosType.Lit(lit) => lit.idStr
    case PosType.Lam(par, bod) =>
      // doc"λ${par.show}. #{  # ${bod.showAsTypeImpl(ArrowRhsPrec)} #} " |> parens(ArrowLhsPrec)
      doc"λ${par.show}. ${bod.showAsTermImpl(LamPrec)}" |> parens(LamPrec)
  
end Type


object NotInf:
  // def unapply(ty: Type): Opt[ty.type] =
  //   ty match
  //   case PosType.Inf(_) => N
  //   case NegType.Inf(_) => N
  //   case _ => S(ty)
  def unapply(ty: Type): Bool =
    ty match
    case PosType.Inf(_) => false
    case NegType.Inf(_) => false
    case _ => true
end NotInf


case class Constraint(in: QuantType, out: NegType):
  def freshen(using InfSymbol): Constraint =
    Constraint(in.freshen, out.freshen)
  def show(using Scope): Document =
    // doc"${in.showAsTypeImpl} # ≤ # ${out.showAsTypeImpl}"
    doc"${in.showAsTypeImpl(TopPrec)} ≤ ${out.showAsTypeImpl(TopPrec)}"
  def showAsTerm(prec: Int)(ty: Type)(using Scope): Document =
    this match
    case Constraint(in, NegType.Inf(inf)) =>
      // doc"let ${inf.show} = #{  # ${in.showAsTermImpl(prec)} #}  in # ${ty.showAsTermImpl(prec)}"
      doc"let ${inf.show} = #{  # ${in.showAsTermImpl(prec)} #}  # in ${ty.showAsTermImpl(prec)}"
    case Constraint(in, NegType.App(arg, inf)) =>
      doc"let ${inf.show} = ${in.showAsTermImpl(FunPrec)} ${arg.showAsTermImpl(ArgPrec)} in # ${ty.showAsTermImpl(prec)}"
end Constraint


// class InfSymbol(val origin: FlowSymbol)(using State):
class InfSymbol(val origin: FlowSymbol | InfSymbol)(using State) extends Symbol:
  def toLoc: Opt[Loc] = origin.toLoc
  def nme: Str = origin.nme
  def subst(using SymbolSubst): Symbol = ???
  override def toString(): String = s"$origin^${uid}"
  def show(using Scope): Document =
    // val res = scope.lookup(this).getOrElse(scope.allocateName(this))
    // println(nme)
    // res
    scope.lookup(this).getOrElse(scope.allocateName(this))

enum QuantType extends Type:
  case Base(ty: PosType)
  case Forall(inf: InfSymbol, ty: QuantType)
  case Constr(cst: Constraint, ty: QuantType)
  
  // def showAsTypeImpl(using Scope): Document =
  //   this match
  //   case Base(ty) => ty.showAsTypeImpl
  
  // def showAsTerm: Document = ???
  
  def freshen(using InfSymbol): QuantType = this match
    case Base(ty) => Base(ty.freshen)
    case Forall(inf, ty) =>
      assert(inf.origin isnt inf)
      Forall(inf, ty.freshen)
    case Constr(cst, ty) => Constr(cst.freshen, ty.freshen)
  
end QuantType

enum PosType extends Type:
  case Err
  case Inf(sym: InfSymbol)
  case Lit(lit: Literal)
  case Lam(param: InfSymbol, body: QuantType)
  case Ctor(sym: CtorSymbol, targs: List[PosType], args: List[PosType])
  
  def freshen(using sym: InfSymbol): PosType = this match
    // case Inf(`sym`) => 
    case Inf(sym.origin) => Inf(sym)
    case Inf(_) => this
    case Lit(lit) => Lit(lit)
    case Lam(param, body) =>
      val newParam = param match
        case sym.origin => sym
        case _ => param
      Lam(newParam, body.freshen)
  
end PosType

enum NegType extends Type:
  case Inf(sym: InfSymbol)
  case App(lhs: QuantType, rhs: InfSymbol)
  case Ctor(sym: CtorSymbol)
  
  def freshen(using sym: InfSymbol): NegType = this match
    case Inf(sym.origin) => Inf(sym)
    case App(lhs, sym.origin) => App(lhs.freshen, sym)
    case App(lhs, rhs) => App(lhs.freshen, rhs)
    case Ctor(sym) => Ctor(sym)
  
end NegType

enum TypeArg:
  case Single(t: Type)
  case Bounds(lb: PosType, ub: PosType)
end TypeArg


case class Ctx(env: Map[Symbol, PosType]):
  def get(sym: Symbol): Opt[PosType] = env.get(sym)
  def +(sym_ty: Symbol -> PosType): Ctx =
    Ctx(env + sym_ty)
end Ctx

def ctx(using Ctx): Ctx = summon


enum CCtx:
  case Empty
  case Constr(ctx: CCtx, cst: Constraint) extends CCtx //with ProductWithTail
  case Bind(ctx: CCtx, sym: InfSymbol) extends CCtx //with ProductWithTail
  case Err(c: Constraint) extends CCtx
  
  def ++(that: CCtx): CCtx = that match
    case Empty => this
    case Bind(ctx, sym) => Bind(this ++ ctx, sym)
    case Constr(ctx, cst) => Constr(this ++ ctx, cst)
  
  def + (cst: Constraint): CCtx = Constr(this, cst)
  def ++ (csts: IterableOnce[Constraint]): CCtx =
    csts.iterator.foldLeft(this)((ctx, cst) => ctx + cst)
  def + (sym: InfSymbol): CCtx = Bind(this, sym)
  
  def quantify(ty: PosType): QuantType = quantify(QuantType.Base(ty))
  
  def quantify(qty: QuantType): QuantType = this match
    case Empty => qty
    case e @ Err(c) => QuantType.Base(PosType.Err)
    case Bind(ctx, sym) => ctx.quantify(QuantType.Forall(sym, qty))
    case Constr(ctx, cst) => ctx.quantify(QuantType.Constr(cst, qty))
  
  lazy val lowerBounds: Map[InfSymbol, Ls[QuantType]] = this match
    case Empty | _: Err => Map.empty
    case Bind(ctx, sym) => ctx.lowerBounds
    case Constr(ctx, Constraint(lb, NegType.Inf(inf))) =>
      val clbs = ctx.lowerBounds
      clbs.get(inf) match
        case Some(lbs) => lowerBounds + (inf -> (lb :: lbs))
        case None => clbs + (inf -> (lb :: Nil))
    case Constr(ctx, cst) => ctx.lowerBounds
  
  lazy val upperBounds: Map[InfSymbol, Ls[NegType]] = this match
    case Empty | _: Err => Map.empty
    case Bind(ctx, sym) => ctx.upperBounds
    case Constr(ctx, Constraint(QuantType.Base(PosType.Inf(inf)), ub)) =>
      val cubs = ctx.upperBounds
      cubs.get(inf) match
        case Some(ubs) => upperBounds + (inf -> (ub :: ubs))
        case None => cubs + (inf -> (ub :: Nil))
    case Constr(ctx, cst) => ctx.upperBounds
  
  def step(using TL, State): Opt[CCtx] =
    // this match
    // case Empty => N
    // case Bind(ctx, sym) => S(ctx)
    // case Constr(ctx, cst) => S(ctx)
    val LBs = lowerBounds
    // tl.log("LBs: " + LBs)
    def go(cs: CCtx, rebuild: CCtx => CCtx): Opt[CCtx] = cs match
      // case cs @ Empty => rebuild(cs)
      case Empty | _: Err => N
      case Bind(ctx, sym) => go(ctx, rebuild compose (Bind(_, sym)))
      // case Constr(ctx, c @ Constraint(QuantType.Base(PosType.Inf(inf)), ub)) =>
      //   ctx.lowerBounds.get(inf) match
      //     case N => go(ctx, Constr(_, c))
      //     case S(Nil) => die
      //     case S(lbs) =>
      //       val newCsts = lbs.map(lb => Constraint(lb, ub))
      //       val newCtx = ctx ++ newCsts
      //       S(rebuild(newCtx))
      case Constr(ctx, c) =>
        tl.log:
          given Scope = Scope.reallyEmpty
          s"Constr (${c.show}) ${c.in.getClass.getSimpleName} ${c.out.getClass.getSimpleName}"
        // tl.log(s"Constr: ${NotInf.unapply(c.out)}")
        // tl.log(s"Constr: ${c.out match { case n @ NotInf() => n; case _ => "??"}}")
        c match
        case Constraint(QuantType.Base(PosType.Lam(par, bod)), NegType.App(arg, res)) =>
          val newCtx = ctx +
            Constraint(arg, NegType.Inf(par)) +
            Constraint(bod, NegType.Inf(res))
          S(rebuild(newCtx))
        case Constraint(QuantType.Forall(inf, ty), ub @ NotInf()) =>
          val ninf = new InfSymbol(inf)
          tl.log(s"Forall: $inf ~> $ninf | $ty ~> ${ty.freshen(using ninf)}")
          S(rebuild(ctx + Constraint(ty.freshen(using ninf), ub)))
          // S(rebuild(ctx + Constraint(ty.freshen(using new InfSymbol(inf)), ub)))
        case Constraint(QuantType.Constr(c, ty), ub @ NotInf()) =>
          S(rebuild(ctx + c + Constraint(ty, ub)))
        case Constraint(QuantType.Base(PosType.Inf(inf)), ub) =>
          LBs.get(inf) match
            case N => go(ctx, rebuild compose (Constr(_, c)))
            case S(Nil) => die
            case S(lbs) =>
              // tl.log(s"LBs: $lbs <: $inf")
              val newCsts = lbs.map(lb => Constraint(lb, ub))
              val newCtx = ctx ++ newCsts
              S(rebuild(newCtx))
        case Constraint(_, NegType.Inf(inf)) =>
          go(ctx, rebuild compose (Constr(_, c)))
        // case _ =>
        //   go(ctx, rebuild compose (Constr(_, c)))
        //   // tl.log(s"ELSE...")
        //   // go(ctx, nctx =>
        //   //   tl.log(s"ELSE RE $nctx")
        //   //   Constr(nctx, c))
        case _ =>
          // S(rebuild(ctx + Err(c)))
          S(Err(c))
    go(this, identity)
  
  def gc(root: Type): CCtx =
    var infs = root.infVars
    def analyze(ctx: CCtx): Unit = ctx match
      case Empty | _: Err => ()
      case Bind(ctx, sym) => analyze(ctx)
      case Constr(ctx, cst) =>
        cst match
        case Constraint(QuantType.Base(PosType.Inf(sym)), ub)
          if lowerBounds.get(sym).isEmpty => analyze(ctx)
        case Constraint(lb @ NotInf(), NegType.Inf(sym))
          // if upperBounds.get(sym).isEmpty => analyze(ctx)
          if !infs.contains(sym) => analyze(ctx)
        case _ =>
          infs |= cst.in.infVars
          infs |= cst.out.infVars
          analyze(ctx)
    analyze(this)
    def go(ctx: CCtx): CCtx = ctx match
      case Empty => Empty
      case Err(c) => Err(c)
      case Bind(ctx, sym) =>
        if infs.contains(sym) then Bind(go(ctx), sym)
        else go(ctx)
      case Constr(ctx, cst) =>
        // if infs.contains(cst.in) || infs.contains(cst.out) then
        //   Constr(go(ctx), cst)
        // else go(ctx)
        cst match
        case Constraint(QuantType.Base(PosType.Inf(sym)), ub) =>
          if infs.contains(sym) then
            infs |= ub.infVars
            Constr(go(ctx), cst)
          else go(ctx)
        case Constraint(lb, NegType.Inf(sym)) =>
          if infs.contains(sym) then
            infs |= lb.infVars
            Constr(go(ctx), cst)
          else go(ctx)
        case _ =>
          Constr(go(ctx), cst)
    go(this)
  
  def show(using Scope): Document =
    doc" #{ ${showSeq} #} "
  def showSeq(using Scope): Document =
    this match
    case Empty => doc""
    case Err(c) => doc"ERROR: ${c.in.showAsType} ≤ ${c.out.showAsType}"
    case Bind(Empty, sym) => sym.show
    case Bind(ctx, sym) => doc"${ctx.showSeq}, # ${sym.show}"
    case Constr(Empty, cst) => cst.show
    case Constr(ctx, cst) => doc"${ctx.showSeq}, # ${cst.show}"
  
end CCtx


class Typer(using State, TL, Raise):
  // import tl.{trace, log}1
  
  // val upperBounds: mutable.Map[FlowSymbol, Ls[PosType]] = mutable.Map.empty
  
  def freshInf(sym: FlowSymbol): InfSymbol =
    new InfSymbol(sym)
  
  def typeCheck(term: Term)(using Ctx)
      : (PosType, CCtx)
      = term match
    case Term.Blk(Nil, res) => typeCheck(res)
    case Term.Lit(lit) => (PosType.Lit(lit), CCtx.Empty)
    case Term.Ref(sym) =>
      ctx.get(sym) match
        case Some(ty) => (ty, CCtx.Empty)
        case None =>
          raise(ErrorReport(
            msg"Symbol not found: ${sym.nme}" -> term.toLoc :: Nil
          ))
          (PosType.Err, CCtx.Empty)
    case app @ Term.App(f, Term.Tup(PlainFld(arg) :: Nil)) =>
      val (fTy, fCtx) = typeCheck(f)
      val (argTy, argCtx) = typeCheck(arg)
      val argQTy = argCtx.quantify(argTy)
      val resTy = freshInf(app.resSym)
      // val appTy = NegType.App(argQTy, NegType.Inf(resTy))
      val appTy = NegType.App(argQTy, resTy)
      val cst = Constraint(QuantType.Base(fTy), appTy)
      (PosType.Inf(resTy), fCtx + resTy + cst)
    case Term.Lam(PlainParamList(p :: Nil), bod) =>
      val param = freshInf(p.sym)
      val (bodTy, bodCtx) =
        given Ctx = ctx + (p.sym -> PosType.Inf(param))
        typeCheck(bod)
      val lamTy = PosType.Lam(param, bodCtx.quantify(bodTy))
      (lamTy, CCtx.Empty + param)
    // case blk @ Term.Blk(LetDecl(sym, _) :: DefineVar(sym2, rhs) :: Nil, body)
    // if sym2 is sym => // TODO: more than one!!
    //   ???
    case Term.Blk(stats, res) =>
      def go(stats: Ls[Statement]): (PosType, CCtx) = stats match
        case Nil => typeCheck(res)
        // case (term: Term) :: stats =>
        //   effBuff += typeCheck(term)._2
        //   go(stats)
        case LetDecl(sym, _) :: DefineVar(sym2, rhs) :: stats =>
          require(sym2 is sym)
          val (rhsTy, rhsCtx) = typeCheck(rhs)
          // val (bodTy, bodCtx) =
          //   given Ctx = ctx + (p.sym -> PosType.Inf(param))
          //   typeCheck(bod)
          // ctx += sym -> rhsTy
          // go(stats)
          ???
      go(stats)
    
  
end Typer




