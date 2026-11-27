package hkmc2
package typing
package logicsub

import hkmc2.utils.*, shorthands.*
import semantics.InfVarSymbol

class TypeTraverser:
  /** Visits the operands of a bound and its fallbacks. A fallback belongs
    * to the enclosing disjunction and carries no independent obligation. */
  def apply(c: SubOr): Unit =
    apply(true)(c.x)
    apply(false)(c.y)
    c.cs.foreach(_.foreach(apply))

  protected def invariant(pol: Bool, ty: Type): Unit =
    apply(pol)(ty)
    apply(!pol)(ty)

  def apply(pol: Bool)(ty: Type): Unit = ty.toBasic match
    case Union(x, y) => 
      apply(pol)(x)
      apply(pol)(y)
    case Inter(x, y) =>
      apply(pol)(x)
      apply(pol)(y)
    case Neg(ty) => apply(!pol)(ty)
    case ClassLikeType(name, targs, refine, _, _) =>
      targs.foreach:
        case Wildcard(in, out) if in eq out => invariant(!pol, in)
        case Wildcard(in, out) =>
          apply(!pol)(in)
          apply(pol)(out)
        case ty: Type => invariant(pol, ty)
      refine.values.foreach(apply(pol))
    case _ =>

/** Visits the inference variables reachable from a type, including variables
  * mentioned only by an effect, a bound, or a guarded alternative. Each
  * variable's state is visited once, including in recursive types. */
class BoundTraverser(using ctx: InfCtx) extends TypeTraverser:
  private val visited = scala.collection.mutable.HashSet.empty[InfVarSymbol]

  // Reachability does not depend on variance. Walk nested invariant arguments once.
  override protected def invariant(pol: Bool, ty: Type): Unit = apply(pol)(ty)

  def visitType(ty: InfType): Unit = ty match
    case t: Type => apply(true)(t)
    case PolyFunType(args, ret, eff) =>
      args.foreach(visitType)
      visitType(ret)
      visitType(eff)
    case PolyType(vars, outer, bounds, body) =>
      outer.foreach(visitType)
      vars.foreach(visitType)
      visitType(body)
      bounds.foreach(visitBound)

  def visitBound(bound: SubOr): Unit = apply(bound)

  protected def visitVariable(v: InfVar): Unit =
    ctx.varSt.get(v.sym).foreach: st =>
      st.lowerBounds.foreach(lb => visitBound(SubOr(lb, v)))
      st.upperBounds.foreach((ub, cs) => visitBound(SubOr(v, ub, cs)))

  final override def apply(pol: Bool)(t: Type): Unit = t.toBasic match
    case v: InfVar =>
      if visited.add(v.sym) then visitVariable(v)
    case _ => super.apply(pol)(t)

class TypeMap:
  def apply(c: SubOr): SubOr =
    SubOr(apply(true)(c.x), apply(false)(c.y), c.cs.map(_.map(apply)))

  def applyArg(pol: Bool)(t: TypeArg): TypeArg =
    Wildcard(apply(!pol)(t.negPart), apply(pol)(t.posPart))
  def apply(pol: Bool)(t: Type): Type = t.toBasic match
    case Bot | Top | _: InfVar => t
    case Union(x, y) => Union(apply(pol)(x), apply(pol)(y))
    case Inter(x, y) => Inter(apply(pol)(x), apply(pol)(y))
    case Neg(x) => Neg(apply(!pol)(x))
    case ClassLikeType(n, args, refine, i,o) =>
      ClassLikeType(n, args.map(applyArg(pol)), refine.mapValues(t => apply(pol)(t)), i,o)
