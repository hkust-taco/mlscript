package hkmc2.bbml

import mlscript.utils.*, shorthands.*

import Type.*

class TypeTraverser:
  def apply(pol: Bool)(ty: GeneralType): Unit = ty match
    case Top | Bot =>
    case NegType(ty) => apply(!pol)(ty)
    case FunType(args, ret, eff) =>
      args.foreach(apply(!pol))
      apply(pol)(ret)
      apply(pol)(eff)
    case ClassLikeType(name, targs) =>
      targs.foreach:
        case Wildcard(in, out) =>
          apply(!pol)(in)
          apply(pol)(out)
        case ty: Type =>
          apply(pol)(ty)
          apply(!pol)(ty)
    case InfVar(vlvl, uid, state, _) =>
      if pol then state.lowerBounds.foreach(apply(true))
      else state.upperBounds.foreach(apply(false))
    case ComposedType(lhs, rhs, _) =>
      apply(pol)(lhs)
      apply(pol)(rhs)
    case PolyType(tv, outer, body) =>
      apply(pol)(body)
    case PolyFunType(args, ret, eff) =>
      args.foreach(apply(!pol))
      apply(pol)(ret)
      apply(pol)(eff)
    case ty: Type => apply(pol)(ty.toBasic) // TODO improve impl for all ctors
