package hkmc2
package typing
package logicsub

import hkmc2.utils.*, shorthands.*

// class TypeTraverser:
//   def apply(pol: Bool)(ty: Type): Unit = ty.toBasic match
//     case Union(x, y) => 
//       apply(pol)(x)
//       apply(pol)(y)
//     case Inter(x, y) =>
//       apply(pol)(x)
//       apply(pol)(y)
//     case Neg(ty) => apply(!pol)(ty)
//     case ClassLikeType(name, targs, refine) =>
//       targs.foreach:
//         case Wildcard(in, out) =>
//           apply(!pol)(in)
//           apply(pol)(out)
//         case ty: Type =>
//           apply(pol)(ty)
//           apply(!pol)(ty)
//       refine.values.foreach(apply(pol))
//     case _ =>

class TypeMapper:
  def applyArg(pol: Bool)(t: TypeArg): TypeArg = ???
  def apply(pol: Bool)(t: Type): Type = t.toBasic match
    case Bot | Top | _: InfVar => t
    case Union(x, y) => Union(apply(pol)(x), apply(pol)(y))
    case Inter(x, y) => Inter(apply(pol)(x), apply(pol)(y))
    case Neg(x) => Neg(apply(!pol)(x))
    case ClassLikeType(n, args, refine, i,o) =>
      ClassLikeType(n, args.map(applyArg(pol)), refine.mapValues(t => apply(pol)(t)), i,o)
