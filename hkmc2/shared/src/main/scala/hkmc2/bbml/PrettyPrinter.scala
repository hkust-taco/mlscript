package hkmc2
package bbml

class PrettyPrinter(output: String => Unit):
  def print(ty: Type): Unit =
    output(s"Type: ${ty}")
    val bounds = PrettyPrinter.collectBounds(ty)
    if !bounds.isEmpty then
      output("Where:")
      bounds.foreach {
        case (lhs, rhs) => output(s"  $lhs <: $rhs")
      }

object PrettyPrinter:
  def apply(output: String => Unit): PrettyPrinter = new PrettyPrinter(output)

  type Bound = (Type, Type) // * Type <: Type

  private def collectBounds(ty: Type): List[Bound] = ty match
    case Type.ClassType(_, targs) => targs.flatMap {
      case Wildcard(in, out) => collectBounds(in) ++ collectBounds(out)
      case ty: Type => collectBounds(ty)
    }
    case v @ Type.InfVar(_, _, state) =>
      state.lowerBounds.flatMap(bd => (bd, v) :: collectBounds(bd)) ++ state.upperBounds.flatMap(bd => (v, bd) :: collectBounds(bd))
    case Type.FunType(args, ret, eff) => args.flatMap(collectBounds) ++ collectBounds(ret) ++ collectBounds(eff)
    case Type.ComposedType(lhs, rhs, pol) => collectBounds(lhs) ++ collectBounds(rhs)
    case Type.NegType(ty) => collectBounds(ty)
    case Type.PolymorphicType(lvl, tv, body) => Nil // TODO
    case _ => Nil
