package hkmc2
package bbml

class PrettyPrinter(output: String => Unit):
  def print(ty: GeneralType): Unit =
    output(s"Type: ${ty}")
    val bounds = PrettyPrinter.collectBounds(ty)(using Set.empty).distinct
    if !bounds.isEmpty then
      output("Where:")
      bounds.foreach {
        case (lhs, rhs) => output(s"  $lhs <: $rhs")
      }

object PrettyPrinter:
  def apply(output: String => Unit): PrettyPrinter = new PrettyPrinter(output)

  type Bound = (Type, Type) // * Type <: Type
  type TVCache = Set[Uid[Type.InfVar]]

  private def collectBounds(ty: GeneralType)(using cache: TVCache): List[Bound] = ty match
    case Type.ClassType(_, targs) => targs.flatMap {
      case Wildcard(in, out) => collectBounds(in) ++ collectBounds(out)
      case ty: Type => collectBounds(ty)
    }
    case v @ Type.InfVar(_, uid, state) if !cache(uid) =>
      val newCache = cache + uid
      given TVCache = newCache
      state.lowerBounds.flatMap(bd => (bd, v) :: collectBounds(bd)) ++ state.upperBounds.flatMap(bd => (v, bd) :: collectBounds(bd))
    case Type.FunType(args, ret, eff) => args.flatMap(collectBounds) ++ collectBounds(ret) ++ collectBounds(eff)
    case PolyFunType(args, ret, eff) => args.flatMap(collectBounds) ++ collectBounds(ret) ++ collectBounds(eff)
    case Type.ComposedType(lhs, rhs, pol) => collectBounds(lhs) ++ collectBounds(rhs)
    case Type.NegType(ty) => collectBounds(ty)
    case PolyType(tvs, body) => tvs.flatMap(collectBounds) ++ collectBounds(body)
    case _ => Nil
