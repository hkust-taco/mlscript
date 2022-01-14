package mlscript

/**
  * Convert types to typescript declarations
  */
sealed trait TypeSourceCode { self: Type => 

    def toSourceCode: SourceCode = this match {
        case Union(TypeName("true"), TypeName("false")) | Union(TypeName("false"), TypeName("true")) => SourceCode("bool")
        case Union(lhs, rhs) => SourceCode.sepBy(List(lhs.toSourceCode, rhs.toSourceCode), SourceCode.separator)
        case Inter(lhs, rhs) => SourceCode.sepBy(List(lhs.toSourceCode, rhs.toSourceCode), SourceCode.ampersand)
        // typescript function types must have a named parameter
        // e.g. (val: number) => string
        // however this name can be different from the parameter in the actual
        // definition. There are two approaches to solve this -
        // 1. generate unique parameter name locally such as arg0, arg1..
        // 2. lookup program context to use meaningful parameter names
        // currently approach 1 is implemented as passing program context
        // requires additional complexity but is a TODO.
        case Function(lhs, rhs) => funcTypeHelper(lhs, rhs)
        case Record(fields) => SourceCode.recordWithEntries(fields.map(entry => (SourceCode(entry._1.name), entry._2.toSourceCode)))
        case Tuple(fields) => SourceCode.array(fields.map(field => field._2.toSourceCode))
        // TODO
        case Recursive(uv, body) => SourceCode("TODO") ++ uv.toSourceCode ++ body.toSourceCode
        case AppliedType(base, targs) => SourceCode(base.name) ++ SourceCode.openAngleBracket ++ SourceCode.sepBy(targs.map(_.toSourceCode)) ++ SourceCode.closeAngleBracket
        // Neg requires creating a new type variable to store
        // the negated definition this operation might also need
        // to update the context with the new name if the negated
        // type is being used in other places. TODO
        case Neg(base) => SourceCode("T extends ") ++ base.toSourceCode ++ SourceCode(" ? never : T")
        case Rem(base, names) => SourceCode("Omit") ++ SourceCode.openAngleBracket ++ base.toSourceCode ++ SourceCode.commaSpace ++ SourceCode.record(names.map(name => SourceCode(name.name))) ++ SourceCode.closeAngleBracket
        // TODO: handle conversion since typescript does not support lower bounds
        case Bounds(lb, ub) => SourceCode("TODO") ++ lb.toSourceCode ++ ub.toSourceCode
        case WithExtension(base, rcd) => Inter(Rem(base, rcd.fields.map(tup => tup._1)), rcd).toSourceCode
        case Top => SourceCode("unknown")
        case Bot => SourceCode("never")
        case TypeName(name) => SourceCode(name)
        case Literal(IntLit(n)) => SourceCode(n.toString)
        case Literal(DecLit(n)) => SourceCode(n.toString)
        case Literal(StrLit(s)) => SourceCode("\"" + s + "\"")
        case TypeVar(identifier, nameHint) => SourceCode("type") ++ SourceCode.space ++ SourceCode(this.toString)
    }

    // function changes how bound variables are processed so
    // they have to be handled in a look ahead style
    // function output is positive polarity and takes upper bound
    // function input is negative polarity and takes lower bound
    // otherwise handle normally
    def funcTypeHelper(lhs: Type, rhs: Type): SourceCode = {
        (lhs, rhs) match {
            case (Bounds(llb, _), Bounds(_, rub)) => SourceCode.concat(List(
                                                (SourceCode("arg0") ++ SourceCode.colon ++ llb.toSourceCode).parenthesized,
                                                rub.toSourceCode
                                            ))
            case (Bounds(llb, _), rhs) => SourceCode.concat(List(
                                                (SourceCode("arg0") ++ SourceCode.colon ++ llb.toSourceCode).parenthesized,
                                                rhs.toSourceCode
                                            ))
            case (lhs, Bounds(_, rub)) => SourceCode.concat(List(
                                                (SourceCode("arg0") ++ SourceCode.colon ++ lhs.toSourceCode).parenthesized,
                                                rub.toSourceCode
                                            ))
            case (lhs, rhs) => SourceCode.concat(List(
                                                (SourceCode("arg0") ++ SourceCode.colon ++ lhs.toSourceCode).parenthesized,
                                                rhs.toSourceCode
                                            ))
        }
    }
}

object Typegen {

}
