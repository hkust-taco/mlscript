package memir

class Var(val name: String)

class Pattern(val ty: IRClassType, val vars: List[Var])

enum LetCase:
  // assign a expression value to a variable.
  case Simple(val v: Expr)
  // assign the result of a method call `f` with parameters `params` on an object
  // `obj` to a variable potentially with casting if the result type is different
  // from the variable type.
  case FunApp(val obj: Option[Val], val f: String, params: List[Val])

enum Val:
  // variable value
  case VarVal(val v: Var)
  // integer constant
  case LitInt(val v: Int)

enum Expr:
  case SimpleValue(val v: Val)
  // assign a value `c` to variable `v` of type `ty`, perform type casting if
  // needed, and allow expressions in `expr` to refer to the variable `v`.
  case LetExpr(val v: Var, val ty: IRType, val c: LetCase, val expr: Expr)
  // perform pattern matching on `v`, execute the first expression in which the
  // pattern matches.
  case MatchExpr(val v: Val, val cases: List[(Pattern, Expr)], val default: Option[Expr])

