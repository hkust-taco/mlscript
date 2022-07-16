package mlscript.mono

import mlscript.{Type, Union, Inter, Function, Record, Tuple, Recursive, AppliedType,
                 Neg, Rem, Bounds, WithExtension, Constrained, Top, Bot, Literal,
                 TypeName, TypeVar, PolyType}

enum Expr:
  case Ref(name: String)
  case Lambda(params: List[Ref], body: Expr)
  case Apply(callee: Expr, arguments: List[Expr])
  case Tuple(fields: List[Expr])
  case Record(fields: List[(Ref, Expr)])
  case Select(receiver: Expr, field: Ref)
  case LetIn(isRec: Boolean, name: Ref, rhs: Expr, body: Expr)
  case Assign(assignee: Expr, value: Expr)
  case Subscript(receiver: Expr, index: Expr)
  case Match(scrutinee: Expr, branches: CaseBranch)
  case Literal(value: BigInt | BigDecimal | String)
  case New(apply: Option[(TypeName, List[Expr])], body: Isolation)
end Expr

enum CaseBranch:
  case Pattern(pattern: Expr.Ref | Expr.Literal, body: Expr, tail: CaseBranch)
  case Wildcard(body: Expr)
  case Empty
end CaseBranch

enum DeclKind:
  case Alias, Class, Trait

enum Item:
  case TypeDecl(name: TypeName, kind: DeclKind, typeParams: List[TypeName],
                parents: List[AppliedType], body: Isolation)
  case FuncDecl(name: Expr.Ref, body: Expr)
  case FuncDefn(name: Expr.Ref, typeParams: List[TypeName], body: PolyType)

class Isolation(items: List[Expr | Item])
