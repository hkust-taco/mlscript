package funtypes

import funtypes.utils._, shorthands._


// Terms

final case class Pgrm(defs: Ls[(Bool, Str, Term)])

sealed abstract class Term                                           extends TermImpl with Statement
sealed abstract class Lit                                            extends Term
final case class Var(name: Str)                                      extends Term
final case class Lam(lhs: Term, rhs: Term)                           extends Term
final case class App(lhs: Term, rhs: Term)                           extends Term
final case class Tup(fields: Ls[Opt[Str] -> Term])                   extends Term
final case class Rcd(fields: Ls[Str -> Term])                        extends Term
final case class Sel(receiver: Term, fieldName: Str)                 extends Term
final case class Let(isRec: Bool, name: Str, rhs: Term, body: Term)  extends Term
final case class Blk(stmts: Ls[Statement]) extends Term with BlkImpl

final case class IntLit(value: BigInt)     extends Lit
final case class DecLit(value: BigDecimal) extends Lit
final case class StrLit(value: Str)     extends Lit

sealed trait Statement extends StatementImpl
final case class LetS(isRec: Bool, pat: Term, rhs: Term) extends Statement


// Types

sealed abstract class Type extends TypeImpl

final case class Union(lhs: Type, rhs: Type)             extends Type
final case class Inter(lhs: Type, rhs: Type)             extends Type
final case class Function(lhs: Type, rhs: Type)          extends Type
final case class Record(fields: Ls[Str -> Type])         extends Type
final case class Recursive(uv: TypeVar, body: Type)      extends Type

sealed abstract class NullaryType                        extends Type

case object Top                                          extends NullaryType
case object Bot                                          extends NullaryType

final case class Primitive(name: Str)                    extends NullaryType
final class TypeVar(val nameHint: Str, val hash: Int)    extends NullaryType {
  override def toString: Str = s"$nameHint:$hash"
}

