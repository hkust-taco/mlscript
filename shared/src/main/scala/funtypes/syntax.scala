package funtypes


// Terms

final case class Pgrm(defs: List[(Boolean, String, Term)])

sealed abstract class Term                                                extends TermImpl with Statement
sealed abstract class Lit                                                 extends Term
final case class Var(name: String)                                        extends Term
final case class Lam(lhs: Term, rhs: Term)                                extends Term
final case class App(lhs: Term, rhs: Term)                                extends Term
final case class Tup(fields: List[(String, Term)])                        extends Term
final case class Rcd(fields: List[(String, Term)])                        extends Term
final case class Sel(receiver: Term, fieldName: String)                   extends Term
final case class Let(isRec: Boolean, name: String, rhs: Term, body: Term) extends Term
final case class Blk(stmts: List[Statement]) extends Term

final case class IntLit(value: BigInt)     extends Lit
final case class DecLit(value: BigDecimal) extends Lit
final case class StrLit(value: String)     extends Lit

sealed trait Statement extends StatementImpl
final case class LetS(isRec: Boolean, pat: Term, rhs: Term) extends Statement


// Types

sealed abstract class Type extends TypeImpl

final case class Union(lhs: Type, rhs: Type)             extends Type
final case class Inter(lhs: Type, rhs: Type)             extends Type
final case class Function(lhs: Type, rhs: Type)          extends Type
final case class Record(fields: List[(String, Type)])    extends Type
final case class Recursive(uv: TypeVar, body: Type)      extends Type

sealed abstract class NullaryType                        extends Type

case object Top                                          extends NullaryType
case object Bot                                          extends NullaryType

final case class Primitive(name: String)                 extends NullaryType
final class TypeVar(val nameHint: String, val hash: Int) extends NullaryType {
  override def toString: String = s"$nameHint:$hash"
}

