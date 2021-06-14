package funtypes

import funtypes.utils._, shorthands._


// Terms

final case class Pgrm(decls: Ls[TopLevel]) {
  override def toString = decls.map("" + _ + ";").mkString(" ")
}

sealed trait TopLevel

sealed abstract class Decl extends TopLevel
final case class Def(rec: Bool, nme: Str, body: Term) extends Decl
final case class TypeDef(kind: TypeDefKind, nme: Str, tparams: List[Str], body: Type) extends Decl

sealed abstract class TypeDefKind
case object Cls extends TypeDefKind
case object Trt extends TypeDefKind
case object Als extends TypeDefKind

sealed abstract class Term                                           extends Statement with DesugaredStatement with TermImpl
sealed abstract class Lit                                            extends SimpleTerm
final case class Var(name: Str)                                      extends SimpleTerm with VarImpl
final case class Lam(lhs: Term, rhs: Term)                           extends Term
final case class App(lhs: Term, rhs: Term)                           extends Term
final case class Tup(fields: Ls[Opt[Str] -> Term])                   extends Term
final case class Rcd(fields: Ls[Str -> Term])                        extends Term
final case class Sel(receiver: Term, fieldName: Str)                 extends Term
final case class Let(isRec: Bool, name: Str, rhs: Term, body: Term)  extends Term
final case class Blk(stmts: Ls[Statement])                           extends Term with BlkImpl
final case class Bra(rcd: Bool, trm: Term)                           extends Term
final case class Asc(trm: Term, ty: Type)                            extends Term
final case class Bind(lhs: Term, rhs: Term)                          extends Term
final case class Test(trm: Term, ty: Term)                           extends Term
final case class With(trm: Term, fieldNme: Str, fieldVal: Term)      extends Term
final case class CaseOf(trm: Term, cases: CaseBranches)              extends Term

sealed abstract class CaseBranches extends CaseBranchesImpl
final case class Case(clsNme: Str, body: Term, rest: CaseBranches) extends CaseBranches
final case object NoCases extends CaseBranches
final case object Wildcard extends CaseBranches

final case class IntLit(value: BigInt)      extends Lit
final case class DecLit(value: BigDecimal)  extends Lit
final case class StrLit(value: Str)         extends Lit

sealed abstract class SimpleTerm extends Term {
  val idStr: Str = this match {
    case Var(name) => name
    case lit: Lit => lit.toString
  }
}

sealed trait Statement extends StatementImpl with TopLevel
final case class LetS(isRec: Bool, pat: Term, rhs: Term) extends Statement
final case class DataDefn(body: Term) extends Statement
final case class DatatypeDefn(head: Term, body: Term) extends Statement

sealed trait DesugaredStatement extends DesugaredStatementImpl
final case class LetDesug(isRec: Bool, v: Var, rhs: Term)(val original: LetS) extends DesugaredStatement
final case class DatatypeDesug(head: Var, params: Ls[Term], cases: Ls[DataDesug])(val original: DatatypeDefn)
  extends DesugaredStatement
final case class DataDesug(head: Var, params: Ls[Term])(val original: Term)
  extends DesugaredStatement


// Types

sealed abstract class Type extends TypeImpl

final case class Union(lhs: Type, rhs: Type)             extends Type
final case class Inter(lhs: Type, rhs: Type)             extends Type
final case class Function(lhs: Type, rhs: Type)          extends Type
final case class Applied(lhs: Type, rhs: Type)           extends Type
final case class Record(fields: Ls[Str -> Type])         extends Type
final case class Tuple(fields: Ls[Opt[Str] -> Type])     extends Type
final case class Recursive(uv: TypeVar, body: Type)      extends Type

sealed abstract class NullaryType                        extends Type

case object Top                                          extends NullaryType
case object Bot                                          extends NullaryType

final case class Primitive(name: Str)                    extends NullaryType
final class TypeVar(val nameHint: Str, val hash: Int)    extends NullaryType {
  override def toString: Str = s"$nameHint:$hash"
}

