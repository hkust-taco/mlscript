package mlscript

import mlscript.utils._, shorthands._


// Terms

final case class Pgrm(tops: Ls[Statement]) extends PgrmImpl

sealed abstract class Decl extends DesugaredStatement with DeclImpl
final case class Def(rec: Bool, nme: Str, rhs: Term \/ PolyType) extends Decl with Terms {
  val body: Located = rhs.fold(identity, identity)
}
final case class TypeDef(
  kind: TypeDefKind,
  nme: Primitive,
  tparams: List[Primitive],
  body: Type,
  mths: List[MethodDef] = Nil,
) extends Decl
final case class MethodDef(
  rec: Bool,
  prt: Primitive,
  nme: Primitive,
  tparams: List[Primitive],
  rhs: Term \/ Type,
) extends Located {
  val body: Located = rhs.fold(identity, identity)
  val children: Ls[Located] = nme :: body :: Nil
}

sealed abstract class TypeDefKind(val str: Str)
sealed trait ObjDefKind
case object Cls extends TypeDefKind("class") with ObjDefKind
case object Trt extends TypeDefKind("trait") with ObjDefKind
case object Als extends TypeDefKind("type")

sealed abstract class Term                                           extends Terms with TermImpl
sealed abstract class Lit                                            extends SimpleTerm with LitImpl
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
final case class With(trm: Term, fields: Rcd)                        extends Term
final case class CaseOf(trm: Term, cases: CaseBranches)              extends Term

sealed abstract class CaseBranches extends CaseBranchesImpl
final case class Case(pat: SimpleTerm, body: Term, rest: CaseBranches) extends CaseBranches
final case class Wildcard(body: Term) extends CaseBranches
final case object NoCases extends CaseBranches

final case class IntLit(value: BigInt)      extends Lit
final case class DecLit(value: BigDecimal)  extends Lit
final case class StrLit(value: Str)         extends Lit

sealed abstract class SimpleTerm extends Term {
  val idStr: Str = this match {
    case Var(name) => name
    case lit: Lit => lit.toString
  }
}

sealed trait Statement extends StatementImpl
final case class LetS(isRec: Bool, pat: Term, rhs: Term)  extends Statement
final case class DataDefn(body: Term)                     extends Statement
final case class DatatypeDefn(head: Term, body: Term)     extends Statement

sealed trait DesugaredStatement extends Statement with DesugaredStatementImpl

sealed trait Terms extends DesugaredStatement


// Types

sealed abstract class Type extends TypeImpl

final case class Union(lhs: Type, rhs: Type)             extends Type
final case class Inter(lhs: Type, rhs: Type)             extends Type
final case class Function(lhs: Type, rhs: Type)          extends Type
final case class Record(fields: Ls[Str -> Type])         extends Type
final case class Tuple(fields: Ls[Opt[Str] -> Type])     extends Type
final case class Recursive(uv: TypeVar, body: Type)      extends Type
final case class AppliedType(base: Primitive, targs: List[Type]) extends Type
final case class Neg(base: Type)                         extends Type
final case class Rem(base: Type, names: Ls[Var])         extends Type

sealed abstract class NullaryType                        extends Type

case object Top                                          extends NullaryType
case object Bot                                          extends NullaryType
final case class Literal(lit: Lit)                       extends NullaryType

final case class Primitive(name: Str)                    extends NullaryType
final class TypeVar(val nameHint: Str, val hash: Int)    extends NullaryType {
  override def toString: Str = s"$nameHint:$hash"
}

final case class PolyType(targs: Ls[Primitive], body: Type) extends PolyTypeImpl

