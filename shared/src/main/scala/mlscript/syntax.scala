package mlscript

import mlscript.utils._, shorthands._


// Terms

final case class Pgrm(tops: Ls[Statement]) extends PgrmImpl

sealed abstract class Decl extends DesugaredStatement with DeclImpl
final case class Def(rec: Bool, nme: Var, rhs: Term \/ PolyType) extends Decl with Terms {
  val body: Located = rhs.fold(identity, identity)
}
final case class TypeDef(
  kind: TypeDefKind,
  nme: TypeName,
  tparams: List[TypeName],
  body: Type,
  mthDecls: List[MethodDef[Right[Term, Type]]] = Nil,
  mthDefs: List[MethodDef[Left[Term, Type]]] = Nil,
) extends Decl

/**
  * Method type can be a definition or a declaration based
  * on the type parameter set. A declaration has `Type` in rhs
  * and definition has `Term` in rhs.
  *
  * @param rec indicates that the method is recursive
  * @param prt name of class to which method belongs
  * @param nme name of method
  * @param tparams list of parameters for the method if any
  * @param rhs term or type if definition and declaration respectively
  */
final case class MethodDef[RHS <: Term \/ Type](
  rec: Bool,
  parent: TypeName,
  nme: Var,
  tparams: List[TypeName],
  rhs: RHS,
) extends Located {
  val body: Located = rhs.fold(identity, identity)
  val children: Ls[Located] = nme :: body :: Nil
}

sealed abstract class TypeDefKind(val str: Str)
sealed trait ObjDefKind
case object Cls extends TypeDefKind("class") with ObjDefKind
case object Trt extends TypeDefKind("trait") with ObjDefKind
case object Als extends TypeDefKind("type alias")

sealed abstract class Term                                           extends Terms with TermImpl
sealed abstract class Lit                                            extends SimpleTerm with LitImpl
final case class Var(name: Str)                                      extends SimpleTerm with VarImpl
final case class Lam(lhs: Term, rhs: Term)                           extends Term
final case class App(lhs: Term, rhs: Term)                           extends Term
final case class Tup(fields: Ls[Opt[Var] -> (Term -> Bool)])         extends Term
final case class Rcd(fields: Ls[Var -> (Term -> Bool)])              extends Term
final case class Sel(receiver: Term, fieldName: Var)                 extends Term
final case class Let(isRec: Bool, name: Var, rhs: Term, body: Term)  extends Term
final case class Blk(stmts: Ls[Statement])                           extends Term with BlkImpl
final case class Bra(rcd: Bool, trm: Term)                           extends Term
final case class Asc(trm: Term, ty: Type)                            extends Term
final case class Bind(lhs: Term, rhs: Term)                          extends Term
final case class Test(trm: Term, ty: Term)                           extends Term
final case class With(trm: Term, fields: Rcd)                        extends Term
final case class CaseOf(trm: Term, cases: CaseBranches)              extends Term
final case class Subs(arr: Term, idx: Term)                          extends Term
final case class Assign(lhs: Term, rhs: Term)                        extends Term

sealed abstract class CaseBranches extends CaseBranchesImpl
final case class Case(pat: SimpleTerm, body: Term, rest: CaseBranches) extends CaseBranches
final case class Wildcard(body: Term) extends CaseBranches
final case object NoCases extends CaseBranches

final case class IntLit(value: BigInt)            extends Lit
final case class DecLit(value: BigDecimal)        extends Lit
final case class StrLit(value: Str)               extends Lit
final case class UnitLit(undefinedOrNull: Bool)   extends Lit

sealed abstract class SimpleTerm extends Term with SimpleTermImpl

sealed trait Statement extends StatementImpl
final case class LetS(isRec: Bool, pat: Term, rhs: Term)  extends Statement
final case class DataDefn(body: Term)                     extends Statement
final case class DatatypeDefn(head: Term, body: Term)     extends Statement

sealed trait DesugaredStatement extends Statement with DesugaredStatementImpl

sealed trait Terms extends DesugaredStatement


// Types

sealed abstract class Type extends TypeImpl

sealed abstract class Composed(val pol: Bool) extends Type with ComposedImpl

final case class Union(lhs: Type, rhs: Type)             extends Composed(true)
final case class Inter(lhs: Type, rhs: Type)             extends Composed(false)
final case class Function(lhs: Type, rhs: Type)          extends Type
final case class Record(fields: Ls[Var -> Field])        extends Type
final case class Tuple(fields: Ls[Opt[Var] -> Field])    extends Type
final case class Recursive(uv: TypeVar, body: Type)      extends Type
final case class AppliedType(base: TypeName, targs: List[Type]) extends Type
final case class Neg(base: Type)                         extends Type
final case class Rem(base: Type, names: Ls[Var])         extends Type
final case class Bounds(lb: Type, ub: Type)              extends Type
final case class WithExtension(base: Type, rcd: Record)  extends Type
final case class Constrained(base: Type, where: Ls[TypeVar -> Bounds]) extends Type

final case class Field(in: Opt[Type], out: Type)         extends FieldImpl

sealed abstract class NullaryType                        extends Type

case object Top                                          extends NullaryType
case object Bot                                          extends NullaryType

/** Literal type type, e.g. type `0` is a type with only one possible value `0`. */
final case class Literal(lit: Lit)                       extends NullaryType

/** Reference to an existing type with the given name. */
final case class TypeName(name: Str)                     extends NullaryType with TypeNameImpl

final case class TypeVar(val identifier: Int \/ Str, nameHint: Opt[Str]) extends NullaryType with TypeVarImpl {
  require(nameHint.isEmpty || identifier.isLeft)
  // ^ The better data structure to represent this would be an EitherOrBoth
  override def toString: Str = identifier.fold("α" + _, identity)
}

final case class PolyType(targs: Ls[TypeName], body: Type) extends PolyTypeImpl

