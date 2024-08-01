package mlscript

import mlscript.utils._, shorthands._


// Terms

final case class Pgrm(tops: Ls[Statement]) extends PgrmImpl

sealed abstract class Decl extends DesugaredStatement with DeclImpl
final case class Def(rec: Bool, nme: Var, rhs: Term \/ Type, isByname: Bool) extends Decl with Terms {
  val body: Located = rhs.fold(identity, identity)
}

final case class AdtInfo(ctorName: TypeName)

final case class TypeDef(
  kind: TypeDefKind,
  nme: TypeName,
  tparams: List[TypeName],
  body: Type,
  mthDecls: List[MethodDef[Right[Term, Type]]],
  mthDefs: List[MethodDef[Left[Term, Type]]],
  positionals: Ls[Var],
  adtInfo: Opt[AdtInfo],
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

sealed trait NameRef extends Located { val name: Str; def toVar: Var }

sealed abstract class OuterKind(val str: Str)
case object Block extends OuterKind("block")
sealed abstract class DeclKind(str: Str) extends OuterKind(str)
case object Val extends DeclKind("value")
sealed abstract class TypeDefKind(str: Str) extends DeclKind(str)
sealed trait ObjDefKind
sealed trait ClsLikeKind extends ObjDefKind
case object Cls extends TypeDefKind("class") with ClsLikeKind
case object Trt extends TypeDefKind("trait") with ObjDefKind
case object Mxn extends TypeDefKind("mixin")
case object Als extends TypeDefKind("type alias")
case object Mod extends TypeDefKind("module") with ClsLikeKind

sealed abstract class Term                                           extends Terms with TermImpl
sealed abstract class Lit                                            extends SimpleTerm with LitImpl
final case class Var(name: Str)                                      extends SimpleTerm with VarImpl with NameRef
final case class Lam(lhs: Term, rhs: Term)                           extends Term
final case class App(lhs: Term, rhs: Term)                           extends Term
final case class Tup(fields: Ls[Opt[Var] -> Fld])                    extends Term with TupImpl
final case class Rcd(fields: Ls[Var -> Fld])                         extends Term
final case class Sel(receiver: Term, fieldName: Var)                 extends Term
final case class Let(isRec: Bool, name: Var, rhs: Term, body: Term)  extends Term
final case class Blk(stmts: Ls[Statement])                           extends Term with BlkImpl with Outer
final case class Bra(rcd: Bool, trm: Term)                           extends Term
final case class Asc(trm: Term, ty: Type)                            extends Term
final case class Bind(lhs: Term, rhs: Term)                          extends Term
final case class Test(trm: Term, ty: Term)                           extends Term
final case class With(trm: Term, fields: Rcd)                        extends Term
final case class CaseOf(trm: Term, cases: CaseBranches)              extends Term with CaseOfImpl
final case class Subs(arr: Term, idx: Term)                          extends Term
final case class Assign(lhs: Term, rhs: Term)                        extends Term
final case class Splc(fields: Ls[Either[Term, Fld]])                 extends Term
final case class New(head: Opt[(NamedType, Term)], body: TypingUnit) extends Term // `new C(...)` or `new C(){...}` or `new{...}`
final case class NuNew(cls: Term) extends Term
final case class If(body: IfBody, els: Opt[Term])                    extends Term
final case class TyApp(lhs: Term, targs: Ls[Type])                   extends Term
final case class Where(body: Term, where: Ls[Statement])             extends Term
final case class Forall(params: Ls[TypeVar], body: Term)             extends Term
final case class Inst(body: Term)                                    extends Term // Explicit instantiation of polymohic term
final case class Super()                                             extends Term
final case class Eqn(lhs: Var, rhs: Term)                            extends Term // equations such as x = y, notably used in constructors; TODO: make lhs a Term
final case class Quoted(body: Term)                                  extends Term 
final case class Unquoted(body: Term)                                extends Term 
final case class Rft(base: Term, decls: TypingUnit)                  extends Term
final case class While(cond: Term, body: Term)                       extends Term
final case class Ann(ann: Term, receiver: Term)                      extends Term

final case class AdtMatchWith(cond: Term, arms: Ls[AdtMatchPat])     extends Term
final case class AdtMatchPat(pat: Term, rhs: Term)                   extends AdtMatchPatImpl

sealed abstract class IfBody extends IfBodyImpl
final case class IfThen(expr: Term, rhs: Term) extends IfBody
final case class IfElse(expr: Term) extends IfBody
final case class IfLet(isRec: Bool, name: Var, rhs: Term, body: IfBody) extends IfBody
final case class IfOpApp(lhs: Term, op: Var, rhs: IfBody) extends IfBody
final case class IfOpsApp(lhs: Term, opsRhss: Ls[Var -> IfBody]) extends IfBody
final case class IfBlock(lines: Ls[IfBody \/ Statement]) extends IfBody
// final case class IfApp(fun: Term, opsRhss: Ls[Var -> IfBody]) extends IfBody

final case class FldFlags(mut: Bool, spec: Bool, genGetter: Bool) extends FldFlagsImpl // TODO make it a Located and use in diagnostics
final case class Fld(flags: FldFlags, value: Term) extends FldImpl

object FldFlags { val empty: FldFlags = FldFlags(false, false, false) }

sealed abstract class CaseBranches extends CaseBranchesImpl
final case class Case(pat: SimpleTerm, body: Term, rest: CaseBranches)(val refined: Bool) extends CaseBranches
final case class Wildcard(body: Term) extends CaseBranches
// final case class TupleCase(numElems: Int, canHaveMore: Bool, body: Term, rest: CaseBranches) extends CaseBranches
final case object NoCases extends CaseBranches

final case class IntLit(value: BigInt)            extends Lit
final case class DecLit(value: BigDecimal)        extends Lit
final case class StrLit(value: Str)               extends Lit
final case class UnitLit(undefinedOrNull: Bool)   extends Lit

trait IdentifiedTerm

sealed abstract class SimpleTerm extends Term with IdentifiedTerm with SimpleTermImpl

sealed trait Statement extends StatementImpl
final case class LetS(isRec: Bool, pat: Term, rhs: Term) extends Statement
final case class DataDefn(body: Term)                    extends Statement
final case class DatatypeDefn(head: Term, body: Term)    extends Statement

sealed trait DesugaredStatement extends Statement with DesugaredStatementImpl

sealed trait Terms extends DesugaredStatement


// Types

sealed abstract class TypeLike extends TypeLikeImpl

sealed abstract class Type extends TypeLike with TypeImpl

sealed trait NamedType extends Type { def base: TypeName; def targs: Ls[Type] }

sealed abstract class Composed(val pol: Bool) extends Type with ComposedImpl

final case class Union(lhs: Type, rhs: Type)             extends Composed(true)
final case class Inter(lhs: Type, rhs: Type)             extends Composed(false)
final case class Function(lhs: Type, rhs: Type)          extends Type
final case class Record(fields: Ls[Var -> Field])        extends Type
final case class Tuple(fields: Ls[Opt[Var] -> Field])    extends Type
final case class Recursive(uv: TypeVar, body: Type)      extends Type
final case class AppliedType(base: TypeName, targs: List[Type]) extends Type with NamedType
final case class Selection(base: Type, name: TypeName)   extends Type
final case class Neg(base: Type)                         extends Type
final case class Rem(base: Type, names: Ls[Var])         extends Type
final case class Bounds(lb: Type, ub: Type)              extends Type
final case class WithExtension(base: Type, rcd: Record)  extends Type
final case class Splice(fields: Ls[Either[Type, Field]]) extends Type
final case class Constrained(base: TypeLike, tvBounds: Ls[TypeVar -> Bounds], where: Ls[Bounds], tscs: Ls[Ls[(Bool, Type)] -> Ls[Ls[Type]]]) extends Type
// final case class FirstClassDefn(defn: NuTypeDef)         extends Type // TODO
// final case class Refinement(base: Type, decls: TypingUnit) extends Type // TODO

final case class Field(in: Opt[Type], out: Type)         extends FieldImpl

sealed abstract class NullaryType                        extends Type

case object Top                                          extends NullaryType
case object Bot                                          extends NullaryType

/** Literal type type, e.g. type `0` is a type with only one possible value `0`. */
final case class Literal(lit: Lit)                       extends NullaryType

/** Reference to an existing type with the given name. */
final case class TypeName(name: Str)                     extends NullaryType with NamedType with TypeNameImpl with NameRef
final case class TypeTag (name: Str)                     extends NullaryType

final case class TypeVar(val identifier: Int \/ Str, nameHint: Opt[Str]) extends NullaryType with TypeVarImpl {
  require(nameHint.isEmpty || identifier.isLeft)
  // ^ The better data structure to represent this would be an EitherOrBoth
  override def toString: Str = identifier.fold("α" + _, identity)
}

final case class PolyType(targs: Ls[TypeName \/ TypeVar], body: Type) extends Type with PolyTypeImpl


// New Definitions AST

final case class TypingUnit(rawEntities: Ls[Statement]) extends TypingUnitImpl
// final case class TypingUnit(entities: Ls[Statement]) extends TypeLike with PgrmOrTypingUnit with TypingUnitImpl

final case class Signature(members: Ls[NuDecl], result: Opt[Type]) extends TypeLike with SignatureImpl

sealed abstract class NuDecl extends TypeLike with Statement with NuDeclImpl

sealed trait Outer { def kind: OuterKind }

final case class NuTypeDef(
  kind: TypeDefKind,
  nme: TypeName,
  tparams: Ls[(Opt[VarianceInfo], TypeName)],
  params: Opt[Tup], // the specialized parameters for that type
  ctor: Opt[Constructor],
  sig: Opt[Type],
  parents: Ls[Term],
  superAnnot: Opt[Type],
  thisAnnot: Opt[Type],
  body: TypingUnit
)(val declareLoc: Opt[Loc], val abstractLoc: Opt[Loc], val annotations: Ls[Term])
  extends NuDecl with Statement with Outer {
    def isPlainJSClass: Bool = params.isEmpty
  }

final case class NuFunDef(
  isLetRec: Opt[Bool], // None means it's a `fun`, which is always recursive; Some means it's a `let`/`let rec` or `val`
  nme: Var,
  symbolicNme: Opt[Var],
  tparams: Ls[TypeName],
  rhs: Term \/ Type,
)(
  val declareLoc: Opt[Loc],
  val virtualLoc: Opt[Loc], // Some(Loc) means that the function is modified by keyword `virtual`
  val mutLoc: Opt[Loc],
  val signature: Opt[NuFunDef],
  val outer: Opt[Outer],
  val genField: Bool, // true means it's a `val`; false means it's a `let`
  val annotations: Ls[Term],
) extends NuDecl with DesugaredStatement {
  val body: Located = rhs.fold(identity, identity)
  def kind: DeclKind = Val
  val abstractLoc: Opt[Loc] = None
  
  def isLetOrLetRec: Bool = isLetRec.isDefined && !genField
  
  // If the member has no implementation, it is virtual automatically
  def isVirtual: Bool = virtualLoc.nonEmpty || rhs.isRight
  
  def isMut: Bool = mutLoc.nonEmpty
  
  def isGeneralized: Bool = isLetRec.isEmpty || (rhs match {
    case Left(value) => value.isGeneralizableLam
    case Right(ty) => false
  })
}

final case class Constructor(params: Tup, body: Blk) extends DesugaredStatement with ConstructorImpl // constructor(...) { ... }



final case class VarianceInfo(isCovariant: Bool, isContravariant: Bool) {
  
  /** Combine two pieces of variance information together
   */
  def &&(that: VarianceInfo): VarianceInfo =
    VarianceInfo(isCovariant && that.isCovariant, isContravariant && that.isContravariant)
  
  /*  Flip the current variance if it encounters a contravariant position
    */
  def flip: VarianceInfo = VarianceInfo(isContravariant, isCovariant)
  
  override def toString: Str = show
  
  def show: Str = this match {
    case (VarianceInfo(true, true)) => "±"
    case (VarianceInfo(false, true)) => "-"
    case (VarianceInfo(true, false)) => "+"
    case (VarianceInfo(false, false)) => "="
  }
}

object VarianceInfo {
  val bi: VarianceInfo = VarianceInfo(true, true)
  val co: VarianceInfo = VarianceInfo(true, false)
  val contra: VarianceInfo = VarianceInfo(false, true)
  val in: VarianceInfo = VarianceInfo(false, false)
}

