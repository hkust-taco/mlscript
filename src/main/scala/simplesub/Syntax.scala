package simplesub


// Terms

final case class Pgrm(defs: List[(Boolean, String, Term)])

sealed abstract class Term
final case class Lit(value: Int)                                          extends Term
final case class Var(name: String)                                        extends Term
final case class Lam(name: String, rhs: Term)                             extends Term
final case class App(lhs: Term, rhs: Term)                                extends Term
final case class Rcd(fields: List[(String, Term)])                        extends Term
final case class Sel(receiver: Term, fieldName: String)                   extends Term
final case class Let(isRec: Boolean, name: String, rhs: Term, body: Term) extends Term


/*

  In this file, I present two approaches to representing inferred MLsub types:
    
    - The simple approach, named Type, using a basic (multi-level) ADT. After inference, these
      types need to be normalized using the .normalized method.
    
    - An advanced approach, named Pos.Type, which represents types in normalized form and enforces
      the distinction between positive and negative types using the type system, therefore making
      illegal states unrepresentable.
      This data type currently has better pretty printing, and is used by default.
  
*/


// Simple types

sealed abstract class Type extends TypeImpl
sealed abstract class NullaryType extends Type
sealed trait PlainType extends Type

case object Top extends NullaryType
case object Bot extends NullaryType

final case class Union(lhs: Type, rhs: Type)         extends Type
final case class Inter(lhs: Type, rhs: Type)         extends Type
final case class Function(lhs: Type, rhs: Type)      extends PlainType
final case class Record(fields: List[(String, Type)]) extends PlainType
final case class Recursive(uv: TypeVar, body: Type)  extends PlainType

sealed abstract class Atom extends NullaryType with PlainType {
  def hash: Int
}
final case class Ctor(name: String) extends Atom {
  def hash = name.hashCode
}
final class TypeVar(val nameHint: String, val hash: Int) extends Atom {
  override def toString: String = s"$nameHint:$hash"
  override def hashCode: Int = hash
}
object TypeVar {
  implicit val TypeVarOrdering: Ordering[TypeVar] = Ordering.by(_.hash)
}


// Type-safe normalized polar type representations

case object Pos extends Polarity {
  def asBoolean = true
  val Negated: Neg.type = Neg
  val mergeSymbol = "∨"
  val extremumSymbol = "⊥"
  def mergeFields(lhs: Map[String, Type], rhs: Map[String, Type]) =
    lhs.flatMap { case (k, v) => rhs.get(k).map(k -> merge(v, _)) }
}

case object Neg extends Polarity {
  def asBoolean = false
  val Negated: Pos.type = Pos
  val mergeSymbol = "∧"
  val extremumSymbol = "⊤"
  def mergeFields(lhs: Map[String, Type], rhs: Map[String, Type]) =
    mergeMaps(lhs, rhs)(merge)
}

sealed abstract class Polarity extends PolarityImpl { pol =>
  def asBoolean: Boolean
  
  val Negated: Polarity
  
  val mergeSymbol: String
  val extremumSymbol: String
  def mergeFields(lhs: Map[String, Type], rhs: Map[String, Type]): Map[String, Type]
  
  def unary_! : Negated.type = Negated
  val empty: Type = Type(Set.empty, None, None, None)
  
  case class Type(
      atoms: Set[Atom],
      fields: Option[Map[String, Type]],
      fun: Option[(Negated.Type, Type)],
      rec: Option[TypeVar],
  ) extends TypeImpl {
    require(rec.forall(r => !atoms(r)), rec -> atoms)
  }
  
}
object Polarity {
  implicit val PolarityOrdering: Ordering[Polarity] = Ordering.by(_.asBoolean)
}
