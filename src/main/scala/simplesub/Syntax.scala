package simplesub

import scala.util.chaining._

object Syntax {
  
  
  // Terms
  
  final case class Pgrm(defs: List[(Boolean, String, Term)])
  
  sealed abstract class Term
  final case class Lit(value: Int)                                          extends Term
  final case class Var(name: String)                                        extends Term
  final case class Lam(name: String, rhs: Term)                             extends Term
  final case class App(lhs: Term, rhs: Term)                                extends Term
  final case class Rcd(fields: List[(String, Term)])                         extends Term
  final case class Sel(receiver: Term, fieldName: String)                    extends Term
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
    override def toString: String = s"$nameHint:$hash@${System.identityHashCode(this).toHexString}"
    override def hashCode: Int = hash
  }
  
  
  // Helper methods for simple types
  
  sealed abstract class TypeImpl { self: Type =>
    
    lazy val freeVars: Set[TypeVar] = this match {
      case uv: TypeVar => Set(uv)
      case Recursive(n, b) => b.freeVars - n
      case _ => children.iterator.flatMap(_.freeVars).toSet
    }
    
    protected def conjuncts: List[PlainType] = this match {
      case Top => Nil
      case Inter(l, r) => l.conjuncts ::: r.conjuncts
      case ty: PlainType => ty :: Nil
      case _ => throw new AssertionError(s"wrong mix of polarities: $this")
    }
    protected def disjuncts: List[PlainType] = this match {
      case Bot => Nil
      case Union(l, r) => l.disjuncts ::: r.disjuncts
      case ty: PlainType => ty :: Nil
      case _ => throw new AssertionError(s"wrong mix of polarities: $this")
    }
    lazy val normalize: Type = {
      def merge(components: List[Type])(pol: Boolean): Type = {
        val atoms = components.collect { case a: Atom => a }
        val funs = components.collect { case Function(l, r) => (l, r) }
        val rcds = components.collect { case Record(fs) => fs }
        val recs = components.collect { case r @ Recursive(_, _) => r }
        val (extr: Type, mrg, grm) = if (pol) (Bot, Union, Inter) else (Top, Inter, Union)
        val fun = funs.reduceOption[(Type, Type)] { case ((l0,r0), (l1,r1)) => (grm(l0,l1), mrg(r0,r1)) }
        val rcd = rcds.reduceOption { (fs0, fs1) =>
          if (pol) {
            val fs1m = fs1.toMap
            fs0.flatMap { case (k, v) => fs1m.get(k).map(k -> mrg(v, _)) }
          } else mergeMaps(fs0.toMap, fs1.toMap)(mrg).toList
        }
        val normalized =
          atoms.distinct.sortBy(_.hash) :::
          fun.map(lr => Function(lr._1.normalize, lr._2.normalize)).toList :::
          rcd.map(fs => Record(fs.map(nt => nt._1 -> nt._2.normalize).sortBy(_._1))).toList :::
          recs.map(r => Recursive(r.uv, r.body.normalize)).sortBy(_.uv.hash)
        normalized.reduceOption(mrg).getOrElse(extr)
      }
      this match {
        case Bot | Union(_, _) => merge(disjuncts)(true)
        case Top | Inter(_, _) => merge(conjuncts)(false)
        case Record(Nil) => Top
        case Record(fs) => Record(fs.map(nt => nt._1 -> nt._2.normalize))
        case Function(l, r) => Function(l.normalize, r.normalize)
        case Recursive(v, b) => Recursive(v, b.normalize)
        case _: NullaryType => this
      }
    }
    
    def show: String = this match {
      case Top => "⊤"
      case Bot => "⊥"
      case Ctor(name) => name
      case uv: TypeVar => uv.nameHint + uv.hash
      case Recursive(n, b) => s"${b.show} as ${n.nameHint+n.hash}"
      case Function(l, r) => s"(${l.show} -> ${r.show})"
      case Record(fs) => fs.map(nt => s"${nt._1}: ${nt._2.show}").mkString("{", ", ", "}")
      case Union(l, r) => s"(${l.show} ∨ ${r.show})"
      case Inter(l, r) => s"(${l.show} ∧ ${r.show})"
    }
    
    def children: List[Type] = this match {
      case _: NullaryType => Nil
      case Function(l, r) => l :: r :: Nil
      case Record(fs) => fs.map(_._2)
      case Union(l, r) => l :: r :: Nil
      case Inter(l, r) => l :: r :: Nil
      case Recursive(n, b) => b :: Nil
    }
    
    def map(f: Type => Type): Type = this match {
      case _: NullaryType => this
      case Function(l, r) => Function(f(l), f(r))
      case Record(fs) => Record(fs.map(nt => nt._1 -> f(nt._2)))
      case Union(l, r) => Union(f(l), f(r))
      case Inter(l, r) => Inter(f(l), f(r))
      case Recursive(n, b) => Recursive(n, f(b))
    }
    
  }
  
  
  // Type-safe normalized polar type representations
  
  object Pos extends Polarity {
    val Negated: Neg.type = Neg
    protected val mergeSymbol = "∨"
    protected val extremumSymbol = "⊥"
    protected def mergeFields(lhs: Map[String, Type], rhs: Map[String, Type]) =
      lhs.flatMap { case (k, v) => rhs.get(k).map(k -> merge(v, _)) }
  }
  
  object Neg extends Polarity {
    val Negated: Pos.type = Pos
    protected val mergeSymbol = "∧"
    protected val extremumSymbol = "⊤"
    protected def mergeFields(lhs: Map[String, Type], rhs: Map[String, Type]) =
      mergeMaps(lhs, rhs)(merge)
  }
  
  sealed abstract class Polarity {
    
    val Negated: Polarity
    
    protected val mergeSymbol: String
    protected val extremumSymbol: String
    protected def mergeFields(lhs: Map[String, Type], rhs: Map[String, Type]): Map[String, Type]
    
    def unary_! : Negated.type = Negated
    val empty: Type = Type(Set.empty, None, None, None)
    
    private lazy val mergeString = " " + mergeSymbol + " "
    
    def merge(lhs: Type, rhs: Type): Type = (lhs.rec, rhs.rec).pipe {
        case (Some(rec0), Some(rec1)) => rhs.substVar(rec1, rec0)
        case _ => rhs
      }.pipe { rhs =>
        val fields = mergeOptions(lhs.fields, rhs.fields)(mergeFields)
        val fun = mergeOptions(lhs.fun, rhs.fun){
          case ((l0,r0), (l1,r1)) => (Negated.merge(l0, l1), merge(r0, r1)) }
        val newRec = lhs.rec orElse rhs.rec
        val newAtoms = (lhs.atoms ++ rhs.atoms).filterNot(newRec.contains[Atom]) // comply with invariant
        Type(newAtoms, fields, fun, newRec)
      }
    
    case class Type(
        atoms: Set[Atom],
        fields: Option[Map[String, Type]],
        fun: Option[(Negated.Type, Type)],
        rec: Option[TypeVar],
    ) {
      require(rec.forall(r => !atoms(r)), rec -> atoms)
      
      def substVar(uv0: TypeVar, uv1: TypeVar): Type = {
        val newRec = if (rec.contains(uv0)) Some(uv1) else rec
        Type(
          atoms.map(v => if (v eq uv0) uv1 else v)
            .filterNot(newRec.contains[Atom]), // to comply with the invariant
          fields.map(_.view.mapValues(_.substVar(uv0, uv1)).toMap),
          fun.map { case (l, r) => (l.substVar(uv0, uv1), r.substVar(uv0, uv1)) },
          newRec
        )
      }
      
      lazy val freeVariables: Set[TypeVar] =
        atoms.collect { case uv: TypeVar => uv } ++
          fields.iterator.flatMap(_.valuesIterator.flatMap(_.freeVariables)) ++ 
          fun.iterator.flatMap(lr => lr._1.freeVariables ++ lr._2.freeVariables) -- rec.toList
      
      private def sortedFields = fields.toList.flatMap(_.toList).sortBy(_._1)
      
      def variableOccurrences: List[(Boolean, TypeVar)] =
        rec.toList.map(true -> _) ++
          atoms.iterator.collect { case uv: TypeVar => (false, uv) }.toList.sortBy(_._2.hash) ++
          sortedFields.flatMap(_._2.variableOccurrences) ++ 
          fun.iterator.flatMap(lr => lr._1.variableOccurrences ++ lr._2.variableOccurrences)
        
      def showIn(ctx: Map[TypeVar, String], outerPrec: Int): String = {
        val firstComponents =
          (if (fields.forall(_.isEmpty)) Nil
           else sortedFields.iterator.map(nt => s"${nt._1}: ${nt._2.showIn(ctx, 0)}")
                  .mkStringOr(", ", "{", "}") :: Nil
          ) ++ atoms.toList.sortBy(_.hash).map {
                case uv: TypeVar => ctx(uv)
                case Ctor(name) => name }
        val funStr = fun.map { lr =>
          val str = lr._1.showIn(ctx, 2) + " -> " + lr._2.showIn(ctx, 1)
          if (firstComponents.nonEmpty) "(" + str + ")" else str }
        val components = firstComponents ++ funStr
        val body = components.mkStringOr(mergeString,
          els = if (fields.isEmpty) extremumSymbol else Negated.extremumSymbol)
        val innerPrec = if (fun.nonEmpty) 1 else 2
        val realOuterPrec = if (rec.nonEmpty) if (fun.nonEmpty) 3 else 0 else outerPrec
        val needsParens = innerPrec < realOuterPrec
        val withParens = if (needsParens) s"(${body})" else body
        rec.fold(withParens)(r => withParens + " as " + ctx(r))
      }
      
      def show: String = {
        val vars = variableOccurrences.distinctBy(_._2)
        val ctx = vars.zipWithIndex.map {
          case ((bound, tv), idx) =>
            def nme = {
              assert(idx <= 'z' - 'a', "TODO handle case of not enough chars")
              ('a' + idx).toChar.toString
            }
            tv -> ((if (bound) "" else "'")+nme)
        }.toMap
        showIn(ctx, 0)
      }
      
    }
    
  }
  
  
}
