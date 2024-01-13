package mlscript.ucs.context

import mlscript.{Lit, Loc}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.utils._, shorthands._
import mlscript.pretyper.symbol.DummyClassSymbol

sealed abstract class Pattern {
  override def toString(): String = this match {
    case Pattern.ClassLike(symbol) =>
      val kind = symbol match {
        case _: DummyClassSymbol => "dummy class"
        case _ => symbol.defn.kind.str
      }
      s"$kind `${symbol.name}`"
    case Pattern.Tuple() => "tuple"
    case Pattern.Literal(literal) => s"literal $literal"
  }
}

object Pattern {
  final case class ClassLike(symbol: TypeSymbol) extends Pattern
  // Currently, there is only simple tuple pattern, so we cannot differentiate
  // between tuple patterns of different arity. That's why the parameter list
  // is empty for now.
  final case class Tuple() extends Pattern
  final case class Literal(literal: Lit) extends Pattern
}

/**
  * A `CaseSet` represents all patterns that a particular scrutinee is
  * being matched with within a UCS expression. Each Pattern is associated
  * with the locations where these patterns appear.
  *
  * @param patterns a set of patterns that the scrutinee is matched with.
  */
final case class CaseSet(val cases: Map[Pattern, Ls[Loc]]) {
  /**
    * Split the pattern set into two pattern sets.
    * 
    * For example, let A be the base type of B, C, and D. Plus, class `Z` is
    * unrelated to any of them. Suppose the initial pattern set is
    * `{ A, B, C, Z }`. Splitting the set results in two sets, one set
    * contains classes that are compatible with `A`, and the other set
    * contains classes that are unrelated to `A`.
    * 
    * For example, if we split the set with `A`, then we get `{ B, C }` and
    * set `{ Z }`. Set `{ B, C }` represents that the scrutinee can be further
    * refined to class `B` or `class C`. Set `{ Z }` represents that if the
    * scrutinee is not `A`, then it can be `Z`.
    * 
    * If `A` is sealed to `B`, `C`, and `D`, then we get `{ B, C, D }` and
    * `{ Z }`. Because if the scrutinee is assumed to be `A`, then it can also
    * be `D` other than `B`, `C`.
    *
    * @param classLikeSymbol the type symbol represents the class like type
    * @return If the pattern set doesn't include the given type symbol, this
    *         returns `None`. Otherwise, the function returns a triplet of the
    *         locations where the pattern appears, the related patterns, and
    *         unrelated patterns.
    */
  def split(classLikeSymbol: TypeSymbol): Opt[(Ls[Loc], CaseSet, CaseSet)] = {
    val classLikePattern = Pattern.ClassLike(classLikeSymbol)
    cases.get(classLikePattern).map { locations =>
      val withoutSymbol = cases - classLikePattern
      val relatedPatterns = withoutSymbol.filter {
        case (Pattern.ClassLike(otherSymbol), _) => otherSymbol.baseTypes.contains(classLikeSymbol)
        case ((_: Pattern.Tuple | _: Pattern.Literal), _) => false
      } ++ classLikeSymbol.sealedDerivedTypes.iterator.map { symbol =>
        Pattern.ClassLike(symbol) -> symbol.defn.nme.toLoc.toList
      }
      val unrelatedPatterns = withoutSymbol.filter {
        case (Pattern.ClassLike(otherSymbol), _) => !otherSymbol.baseTypes.contains(classLikeSymbol)
        case ((_: Pattern.Tuple | _: Pattern.Literal), _) => true
      }
      (locations, copy(relatedPatterns), copy(unrelatedPatterns))
    }
  }

  def remove(literal: Lit): CaseSet = {
    val literalPattern = Pattern.Literal(literal)
    copy(cases - literalPattern)
  }

  /** Get an iterator of only patterns. */
  @inline def patterns: Iterator[Pattern] = cases.iterator.map(_._1)

  @inline def isEmpty: Bool = cases.isEmpty

  @inline def size: Int = cases.size
}

object CaseSet {
  def empty: CaseSet = CaseSet(Map.empty)
}
