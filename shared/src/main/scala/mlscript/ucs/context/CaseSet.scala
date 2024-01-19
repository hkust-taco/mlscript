package mlscript.ucs.context

import mlscript.{Lit, Loc, Var}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.utils._, shorthands._
import mlscript.pretyper.symbol.DummyClassSymbol

/**
  * A `CaseSet` represents all patterns that a particular scrutinee is
  * being matched with within a UCS expression.
  *
  * @param patterns a list of patterns.
  */
final case class CaseSet(val patterns: List[Pattern]) {
  def showInDiagnostics: Str =
    patterns.iterator.map(_.showInDiagnostics).mkString("[", ", ", "]")

  /** Get a iterator of all class-like patterns. */
  def classLikePatterns: Iterator[Pattern.ClassLike] = patterns.iterator.flatMap {
    case pattern: Pattern.ClassLike => S(pattern)
    case _: Pattern.Boolean | _: Pattern.Literal | _: Pattern.Tuple => N
  }

  /** Separate a class-like pattern if it appears in `patterns`. */
  def separate(classLikeSymbol: TypeSymbol): Opt[(Pattern.ClassLike, Ls[Pattern.ClassLike])] = {
    classLikePatterns.foldRight[(Opt[Pattern.ClassLike], Ls[Pattern.ClassLike])]((N, Nil)) {
      case (pattern, (S(separated), rest)) => (S(separated), pattern :: rest)
      case (pattern, (N, rest)) if pattern.classLikeSymbol === classLikeSymbol => (S(pattern), rest)
      case (pattern, (N, rest)) => (N, pattern :: rest)
    } match {
      case (N, _) => N
      case (S(separated), rest) => S((separated, rest))
    }
  }
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
  def split(classLikeSymbol: TypeSymbol): Opt[(Pattern.ClassLike, CaseSet, CaseSet)] = {
    separate(classLikeSymbol) match {
      case N => N
      case S((pattern, patterns)) =>
        val (unrelated, related) = patterns.partitionMap { pattern =>
          if (pattern.classLikeSymbol hasBaseClass classLikeSymbol) {
            R(pattern)
          } else {
            L(pattern)
          }
        }
        S((pattern, CaseSet(related), CaseSet(unrelated)))
    }
  }

  @inline def remove(boolLit: Var): CaseSet = {
    require(boolLit.name === "true" || boolLit.name === "false")
    CaseSet(patterns.filter(!_.matches(boolLit)))
  }

  @inline def remove(literal: Lit): CaseSet =
    CaseSet(patterns.filter(!_.matches(literal)))

  @inline def isEmpty: Bool = patterns.isEmpty

  @inline def size: Int = patterns.size
}
