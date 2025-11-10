package hkmc2
package semantics
package ups


import mlscript.utils.*, shorthands.*
import semantics.Pattern as SP
import syntax.{Tree, SpreadKind}, Tree.{Ident, StrLit}
import Message.MessageContext
import ucs.{error, warn}
import Context.*
import hkmc2.semantics.ups.Pattern.NonCompositional
import scala.collection.immutable.SeqMap

private[ups] object Kind:
  sealed trait Specialized extends Expanded
  sealed trait Expanded extends Complete
  sealed trait Complete

/** This class `Pattern` with its case classes are the internal representation
  * of patterns used in pattern compilation. The most important difference
  * between these and those in the `semantics` package are as follows.
  * 
  * 1. All symbols in this abstract data type are resolved, including bindings
  *    used in pattern transformations. Ill-formed bindings have been rejected
  *    during the elaboration stage.
  * 2. Higher-order patterns have been instantiated. Diverging patterns have
  *    been rejected during instantiation. Therefore, all symbols in this abstract
  *    data type are guaranteed to be first-order.
  */
sealed abstract class Pattern[+K <: Kind.Complete] extends AutoLocated:
  import Pattern.*
  
  infix def and[L >: K <: Kind.Complete](that: Pattern[L]): Pattern[L] = this match
    case And(patterns) => that match
      case And(patterns2) => And(patterns ++ patterns2)
      case _ => And[L](patterns appended that)
    case _ => that match
      case And(patterns) => And(this :: patterns)
      case _ => And[L](this :: that :: Nil)
  
  infix def or[L >: K <: Kind.Complete](that: Pattern[L]): Pattern[L] = this match
    case Or(patterns) => that match
      case Or(patterns2) => Or(patterns ++ patterns2)
      case _ => Or[L](patterns appended that)
    case _ => that match
      case Or(patterns) => Or[L](this :: patterns)
      case _ => Or[L](this :: that :: Nil)
  
  // TODO: Associate with locations.
  protected def children: List[Located] = this match
    case Literal(lit) => lit :: Nil
    case ClassLike(sym, arguments) => arguments.fold(Nil):
      _.map((id, p) => p).toList
    case Record(entries) => entries.values.toList
    case Tuple(leading, spread) => leading ::: spread.fold(Nil):
      case (_, middle, trailing) => middle :: trailing
    case And(patterns) => patterns
    case Or(patterns) => patterns
    case Not(pattern) => pattern :: Nil
    case Rename(pattern, name) => pattern :: Nil
    case Extract(pattern, _, term) => pattern :: term :: Nil
    case Synonym(pattern) => pattern.symbol :: pattern.arguments
  
  lazy val symbols: Ls[VarSymbol] = this match
    case Literal(lit) => Nil
    case ClassLike(sym, arguments) =>
      arguments.fold(Nil)(_.values.flatMap(_.symbols).toList)
    case Record(entries) => entries.values.flatMap(_.symbols).toList
    case Tuple(leading, spread) => leading.flatMap(_.symbols) ::: spread.fold(Nil):
      case (_, middle, trailing) => middle.symbols ::: trailing.flatMap(_.symbols)
    case Synonym(_) => Nil
    case And(patterns) => patterns.flatMap(_.symbols)
    case Or(patterns) =>
      // We have checked that bindings are consistent in the elaboration stage.
      // Inconsistent bindings are not associated with symbols.
      patterns.find(_ != Never).fold(Nil)(_.symbols)
    case Not(_) => Nil
    case Rename(pattern, name) => name :: pattern.symbols
    case Extract(_, _, _) => Nil
  
  /** Apply a partial function to every node in the pattern tree. Replace each
   *  node with the result of the partial function. If the partial function is
   *  not defined at a node, the node is left unchanged.
   *  @param f The partial function to apply to each node.
   */
  def map[L <: Kind.Complete](f: NonCompositional[K] => Pattern[L]): Pattern[L] = this match
    case p: NonCompositional[K] => f(p)
    case And(patterns) => And[L](patterns.map(_.map(f)))
    case Or(patterns) => Or[L](patterns.map(_.map(f)))
    case Not(pattern) => Not[L](pattern.map(f))
    case Rename(pattern, name) => Rename[L](pattern.map(f), name)
    case Extract(pattern, correspondence, term) =>
      Extract[L](pattern.map(f), correspondence, term)
  
  /** A simplified reduce for ``Pattern``.
    * It is designed to be used when we want to
    * compute a single value, starting from the leaves.
    * It silently goes through ``Not``, ``Extract``, ``Rename`` and ``Synonym``.
    * The function must provide all the other base cases, and how
    * a list is merged (for ``And`` and ``Or`` nodes)
    */
  def reduce[A](merge: List[A] => A)(f: PartialFunction[Pattern[K], A]): A = this match
    case p: NonCompositional[K] =>
      if f.isDefinedAt(p) then f(p) else merge(Nil)
    case And(patterns) => merge(patterns.map(_.reduce(merge)(f)))
    case Or(patterns) => merge(patterns.map(_.reduce(merge)(f)))
    case Not(pattern) => pattern.reduce(merge)(f)
    case Rename(pattern, _) => pattern.reduce(merge)(f)
    case Extract(pattern, _, _) => pattern.reduce(merge)(f)

  def heads: Set[Head] = reduce[Set[Head]](_.toSet.flatten):
    case Literal(lit) => Set(lit)
    case ClassLike(sym, _) => Set(sym)

  def fields: Set[Ident | Int] = reduce[Set[Ident | Int]](_.toSet.flatten):
    case Record(entries) => entries.keys.toSet
    case Tuple(leading, spread) =>
      val n = leading.size + spread.fold(0)(_._3.size)
      val subfields = Range(0, n).toSet[Ident | Int]
      // if this is strict, then a condition is imposed on field n
      if spread.isEmpty then subfields + n else subfields

  def collectSubPatterns(field: Ident | Int): Set[Pat] = field match
    case id: Ident => this.reduce[Set[Pat]](_.toSet.flatten):
        // TODO: raise a warning
      case ClassLike(sym, arguments) => /* TODO:raise a warning */ arguments match
        case None => Set()
        case Some(arguments) =>
          arguments.find((id1, _) => id === id).map((_, p) => p).toSet
      case Record(entries) => entries.get(id).toSet
      case Tuple(leading, spread) => Set()
    case n: Int => this.reduce[Set[Pat]](_.toSet.flatten):
      case Tuple(leading, S(_, _, trailing)) => trailing.lift(n).toSet
  
  /** Simplify the pattern by removing `Never` patterns. */
  def simplify: Pattern[K] = this match
    case _: Literal => this
    case ClassLike(sym, arguments) =>
      ClassLike(sym, arguments.map(_.map((id, p) => (id, p.simplify))))
    case Record(entries) =>
      val simplify = entries.map((id, p) => (id, p.simplify))
      if simplify.exists((_, p) => p === Never) then Never else Record(simplify)
    case Tuple(leading, N) =>
      val simplified = leading.map(_.simplify)
      if simplified contains Never then Never else Tuple(simplified, N)
    case Tuple(leading, S((spreadKind, middle, trailing))) =>
      val leading2 = leading.map(_.simplify)
      val middle2 = middle.simplify
      val trailing2 = trailing.map(_.simplify)
      if leading2.contains(Never) || middle2 === Never ||
        trailing2.contains(Never) then Never
      else Tuple(leading2, S((spreadKind, middle2, trailing2)))
    case And(patterns) =>
      // TODO: Complete the simplification logic here.
      val simplified = patterns.foldRight(Nil: Ls[Pattern[K]]):
        case (p, acc) => p.simplify match
          case `Wildcard` => acc match
            case `Wildcard` :: _ => acc // One consecutive wildcard is enough.
            case acc => Wildcard :: acc
          case simplified => simplified :: acc
      if simplified contains Never then Never else simplified.foldSingleton(And.apply)(identity)
    case Or(patterns) =>
      patterns.foldRight(Nil: Ls[Pattern[K]]):
        case (p, acc) => p.simplify match
          case Never => acc match
            // The list should be a list of non-`Never` patterns or a singleton
            // list of `Never` pattern.
            case Nil => Never :: Nil
            case Never :: Nil | _ => acc
          // Should we discard the accumulated patterns?
          // case `Wildcard` => Wildcard :: Nil // Discard the following patterns.
          case `Wildcard` => acc match
            case `Never` :: Nil => Wildcard :: Nil
            case `Wildcard` :: _ => acc // One consecutive wildcard is enough.
            case acc => Wildcard :: acc
          case pat => acc match
            case Nil | Never :: Nil => pat :: Nil
            case _ => pat :: acc
      .foldSingleton(Or.apply)(identity)
    case Not(pattern) => Not(pattern.simplify)
    case Rename(pattern, name) => Rename(pattern.simplify, name)
    case Extract(pattern, correspondence, term) => pattern.simplify match
      case `Never` => Never // Lift up `Never`. Let the caller reduce it.
      case simplified => Extract(simplified, correspondence, term)
    case Synonym(sym) => this
  
  /** Expand the pattern by replacing any top-level synonym with its body.
   *  @return the expanded pattern named "ExPat" in the paper. */
  def expand(alreadyExpanded: Set[Instantiation])(using Context, Raise): ExPat = map:
    case Synonym(instantiation) =>
      if alreadyExpanded contains instantiation then
        error(msg"Expanding this pattern leads to an infinite loop." -> instantiation.toLoc)
        Never // Infinite recursive patterns are considered as never patterns.
      else
        // Otherwise, we expand the instantiated pattern definition's body.
        instantiation.body.expand(alreadyExpanded + instantiation)
    // I don't know how to make the GADT type checking work here.
    // case pattern: NonCompositional[K] => pattern // Noop.
    // case pattern: ExPat => pattern // Noop.
    case pattern: ClassLike => pattern
    case pattern: Record => pattern
    case pattern: Tuple => pattern
    case pattern: Literal => pattern
  
  /** Unwrap `Rename` patterns until we reach a non-`Rename` pattern. Collect
   *  the symbols on the way. Maybe we can make `Rename` a property of each
   *  pattern. */
  def aliases: Ls[VarSymbol] = this match
    case Rename(pattern, name) => name :: pattern.aliases
    case _: Pattern[K] => Nil
  
  def showDbg: Str = this match
    case Literal(lit) => lit.idStr
    case ClassLike(sym, arguments) =>
      val argumentsText = arguments.fold(""):
        _.iterator.map((id, p) => s"${id.name}: ${p.showDbg}").mkString(" { ", ", ", " }")
      s"${sym.nme}$argumentsText"
    case Record(entries) =>
      if entries.isEmpty then "{}" else entries.iterator.map:
        case (id, p) => s"${id.name}: ${p.showDbg}"
      .mkString("{ ", ", ", " }")
    case Tuple(leading, N) =>
      leading.iterator.map(_.showDbg).mkString("[", ", ", "]")
    case Tuple(leading, S(spreadKind, spread, trailing)) =>
      val leadingItems = leading.iterator.map(_.showDbg)
      val spreadItem = Iterator.single(spreadKind.str + spread.showDbg)
      val trailingItems = trailing.iterator.map(_.showDbg)
      (leadingItems ++ spreadItem ++ trailingItems).mkString("[", ", ", "]")
    case And(Nil) => "⊤"
    case And(pattern :: Nil) => pattern.showDbg
    case And(patterns) =>
      patterns.map(_.showDbg).mkString("(", " ∧ ", ")")
    case Or(Nil) => "⊥"
    case Or(pattern :: Nil) => pattern.showDbg
    case Or(patterns) =>
      patterns.map(_.showDbg).mkString("(", " ∨ ", ")")
    case Not(pattern) => s"!${pattern.showDbg}"
    case Rename(Or(Nil), name) => name.name
    case Rename(pattern, name) => s"${pattern.showDbg} as $name"
    case Extract(pattern, _, term) => s"${pattern.showDbg} => ${term.showDbg}"
    case Synonym(sym) => sym.showDbg

object Pattern:
  sealed trait NonCompositional[+K <: Kind.Complete] extends Pattern[K]
  
  final case class Literal(lit: syntax.Literal) extends NonCompositional[Kind.Expanded]

  /** Represents a constructor or a class, possibly with arguments.
    * @param sym the class symbol corresponding to the class or the constructor
    * @param arguments is None if no arguments were provided (as
    * in ``Foo``, and is Some if there were arguments provided, even if
    *  it is an empty argument list, e.g. ``Bar()``)
    *
    * the list contains the patterns in the order with which they were given
    * along with the corresponding identifier, even if it was not present before.
    * e.g. if we have a class defintion ``class L = Nil | Cons(hd: Int, tl: L)``
    * then the pattern ``Cons(foo, bar)`` is expected to be
    * ``ClassLike(sym=Cons, arguments=Some(List((hd, foo), tl, bar)))``
    */
  final case class ClassLike(
      sym: ClassLikeSymbol,
      arguments: Opt[SeqMap[Ident, Pat]]
  ) extends NonCompositional[Kind.Expanded]

  final case class Record(
      entries: SeqMap[Ident, Pat]
  ) extends NonCompositional[Kind.Specialized]

  /** @param entries is the ordered list of patterns, from left to right
    * @param strict is true if we matchexactly these fields, and no more,
    * it is false, if we are allowed to have more fields.
    *
    * Tuple([p0, ..., p(n-1)], true) <~> {0:p0, ..., n-1: p(n-1)} & Not({n:_})
    * Tuple([p0, ..., p(n-1)], false) <~> {0:p0, ..., n-1: p(n-1)}
    */
  final case class Tuple(
      leading: List[Pat],
      spread: Opt[(SpreadKind, Pat, List[Pat])],
  ) extends NonCompositional[Kind.Specialized]
  
  /** Represents a pattern synonym.
    * @param sym the pattern symbol corresponding
    */
  final case class Synonym(pattern: Instantiation) extends NonCompositional[Kind.Complete]
  
  // * Pattern kinds propagate through the following cases.
  final case class And[+K <: Kind.Complete](patterns: List[Pattern[K]]) extends Pattern[K]
  final case class Or[+K <: Kind.Complete](patterns: List[Pattern[K]]) extends Pattern[K]
  final case class Not[+K <: Kind.Complete](pattern: Pattern[K]) extends Pattern[K]
  final case class Rename[+K <: Kind.Complete](pattern: Pattern[K], name: VarSymbol) extends Pattern[K]
  /**
    * Similar to `Pattern.Transform`.
    *
    * @param pattern The pattern to be matched against.
    * @param correspondence The correspondence between symbols in the pattern
    *        and symbols in the transformation term.
    * @param term The term to be applied to the extracted values.
    */
  final case class Extract[+K <: Kind.Complete](
      pattern: Pattern[K],
      correspondence: Map[VarSymbol, VarSymbol],
      term: Term
  ) extends Pattern[K]
  
  val Wildcard = Or(Nil)
  
  val Never = And(Nil)
  
  type Head = syntax.Literal | ClassLikeSymbol
  
  /** A representation of fully instantiated first-order patterns. */
  final case class Instantiation(
      symbol: PatternSymbol,
      arguments: Ls[Pat]
  )(val toLoc: Opt[Loc]) extends Located:
    def showDbg: Str =
      val argumentsText = if arguments.isEmpty then "" else
        arguments.iterator.map(_.showDbg).mkString("[", ", ", "]")
      s"${symbol.nme}$argumentsText"

type Pat = Pattern[Kind.Complete]

type ExPat = Pattern[Kind.Expanded]

type SpPat = Pattern[Kind.Specialized]

import Pattern.*

extension (pattern: ExPat)
  /** Modifies the pattern under the assumption that the scrutinee matches the
   *  given literal. We decide to not care about literals with fields. (For
   *  example, wrapped primitives with properties in JavaScript.) */
  def specialize(lit: syntax.Literal): SpPat = pattern.map:
    case Literal(`lit`) => Wildcard
    case _: (Literal | ClassLike) => Never
    case pattern: (Record | Tuple) => pattern
  
  /** Modifies the pattern under the assumption that the scrutinee matches the
   *  given class. */
  def specialize(symbol: ClassLikeSymbol): SpPat = pattern.map:
    case Literal(_) => Never
    /** Note that `ClassLike` corresponds the syntax sugar of class patterns
     *  intersected with record patterns. So, we need to leave the arguments
     *  part unchanged. If there's no arguments, we return `Wildcard`. */
    case ClassLike(`symbol`, arguments) =>
      arguments.fold(Wildcard)(_ |> Record.apply)
    case ClassLike(_, _) => Never
    case pattern: (Record | Tuple) => pattern
  
  /** Modifies the pattern under the assumption that the scrutinee matches the
   *  given literal or class. */
  def specialize(head: Option[Head]): SpPat = head match
    case Some(h: syntax.Literal) => pattern.specialize(h)
    case Some(h: ClassLikeSymbol) => pattern.specialize(h)
    case None => pattern.map:
      case _: (Literal | ClassLike) => Never
      case pattern: (Record | Tuple) => pattern
