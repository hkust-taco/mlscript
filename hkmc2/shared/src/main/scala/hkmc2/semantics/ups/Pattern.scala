package hkmc2
package semantics
package ups


import mlscript.utils.AnyOps
import mlscript.utils.shorthands.*

import syntax.Tree
import Tree.Ident
import Term.Lit


enum Pattern:
  import Pattern.{Wildcard, Never}

  case Lit(lit: Term.Lit)

  /** Represents a constructor or a class,
    * possibly with arguments.
    * @param sym the class symbol corresponding to the class or the constructor
    * @param arguments is None if no arguments were provided (as
    * in ``Foo``, and is Some if there were arguments provided, even if
    *  it is an empty argument list, e.g. ``Bar()``)
    *
    * the list contains the patterns in the order with which they were given
    * along with the corresponding identifier, even if it was not present before.
    * e.g. if we have a class defintion ``class L = Nil | Cons(hd: Int, tl: L)``
    * then the pattern ``Cons(foo, bar)`` is expected to be
    * ``ClassLike(sym=Cons, arguments=Som(List((hd, foo), tl, bar)))``
    */
  case ClassLike(
    sym: ClassSymbol,
    arguments: Opt[Ls[(Ident, Pattern)]]
  )

  case Record(entries: Map[Ident, Pattern])

  /** @param entries is the ordered list of patterns, from left to right
    * @param strict is true if we matchexactly these fields, and no more,
    * it is false, if we are allowed to have more fields.
    *
    * Tuple([p0, ..., p(n-1)], true) <~> {0:p0, ..., n-1: p(n-1)} & Not({n:_})
    * Tuple([p0, ..., p(n-1)], false) <~> {0:p0, ..., n-1: p(n-1)}
    */
  case Tuple(entries: List[Pattern], strict: Bool)

  case And(patterns: List[Pattern])

  case Or(patterns: List[Pattern])

  case Not(pattern: Pattern)

  case Rename(pattern: Pattern, name: VarSymbol)

  case Extract(pattern: Pattern, term: Term)

  /** Represents a pattern Synonym,
    * possibly with arguments.
    * @param sym the pattern symbol corresponding to the class or the constructor
    * @param arguments is None if no arguments were provided (as
    * in ``Foo``, and is Some if there were arguments provided, even if
    *  it is an empty argument list, e.g. ``Bar()``)
    */
  case Synonym(sym: PatternSymbol, params: Opt[Ls[Pattern]])

  /** A simplified fold for ``Pattern``.
    * It is designed to be used when we want to
    * compute a single value, starting from the leaves.
    * It silently goes through ``Not``, ``Extract``, ``Rename`` and ``Synonym``.
    * The function must provide all the other base cases, and how
    * a list is merged (for ``And`` and ``Or`` nodes)
    */
  def fold[A](f: (Lit | ClassLike | Record | Tuple | List[A]) => A): A = this match
    case p: (Lit | ClassLike | Record | Tuple) => f(p)
    case And(patterns) => f(patterns.map(_.fold(f)))
    case Or(patterns) => f(patterns.map(_.fold(f)))
    case Not(pattern) => pattern.fold(f)
    case Rename(pattern, _) => pattern.fold(f)
    case Extract(pattern, _) => pattern.fold(f)
    case Synonym(_, params) => ??? // TODO call on the body 

    def heads: Set[Term.Lit | ClassSymbol] = this.fold:
    case Lit(lit) => Set(lit)
    case ClassLike(sym, _) => Set(sym)
    case _: (Record | Tuple) => Set()
    case ls: List[Set[Term.Lit | ClassSymbol]] => ls.toSet.flatten


  def fields: Set[Ident | Int] = this.fold:
    case _: (Lit | ClassLike) => Set()
    case Record(entries) => entries.keys.toSet[Ident | Int]
    case Tuple(entries, strict) =>
      val n = entries.size
      val subfields = Range(0, n).toSet[Ident | Int]
      // if this is strict, then a condition is imposed on field n
      if strict then subfields + n else subfields
    case ls: List[Set[Ident | Int]] => ls.toSet.flatten

  def collectSubPatterns(id: Ident): Set[Pattern] = this.fold:
    case Lit(_) => Set()
      // TODO: raise a warning
    case ClassLike(sym, arguments) => /* TODO:raise a warning */ arguments match
      case None => Set()
      case Some(arguments) =>
        arguments.find((id1, _) => id === id).map((_, p) => p) match
          case None => Set()
          case Some(value) => Set(value)
    case Record(entries) => entries.get(id).toSet
    case Tuple(entries, strict) => Set()
    case ls: List[Set[Pattern]] => ls.toSet.flatten

  def collectSubPatterns(n: Int): Set[Pattern] = this.fold:
    case _: (Lit | ClassLike) => /* TODO : riase a warning */ Set()
    case Record(_) => Set()
    case Tuple(entries, strict) => entries.lift(n).toSet
    case ls: List[Set[Pattern]] => ls.toSet.flatten

  // old versions without fold

  // def heads: Set[Term.Lit | ClassSymbol] = this match
  //   case _: (Record | Tuple) => Set()
  //   case Lit(lit) => Set(lit)
  //   case ClassLike(sym, _) => Set(sym)
  //   case And(patterns) => patterns.toSet.flatMap(_.heads)
  //   case Or(patterns) => patterns.toSet.flatMap(_.heads)
  //   case Not(pattern) => pattern.heads
  //   case Rename(pattern, _) => pattern.heads
  //   case Extract(pattern, _) => pattern.heads
  //   case Synonym(sym, params) => ??? // TODO : raise a warning

  // def fields: Set[Ident | Int] = this match
  //   case _: (Lit | ClassLike) => Set()
  //     // TODO : raise a warning
  //   case Record(entries) => entries.keys.toSet[Ident | Int]
  //   case Tuple(entries, strict) =>
  //     val n = entries.size
  //     val subfields = Range(0, n).toSet[Ident | Int]
  //     // if this is strict, then a condition is imposed on field n
  //     if strict then subfields + n else subfields
  //   case And(patterns) => patterns.toSet.flatMap(_.fields)
  //   case Or(patterns) => patterns.toSet.flatMap(_.fields)
  //   case Not(pattern) => pattern.fields
  //   case Rename(pattern, _) => pattern.fields
  //   case Extract(pattern, _) => pattern.fields
  //   case Synonym(sym, params) => ??? // TODO : raise a warning

  // def collectSubPatterns(id: Ident): Set[Pattern] = this match
  //   case Lit(_) => Set()
  //     // TODO: raise a warning
  //   case ClassLike(sym, arguments) => /* TODO:raise a warning */ arguments match
  //     case None => Set()
  //     case Some(arguments) =>
  //       arguments.find((id1, _) => id === id).map((_, p) => p) match
  //         case None => Set()
  //         case Some(value) => Set(value)
  //   case Record(entries) => entries.get(id).toSet
  //   case Tuple(entries, strict) => Set()
  //   case And(patterns) => patterns.toSet.flatMap(_.collectSubPatterns(id))
  //   case Or(patterns) => patterns.toSet.flatMap(_.collectSubPatterns(id))
  //   case Not(pattern) => pattern.collectSubPatterns(id)
  //   case Rename(pattern, _) => pattern.collectSubPatterns(id)
  //   case Extract(pattern, _) => pattern.collectSubPatterns(id)
  //   case Synonym(sym, params) => ???

  // def collectSubPatterns(n: Int): Set[Pattern] = this match
  //   case _: (Lit | ClassLike) => /* TODO : riase a warning */ Set()
  //   case Record(_) => Set()
  //   case Tuple(entries, strict) => entries.lift(n).toSet
  //   case And(patterns) => patterns.toSet.flatMap(_.collectSubPatterns(n))
  //   case Or(patterns) => patterns.toSet.flatMap(_.collectSubPatterns(n))
  //   case Not(pattern) => pattern.collectSubPatterns(n)
  //   case Rename(pattern, _) => pattern.collectSubPatterns(n)
  //   case Extract(pattern, _) => pattern.collectSubPatterns(n)
  //   case Synonym(sym, params) => ???

  def simplify: Pattern = this match
    case _: Lit => this
    case ClassLike(sym, arguments) =>
      ClassLike(sym, arguments.map(_.map((id, p) => (id, p.simplify))))
    case Record(entries) =>
      val simplify = entries.map((id, p) => (id, p.simplify))
      if simplify.exists((_, p) => p === Never) then Never else Record(simplify)
    case Tuple(entries, strict) =>
      val simplify = entries.map(_.simplify)
      if simplify.contains(Never) then Never else Tuple(simplify, strict)
    case And(patterns) =>
      val simplify = patterns.map(_.simplify)
      // we cannot simplify wildcard, because we still return the scrutinee
      if simplify.contains(Never) then Never else And(simplify)
    case Or(patterns) =>
      def simplifyOr(patterns: List[Pattern]): List[Pattern] = patterns match
        case Nil => Nil
        case p :: tl => p.simplify match
          case Never => simplifyOr(tl)
          case Wildcard => Wildcard :: Nil
          case pat => pat :: simplifyOr(tl)
      Or(simplifyOr(patterns))
    case Not(pattern) => Not(pattern.simplify)
    case Rename(pattern, name) => Rename(pattern.simplify, name)
    case Extract(pattern, term) => Extract(pattern.simplify, term)
    case Synonym(sym, params) => ???

  def specialize(lit: Term.Lit): Pattern = this match
    case Lit(lit1) =>
      if lit1 === lit then Wildcard else Never 
    case ClassLike(_, _) => Never
    case Record(_) => Never
      // TODO : are we sure that a literal can't have fields?
    case Tuple(Nil, false) => ???
    case Tuple(_, _) => Never
    case And(patterns) => And(patterns.map(_.specialize(lit)))
    case Or(patterns) => Or(patterns.map(_.specialize(lit)))
    case Not(pattern) => Not(pattern.specialize(lit))
    case Rename(pattern, name) => Rename(pattern.specialize(lit), name)
    case Extract(pattern, term) => Extract(pattern.specialize(lit), term)
    case Synonym(sym, params) => Synonym(sym, params.map(_.map(_.specialize(lit))))
  
  def specialize(cons: ClassSymbol): Pattern = this match
    case Lit(_) => Never
    case ClassLike(sym, arguments) =>
      if sym === cons then Wildcard else Never
    case Record(_) => this
    case Tuple(Nil, false) => ???
    case Tuple(_, _) => Never
    case And(patterns) => And(patterns.map(_.specialize(cons)))
    case Or(patterns) => Or(patterns.map(_.specialize(cons)))
    case Not(pattern) => Not(pattern.specialize(cons))
    case Rename(pattern, name) => Rename(pattern.specialize(cons), name)
    case Extract(pattern, term) => Extract(pattern.specialize(cons), term)
    case Synonym(sym, params) => Synonym(sym, params.map(_.map(_.specialize(cons))))

object Pattern:

  val Wildcard = Or(Nil)

  val Never = And(Nil)
