package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.*, Tree.Ident, Elaborator.State

/**
  * Flattened patterns used in splits for `Normalization` and `Lowering`. All
  * cases of patterns declared hereby can be matched in constant time.
  * Non-trivial patterns (e.g., unions, intersections,
  * transformations, etc) have been compiled to `Split`.
  */
enum FlatPattern extends AutoLocated:
  case Lit(literal: Literal)
  
  /**
    * To match against a class or an object.
    *
    * @param constructor The term representing the class or the object.
    * @param symbol The symbol resolved from `constructor`.
    * @param arguments The sub-scrutinees and their locations. This field is
    *        `None` when no argument list is provided, i.e., `x is Some`.
    * @param refined Whether the type of the scrutinee can be further refined by
    *        other patterns in nested splits. It is not used currently.
    * @param tree The tree which this pattern is elaborated from. This is only
    *        used for error reporting and should not be copied in `mkClone`.
    */
  case ClassLike(
      val constructor: Term,
      val symbol: ClassSymbol | ModuleOrObjectSymbol,
      val arguments: Opt[Ls[(LocalVarSymbol, Opt[Loc])]],
      var refined: Bool
  )(val tree: Tree)
  
  case Tuple(size: Int, inf: Bool)
  
  case Record(entries: List[(Ident -> LocalVarSymbol)])
  
  def mkClone(using State): FlatPattern = this match
    case Lit(literal) => Lit(literal)
    case pattern @ ClassLike(constructor, symbol, arguments, refined) =>
      ClassLike(constructor.mkClone, symbol, arguments, refined)(Tree.Dummy)
    case Tuple(size, inf) => Tuple(size, inf)
    case Record(entries) => Record(entries)
  
  def subTerms: Vector[Term] = this match
    case p: ClassLike => Vector(p.constructor)
    case _: (Lit | Tuple | Record) => Vector.empty
  
  def children: Vector[Located] = this match
    case Lit(literal) => Vector(literal)
    case ClassLike(ctor, symbol, scruts, _) => Vector(ctor) ++ scruts.fold(Vector.empty)(_.map(_._1))
    case Tuple(fields, _) => Vector.empty
    case Record(entries) =>
      entries.iterator.flatMap:
        case (nme, als) => Vector(nme, als)
      .toVector
  
  def showDbg(using DebugPrinter): Str =
    (this match
    case Lit(literal) => literal.idStr
    case ClassLike(ctor, symbol, args, rfd) =>
      def showCtor(ctor: Term): Str = ctor match
        // This prints the symbol name without `refNum` and "member:" prefix.
        case Term.Ref(sym: BlockMemberSymbol) => sym.nme
        // This prints the symbol without `refNum`.
        case Term.Ref(sym) => sym.toString
        case Term.Sel(p, i) => s"${showCtor(p)}.${i.name}"
        case Term.SynthSel(p, i) => s"${showCtor(p)}.${i.name}"
        case _ => ctor.showDbg
      (if rfd then "refined " else "") + showCtor(ctor) +
        args.fold("")(_.iterator.map(_._1.nme).mkString("(", ", ", ")"))
    case Tuple(size, inf) => "[]" + (if inf then ">=" else "=") + size
    case Record(Nil) => "{}"
    case Record(entries) =>
      entries.iterator.map(_.name + ": " + _).mkString("{ ", ", ", " }"))
