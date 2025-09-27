package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.*, Tree.Ident
import Elaborator.{Ctx, ctx, State}
import collection.mutable.Buffer

import FlatPattern.*
import hkmc2.codegen.Block

// TODO TODO: Renamed to `ResolvedPattern`.
/** Flat patterns for pattern matching */
enum FlatPattern extends AutoLocated:
  /** The symbol that binds the output of this pattern. */
  val output: Ls[BlockLocalSymbol]
  
  case Lit(literal: Literal)(val output: Ls[BlockLocalSymbol])
  
  // TODO TODO: Separate into class and object patterns so that the 
  // number of arguments are always correct.
  /** An individual argument is None when it is not matched, i.e. when an underscore is used there.
    * The whole argument list is None when no argument list is being matched at all, as in `x is Some then ...`. */
  case ClassLike(
      val constructor: Term,
      val symbol: ClassSymbol | ModuleOrObjectSymbol | VarSymbol,
      val arguments: Opt[Ls[(BlockLocalSymbol, Opt[Loc])]],
      val mode: MatchMode,
      var refined: Bool
  )(val tree: Tree, val output: Ls[BlockLocalSymbol])
  
  /**
    * The number of pattern arguments and the number of extraction arguments are
    * assumed to match with the pattern definition.
    *
    * @param constructor
    * @param symbol
    * @param patternArguments
    * @param extractionArguments
    * @param mode to either match the entire scrutinee or match the prefix
    * @param output
    */
  case Pattern(
      val constructor: Term,
      val symbol: PatternSymbol,
      val patternArguments: Ls[semantics.Pattern],
      val extractionArguments: Opt[Ls[(BlockLocalSymbol, Opt[Loc])]],
      val mode: MatchMode,
  )(val output: Ls[BlockLocalSymbol])
  
  case Tuple(size: Int, inf: Bool)(val output: Ls[BlockLocalSymbol])
  
  case Record(entries: List[(Ident -> BlockLocalSymbol)])(val output: Ls[BlockLocalSymbol])
  
  def mkClone(using State): FlatPattern = this match
    case Lit(literal) => Lit(literal)(output)
    case pattern @ ClassLike(constructor, symbol, arguments, mode, refined) =>
      ClassLike(constructor.mkClone, symbol, arguments, mode, refined)(Tree.Dummy, output)
    case Pattern(constructor, patternSymbol, patternArguments, extractionArguments, mode) =>
      val clonedPatternArguments = patternArguments.map(_.mkClone)
      val clonedExtractionArguments = 
        extractionArguments.map(_.map(_._1 -> N))
      Pattern(constructor.mkClone, patternSymbol, clonedPatternArguments, clonedExtractionArguments, mode)(output)
    case Tuple(size, inf) => Tuple(size, inf)(output)
    case Record(entries) => Record(entries)(output)
  
  def subTerms: Ls[Term] = this match
    case p: ClassLike => p.constructor :: Nil
    case _: (Lit | Tuple | Record) => Nil
  
  def children: Ls[Located] = this match
    case Lit(literal) => literal :: Nil
    case ClassLike(ctor, symbol, scruts, _, _) => ctor :: scruts.fold(Nil)(_.map(_._1))
    case Tuple(fields, _) => Nil
    case Record(entries) => entries.flatMap { case (nme, als) => nme :: als :: Nil }
    case Pattern(patternTerm, patternSymbol, patternArguments, extractionArguments, _) =>
      // TODO TODO: Return `extractionArguments`.
      patternTerm :: patternArguments
  
  def showDbg: Str =
    (this match
    case Lit(literal) => literal.idStr
    case ClassLike(ctor, symbol, args, _, rfd) =>
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
      entries.iterator.map(_.name + ": " + _).mkString("{ ", ", ", " }")) +
      output.iterator.map(s => s.nme).mkStringOr("as ", " as ", "", "")

object FlatPattern:
  /** A class-like pattern whose symbol is resolved to a class. */
  object Class:
    def unapply(p: FlatPattern): Opt[ClassSymbol] = p match
      case p: FlatPattern.ClassLike => p.constructor.symbol.flatMap(_.asCls)
      case _ => N
  
  /** A class-like pattern whose symbol is resolved to a module. */
  object Module:
    def unapply(p: FlatPattern): Opt[ModuleOrObjectSymbol] = p match
      case p: FlatPattern.ClassLike => p.constructor.symbol.flatMap(_.asModOrObj)
      case _ => N
  
  enum MatchMode:
    /** The default mode. If the constructor resolves to:
     *  - a `ClassSymbol`, then check if the scrutinee is an instance;
     *  - a `ModuleSymbol`, then check if the scrutinee is the object;
     *  - a `PatternSymbol`, then call `unapply` on the pattern.
     */
    case Default
    /** Call `unapplyStringPrefix` instead of `unapply`. */
    case StringPrefix(prefix: BlockLocalSymbol, postfix: BlockLocalSymbol)
    
  object ClassLike:
    def apply(constructor: Term, symbol: ClassSymbol | ModuleOrObjectSymbol, arguments: Opt[Ls[(BlockLocalSymbol, Opt[Loc])]], output: Ls[BlockLocalSymbol]): ClassLike =
      ClassLike(constructor, symbol, arguments, MatchMode.Default, false)(Tree.Dummy, output)
    def apply(constructor: Term, symbol: ClassSymbol | ModuleOrObjectSymbol, symbols: Opt[Ls[BlockLocalSymbol]]): ClassLike =
      ClassLike(constructor, symbol, symbols.map(_.map(_ -> N)), MatchMode.Default, false)(Tree.Dummy, Nil)
