package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.*, Tree.Ident
import Elaborator.{Ctx, ctx, State}
import DeBrujinSplit.*
import collection.mutable.Buffer

import FlatPattern.*

/** Flat patterns for pattern matching */
enum FlatPattern extends AutoLocated:
  /** The symbol that binds the output of this pattern. */
  val output: Ls[BlockLocalSymbol]
  
  case Lit(literal: Literal)(val output: Ls[BlockLocalSymbol])
  
  /** An individual argument is None when it is not matched, i.e. when an underscore is used there.
    * The whole argument list is None when no argument list is being matched at all, as in `x is Some then ...`. */
  case ClassLike(
      val constructor: Term,
      val arguments: Opt[Ls[Argument]],
      val mode: MatchMode,
      var refined: Bool
  )(val tree: Tree, val output: Ls[BlockLocalSymbol])
  
  case Tuple(size: Int, inf: Bool)(val output: Ls[BlockLocalSymbol])
  
  case Record(entries: List[(Ident -> BlockLocalSymbol)])(val output: Ls[BlockLocalSymbol])
  
  def subTerms: Ls[Term] = this match
    case p: ClassLike => p.constructor :: (p.mode match
      case MatchMode.Default => p.arguments.fold(Nil):
        _.iterator.flatMap(_.pattern).toList
      case _: MatchMode.StringPrefix => Nil
      case MatchMode.Annotated(annotation) => annotation :: Nil)
    case _: (Lit | Tuple | Record) => Nil
  
  def children: Ls[Located] = this match
    case Lit(literal) => literal :: Nil
    case ClassLike(ctor, scruts, _, _) => ctor :: scruts.fold(Nil)(_.map(_.scrutinee))
    case Tuple(fields, _) => Nil
    case Record(entries) => entries.flatMap { case (nme, als) => nme :: als :: Nil }
  
  def showDbg: Str =
    (this match
    case Lit(literal) => literal.idStr
    case ClassLike(ctor, args, _, rfd) =>
      def showCtor(ctor: Term): Str = ctor match
        // This prints the symbol name without `refNum` and "member:" prefix.
        case Term.Ref(sym: BlockMemberSymbol) => sym.nme
        // This prints the symbol without `refNum`.
        case Term.Ref(sym) => sym.toString
        case Term.Sel(p, i) => s"${showCtor(p)}.${i.name}"
        case Term.SynthSel(p, i) => s"${showCtor(p)}.${i.name}"
        case _ => ctor.showDbg
      (if rfd then "refined " else "") + showCtor(ctor) +
        args.fold("")(_.iterator.map(_.scrutinee.nme).mkString("(", ", ", ")"))
    case Tuple(size, inf) => "[]" + (if inf then ">=" else "=") + size
    case Record(Nil) => "{}"
    case Record(entries) =>
      entries.iterator.map(_.name + ": " + _).mkString("{ ", ", ", " }")) +
      output.iterator.map(s => s.nme).mkStringOr("as ", " as ", "", "")

object FlatPattern:
  /** Represent the type of arguments in `ClassLike` patterns. This type alias
   *  is used to reduce repetition in the code.
   * 
   *  @param scrutinee the symbol representing the scrutinee
   *  @param tree the original `Tree` for making error messages
   *  @param split is for the old pattern compilation. **TODO(ucs/rp)**: Replace
   *               with suitable representation when implementing the new pattern
   *               compilation.
   *  @param pattern is for the new pattern compilation and translation.
   */
  final case class Argument(
      scrutinee: BlockLocalSymbol,
      tree: Tree,
      split: Opt[DeBrujinSplit],
      pattern: Opt[Term.Rcd]
  ) extends Located:
    override def toLoc: Opt[Loc] = tree.toLoc
  
  object Argument:
    def apply(scrutinee: BlockLocalSymbol, tree: Tree): Argument =
      Argument(scrutinee, tree, N, N)
    def apply(scrutinee: BlockLocalSymbol): Argument =
      Argument(scrutinee, Tree.Dummy, N, N)
  
  /** A class-like pattern whose symbol is resolved to a class. */
  object Class:
    def unapply(p: FlatPattern): Opt[ClassSymbol] = p match
      case p: FlatPattern.ClassLike => p.constructor.symbol.flatMap(_.asCls)
      case _ => N
  
  /** A class-like pattern whose symbol is resolved to a module. */
  object Module:
    def unapply(p: FlatPattern): Opt[ModuleSymbol] = p match
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
    case StringPrefix(prefix: TempSymbol, postfix: TempSymbol)
    /** Call `unapplyTuplePrefix` instead of `unapply`. */
    case TuplePrefix(prefix: TempSymbol, postfix: TempSymbol)
    /** The pattern is annotated. The normalization will intepret the pattern
     *  matching behavior based on the resolved symbol
     */
    case Annotated(annotation: Term)
    
  object ClassLike:
    def apply(constructor: Term, arguments: Opt[Ls[BlockLocalSymbol]])(output: Ls[BlockLocalSymbol]): ClassLike =
      ClassLike(constructor, arguments.map(_.map(Argument(_))), MatchMode.Default, false)(Tree.Dummy, output)
