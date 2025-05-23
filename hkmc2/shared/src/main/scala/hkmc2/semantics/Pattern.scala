package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*, Tree.Ident
import Elaborator.{Ctx, ctx}
import ucs.DeBrujinSplit

import Pattern.*

/** Flat patterns for pattern matching */
enum Pattern extends AutoLocated:
  
  case Lit(literal: Literal)
  
  /** An individual argument is None when it is not matched, i.e. when an underscore is used there.
    * The whole argument list is None when no argument list is being matched at all, as in `x is Some then ...`. */
  case ClassLike(
      val constructor: Term,
      val arguments: Opt[Ls[Argument]],
      val mode: MatchMode,
      var refined: Bool
  )(val tree: Tree)
  
  case Tuple(size: Int, inf: Bool)
  
  case Record(entries: List[(Ident -> BlockLocalSymbol)])

  
  def subTerms: Ls[Term] = this match
    case p: ClassLike => p.constructor :: (p.mode match
      case MatchMode.Default | _: MatchMode.StringPrefix => Nil
      case MatchMode.Annotated(annotation) => annotation :: Nil)
    case _: (Lit | Tuple | Record) => Nil 
  
  def children: Ls[Located] = this match
    case Lit(literal) => literal :: Nil
    case ClassLike(ctor, scruts, _, _) => ctor :: scruts.fold(Nil)(_.map(_.scrutinee))
    case Tuple(fields, _) => Nil
    case Record(entries) => entries.flatMap { case (nme, als) => nme :: als :: Nil }
  
  def showDbg: Str = this match
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
      entries.iterator.map(_.name + ": " + _).mkString("{ ", ", ", " }")

object Pattern:
  /** Represent the type of arguments in `ClassLike` patterns. This type alias
   *  is used to reduce repetition in the code.
   * 
   *  - Field `pattern` is for error messages.
   *  - Field `split` is for pattern compilation.
   *    **TODO(ucs/rp)**: Replace with suitable representation when implement
   *    the new pattern compilation.
   */
  type Argument = (scrutinee: BlockLocalSymbol, pattern: Tree, split: Opt[DeBrujinSplit])
  
  /** A class-like pattern whose symbol is resolved to a class. */
  object Class:
    def unapply(p: Pattern): Opt[ClassSymbol] = p match
      case p: Pattern.ClassLike => p.constructor.symbol.flatMap(_.asCls)
      case _ => N
  
  /** A class-like pattern whose symbol is resolved to a module. */
  object Module:
    def unapply(p: Pattern): Opt[ModuleSymbol] = p match
      case p: Pattern.ClassLike => p.constructor.symbol.flatMap(_.asModOrObj)
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
    /** The pattern is annotated. The normalization will intepret the pattern
     *  matching behavior based on the resolved symbol
     */
    case Annotated(annotation: Term)
    
  object ClassLike:
    def apply(constructor: Term, arguments: Opt[Ls[BlockLocalSymbol]]): ClassLike =
      ClassLike(constructor, arguments.map(_.map(s => (s, Tree.Dummy, N))), MatchMode.Default, false)(Tree.Dummy)
