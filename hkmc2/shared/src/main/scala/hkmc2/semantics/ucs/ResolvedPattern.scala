
package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import utils.TL
import syntax.Tree, Tree.Ident
import Elaborator.{Ctx, ctx, State}
import Term.Ref, SimpleSplit as SS
import hkmc2.Message.MessageContext
import collection.mutable.{Map as MutMap}
import hkmc2.semantics.ups.NaiveCompiler

/**
  * `ResolvedPattern` is produced from the UCS desugaring phase. It makes sure
  * that the class/object/pattern is resolved to a symbol and the arguments have
  * been checked and guaranteed to be valid.
  * 
  * Note that since pattern compilation has not taken place yet, thus there is a
  * field for alias variables declared by `as` keyword. Also, there is a field
  * for annotations on the split, which decides how the pattern is compiled in
  * the later stages.
  */
enum ResolvedPattern extends AutoLocated:
  case Literal(literal: syntax.Literal)
  case Class(symbol: ClassSymbol, arguments: Opt[Ls[BlockLocalSymbol]])
  case Object(symbol: ModuleOrObjectSymbol)
  case Pattern(
      symbol: PatternSymbol,
      patternArguments: Ls[Pattern],
      extractionArguments: Ls[BlockLocalSymbol]
  )
  case Tuple(size: Int, infinite: Bool)
  case Record(entries: Ls[Ident -> BlockLocalSymbol])
  
  protected def children: List[Located] = ???

object ExpandedSplit:
  enum Head:
    case Match(
        scrutinee: Ref,
        pattern: ResolvedPattern,
        annotations: Ls[Annot],
        aliases: Ls[BlockLocalSymbol],
        consequent: ExpandedSplit,
    )
    case Let(symbol: Opt[BlockLocalSymbol], term: Term)
  
  /**
    * We hope to reuse the symbols of sub-scrutinees when scrutinees are matched
    * against the same patterns, so that these splits can be merged more
    * efficiently during normalization.
    */
  private class SubScrutineeCache(using State):
    type Sym = BlockLocalSymbol
    val parameters = MutMap.empty[ClassSymbol | PatternSymbol, MutMap[Int, Sym]]
    val tupleFirstElements = MutMap.empty[Int, Sym]
    var tupleSpreadElements: Opt[Sym] = N
    val tupleLastElements = MutMap.empty[Int, Sym]
    val recordFields = MutMap.empty[Ident, Sym]
    
    def apply(classOrPattern: ClassSymbol | PatternSymbol, index: Int): Sym = ???
    def apply(index: Int): Sym = ???
    def spread: Sym = tupleSpreadElements match
      case N => val s = TempSymbol(N, "spread"); tupleSpreadElements = S(s); s
      case S(s) => s
    def apply(ident: Ident): Sym = ???
  
  // def from(rootSplit: SS)(using Ctx, Raise, State, TL): ExpandedSplit =
  //   val subScrutineeCacheMap = MutMap.empty[Ref, SubScrutineeCache]
  //   val compiler = new NaiveCompiler()
  //   def expand(
  //       scrutinee: Ref,
  //       pattern: Pattern,
  //       consequent: ExpandedSplit,
  //       alternative: ExpandedSplit
  //   ): ExpandedSplit =
  //     compiler.makeMatchSplit
  //       (Function.const(scrutinee), pattern)
  //       ((_) => consequent, alternative)
  //   def main(split: SS): ExpandedSplit = split match
  //     case SS.Cons(branch, tail) => branch match
  //       case SS.Head.Match(scrutinee, pattern, consequent) =>
  //         expand(scrutinee, pattern, main(consequent), main(tail))
  //       case SS.Head.Let(binding, term) =>
  //         Cons(Head.Let(S(binding), term), main(tail))
  //     case SS.Else(default) => Else(default)
  //     case SS.End => End
  //   main(rootSplit)

enum ExpandedSplit extends AutoLocated:
  case Cons(head: ExpandedSplit.Head, tail: ExpandedSplit)
  case Else(term: Term)
  case End
  
  protected def children: List[Located] = ???
