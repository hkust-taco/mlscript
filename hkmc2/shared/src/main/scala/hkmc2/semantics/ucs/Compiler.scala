package hkmc2
package semantics
package ucs

import collection.mutable.{Map as MutMap}
import mlscript.utils.*, shorthands.*
import syntax.Tree, Tree.{BoolLit, DecLit, IntLit, StrLit, UnitLit}
import scala.collection.immutable.NumericRange
import Elaborator.{Ctx, State}
import hkmc2.semantics.Elaborator.ctx

class Compiler(val elaborator: Elaborator)(using Raise)
    extends DesugaringBase(using elaborator.state):
  
  import elaborator.tl.*, HelperExtractors.*
  
  extension (split: PartialSplit)
    def generate(parameters: Vector[() => Term.Ref], success: Split, failure: Split)(using State, Ctx): Split =
      def go(split: PartialSplit): Split = split match
        case PartialSplit.Branch(n, pattern, consequence, alternative) =>
          val scrutineeRef = parameters(n)
          pattern match
          case PatternStub.Literal(StrLit(value)) =>
            val test = app(eq.ref(), tup(fld(scrutineeRef()), fld(str(value))), "test equality")
            tempLet("test", test): testSymbol =>
              Branch(testSymbol.ref(), consequence.generate(parameters, success, failure)) ~:
                alternative.generate(parameters, success, failure)
          case PatternStub.ClassLike(StringJoin) =>
            tempLet("head", callStringGet(scrutineeRef(), 0, "get string head")): headSymbol =>
              tempLet("tail", callStringGet(scrutineeRef(), 1, "get string tail")): tailSymbol =>
                consequence.decrement.generate(Vector(() => headSymbol.ref(), () => tailSymbol.ref()), success, 
                  alternative.generate(parameters, success, failure))
        case PartialSplit.Accept => success
        case PartialSplit.Reject => failure
      go(split)
  
  /** All the splits that we have seen so far. */
  val visited = MutMap.empty[PartialSplit, Opt[TermDefinition]]
  
  def expand(split: PartialSplit)(using Ctx): PartialSplit =
    import Tree.*, PatternStub.*, PartialSplit.*
    def go(n: Int, tree: Tree): (=> PartialSplit, => PartialSplit) => PartialSplit =
      tree match
      case lhs or rhs => (con, alt) => go(n, lhs)(con, go(n, rhs)(con, alt))
      case lhs to (inclusive, rhs) => (lhs, rhs) match
        case (StrLit(lo), StrLit(hi)) => (lo.headOption, hi.headOption) match
          case (S(start), S(end)) if lo.length == 1 && hi.length == 1 =>
            Branch(n, CharClass(start, end, inclusive), _, _)
          case (_, _) => ???
        case (IntLit(lo), IntLit(hi)) => ??? // TODO: generalize `CharClass`
        case (DecLit(lo), DecLit(hi)) => ??? // TODO: generalize `CharClass`
        case (_, _) => ??? // TODO: warn about the type mismatch
      case prefix ~ suffix => (con, alt) =>
        val c = go(n + 1, prefix)(go(n + 2, suffix)(con, Reject), Reject)
        Branch(n, ClassLike(StringJoin), c, alt)
      case literal: syntax.Literal => Branch(n, Literal(literal), _, _)
      case constructor: (Ident | Sel) =>
        val clsTrm = elaborator.cls(constructor, inAppPrefix = false)
        clsTrm.symbol.flatMap(_.asClsLike) match
          case S(cls: (ClassSymbol | ModuleSymbol)) =>
            Branch(n, ClassLike(cls), _, _)
          case S(pat: PatternSymbol) =>
            Branch(n, ClassLike(pat), _, _)
    def rec(split: PartialSplit): PartialSplit = split match
      case Accept | Reject => split
      case Branch(n, ClassLike(ps: PatternSymbol), con, alt) =>
        go(n, ps.body)(con, alt)
      case split @ Branch(n, Literal(literal), con, alt) =>
        split.copy(alternative = rec(alt))
    rec(split)
    
  def first(split: PartialSplit): Set[PatternStub] =
    import PartialSplit.*, PatternStub.*
    def go(acc: Set[PatternStub], split: PartialSplit): Set[PatternStub] = split match
      case Accept | Reject => acc
      case Branch(0, pattern, consequence, alternative) =>
        go(acc + pattern, alternative)
      case Branch(_, _, _, alternative) => go(acc, alternative)
    go(Set.empty, split)
    
  private def lift(f: PartialSplit.Branch => PartialSplit): PartialSplit => PartialSplit =
    case split: PartialSplit.Branch => f(split)
    case split => split
    
  def specialize(split: PartialSplit, pattern: PatternStub): PartialSplit =
    import PatternStub.*, PartialSplit.*
    lazy val handle: PartialSplit => PartialSplit = lift(pattern match
      case Literal(StrLit(value)) =>
        value.headOption match
        case N => branch =>
          branch.pattern match
          case Literal(StrLit("")) => branch.consequence.decrement
          case _ => handle(branch.alternative)
        case S(head) => branch =>
          branch.pattern match
          case Literal(StrLit(value)) if value.headOption.contains(head) =>
            if value.length == 1 then
              branch.consequence.decrement
            else
              log("here?")
              branch.copy(pattern = Literal(StrLit(value.tail)))
          case CharClass(range) if range.contains(head) =>
            branch.consequence.decrement
      case CharClass(range) => branch => ???
      case ClassLike(StringJoin) => branch =>
        branch.pattern match
        case ClassLike(StringJoin) => branch.consequence.decrement
        case _ => Reject
      case Wildcard => identity)
    handle(split)
          
  // def specialize(pattern: PatternStub): PartialSplit => PartialSplit =
  //   import PatternStub.*, PartialSplit.*
  //   val go: PartialSplit => PartialSplit = lift(pattern match
  //     case Literal(StrLit("")) => branch =>
  //       // Empty string matches the prefix of any string. It filters out all
  //       // string patterns in the given split.
  //       branch.pattern match
  //         case CharClass(range) => branch
  //         case ClassLike(StringJoin, arguments) =>
  //           val left = arguments(0)
  //           val right = arguments(1)
  //           go(left) match
  //             case Accept => right
  //             case _ => 
  //         case _ => Accept
  //     case Literal(StrLit(prefix)) => branch =>
  //       branch.pattern match
  //         case Literal(StrLit(value)) if prefix.startsWith(value) =>
  //           // If the prefix of the string matches the prefix of the pattern,
  //           // we can remove the prefix from the pattern and continue.
  //           if prefix.length == value.length then Accept
  //           else branch.copy(pattern = Literal(StrLit(prefix.drop(value.length))))
  //         case CharClass(range) => prefix.headOption match
  //           case S(head) if prefix.length == 1 =>
              
  //         case _ => Reject
  //     case Literal(literal: (BoolLit | IntLit | DecLit | UnitLit)) =>
  //       // For literals other than strings, we can directly compare the values.
  //       // Note that `IntLit` and `DecLit` are not comparable and will be
  //       // specialized after we introduce numeric range patterns.
  //       _.pattern match
  //         case Literal(`literal`) => Accept
  //         case _ => Reject
  //     case CharClass(range) => branch => ???
  //     case ClassLike(symbol, subSplits) => branch => ???
  //     case Wildcard => branch => Accept)
  //   go
  
  def apply(ps: PatternSymbol)(using Ctx, State): (() => Term.Ref, Split) => Split =
    // Compile the definition of the pattern into a split generation function.
    // 1. Convert the definition of the pattern into a partial split.
    // 2. Expand the partial split until we the `FIRST` set can be computed.
    // 3. Specialize the expanded partial split with respect to the `FIRST` set.
    // 4. If we reach a fixed point, we create a local function and replace the
    //    pattern with the function call.
    // 5. Stop after we have visited all the accepts and rejects.
    import PartialSplit.*, PatternStub.*

    val visited = MutMap.empty[PartialSplit, Opt[TermSymbol]]

    def visit(split: PartialSplit): PartialSplit =
      val num = visited.size
      log(s"[$num] Initial split:\n" + split.showDbg)
      val expanded = expand(split)
      log(s"[$num] Expanded split:\n" + expanded.showDbg)
      visited += expanded -> N
      val firstPatterns = first(expanded)
      log(s"[$num] First patterns: " + (if firstPatterns.isEmpty then "none" else
        firstPatterns.iterator.map(_.showDbg).mkString(", ")))
      val specialized = firstPatterns.map(first => first -> specialize(expanded, first))
      log(s"[$num] Specialized splits: " + (if specialized.isEmpty then "none" else specialized.iterator.map:
        case (first, split) =>
          val tree = split.showDbg
          val v = if visited.contains(split) then " *" else ""
          s"${first.showDbg} =>$v ${if tree.contains('\n') then "\n" + tree else " " + tree}"
      .mkString("\n")))
      specialized.foldRight(Reject):
        case ((firstPattern, specializedSplit), alternative) =>
        visited.get(specializedSplit) match
          case N =>
            Branch(0, firstPattern, visit(specializedSplit), alternative.decrement).increment
          case S(N) =>
            val funSym = TermSymbol(syntax.Fun, ctx.outer, Tree.Ident("matcher"))
            visited.update(specializedSplit, S(funSym))
            Branch(0, PatternStub.ClassLike(funSym), Accept, alternative.decrement).increment
          case S(S(funSym)) => 
            Branch(0, PatternStub.ClassLike(funSym), Accept, alternative.decrement).increment
      
    val result = visit(Branch(0, ClassLike(ps), Accept,Reject))
    log("Final result:\n" + result.showDbg)
    
    (scrutineeRef, consequence) =>
      result.generate(Vector(scrutineeRef), consequence, Split.End)(using elaborator.state)
end Compiler
