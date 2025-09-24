package hkmc2
package semantics
package ups

import mlscript.utils.*, shorthands.*, Message.MessageContext, utils.TL
import syntax.Tree, Tree.Ident, ucs.safeRef, Elaborator.{Ctx, State}
import semantics.Pattern as SP // "SP" is short for "semantic patterns"

/** This class compiles a tree describing a pattern into functions that can
 *  perform pattern matching on terms described by the pattern. */
class NaiveCompiler(using tl: TL)(using State, Ctx, Raise) extends SplitCompiler:
  import tl.*, SP.*, SplitCompiler.*
  
  /** Make a term like `MatchFailure(null)`. We will synthesize detailed
   *  error messages and pass them to the function. */
  private def failure: Split = Split.Else(makeMatchFailure())
  
  /** Create a method from the given UCS splits.
   *  The function has a parameter list that contains the pattern parameters and
   *  a parameter that represents the input value.
   */
  private def makeMethod(
      name: Str,
      patternParameters: List[Param],
      scrut: VarSymbol,
      topmost: Split
  ): (BlockMemberSymbol, ParamList, Split) =
    val sym = BlockMemberSymbol(name, Nil)
    // Pattern parameters are passed as objects.
    val patternInputs = patternParameters.map(_.copy(flags = FldFlags.empty))
    // The last parameter is the scrutinee.
    val scrutParam = Param(FldFlags.empty, scrut, N, Modulefulness.none)
    val ps = PlainParamList(patternInputs :+ scrutParam)
    (sym, ps, topmost)
  
  /** Translate a list of extractor/matching functions for the given pattern.
   *  There are currently two functions: `unapply` and `unapplyStringPrefix`.
   *  
   *  - `unapply` is used for matching the entire scrutinee. It returns the
   *    captured/extracted values.
   *  - `unapplyStringPrefix` is used for matching the string prefix of the
   *    scrutinee. It returns the remaining string and the captured/extracted
   *    values. If the given tree does not represent a string pattern, this
   *    function will not be generated.
   *  
   *  @param pattern We will eventually generate methods from the omnipotent
   *                 `Pattern` class. Now the new `pattern` parameter and the
   *                 old `body` parameter are mixed.
   */
  def compilePattern(pd: PatternDef): Ls[(BlockMemberSymbol, ParamList, Split)] =
  trace(
    pre = s"compilePattern <<< ${pd.showDbg}", 
    post = (blk: Ls[(BlockMemberSymbol, ParamList, Split)]) =>
      s"compilePattern >>> $blk"
  ):
    // TODO: Use `pd.extractionParams`.
    val unapply = scoped("ucs:translation"):
      val inputSymbol = VarSymbol(Ident("input"))
      val topmost = makeMatchSplit(inputSymbol.toScrut, pd.pattern)
        ((output, bindings) => Split.Else(makeMatchResult(output())), failure)
      log(s"Translated `unapply`: ${topmost.prettyPrint}")
      makeMethod("unapply", pd.patternParams, inputSymbol, topmost)
    // TODO: Use `pd.extractionParams`.
    val unapplyStringPrefix = scoped("ucs:cp"):
      // We don't report errors here because they have been already reported in
      // the translation of `unapply` function.
      given Raise = Function.const(())
      val inputSymbol = VarSymbol(Ident("input"))
      val topmost = makeStringPrefixMatchSplit(inputSymbol.toScrut, pd.pattern)
        ((consumedOutput, remainingOutput, bindings) => Split.Else:
          makeMatchResult(tup(fld(consumedOutput()), fld(remainingOutput()))), failure)
      log(s"Translated `unapplyStringPrefix`: ${topmost.prettyPrint}")
      makeMethod("unapplyStringPrefix", pd.patternParams, inputSymbol, topmost)
    unapply :: unapplyStringPrefix :: Nil
  
  /** Generate the record statements of `unapply` methods that can be used in
   *  objects for anonymous patterns. */
  def makeUnapplyRecordStatements(
      name: Str,
      patternParameters: List[Param],
      scrut: VarSymbol,
      topmost: Split
  ): Ls[Statement] =
    val fieldSymbol = TempSymbol(N, name)
    val decl = LetDecl(fieldSymbol, Nil)
    val param = Param(FldFlags.empty, scrut, N, Modulefulness.none)
    val paramList = PlainParamList(param :: Nil)
    val lambda = Term.Lam(paramList, Term.SynthIf(topmost))
    val defineVar = DefineVar(fieldSymbol, lambda)
    val field = RcdField(str(name), fieldSymbol.safeRef)
    decl :: defineVar :: field :: Nil
  
  /** Translate an anonymous pattern. They are usually pattern arguments. */
  def compileAnonymousPattern(patternParams: Ls[Param], params: Ls[Param], pattern: SP): Term = trace(
    pre = s"compileAnonymousPattern <<< $pattern", 
    post = (blk: Term) => s"compileAnonymousPattern >>> $blk"
  ):
    // If the `target` refers to a pattern symbol, we can reference the pattern.
    val term = pattern match
      case Constructor(target, Nil, N) =>
        target.symbol.flatMap(_.asPat).flatMap(Compiler.reference(_, target.toLoc))
      case _ => N
    term.getOrElse:
      val unapply = scoped("ucs:translation"):
        val inputSymbol = VarSymbol(Ident("input"))
        val topmost = makeMatchSplit(inputSymbol.toScrut, pattern)
          ((output, bindings) => Split.Else(makeMatchResult(output())), failure)
        log(s"Translated `unapply`: ${topmost.prettyPrint}")
        makeUnapplyRecordStatements("unapply", patternParams, inputSymbol, topmost)
      val unapplyStringPrefix = scoped("ucs:cp"):
        // We don't report errors here because they have been already reported in
        // the translation of `unapply` function.
        given Raise = Function.const(())
        val inputSymbol = VarSymbol(Ident("input"))
        val topmost = makeStringPrefixMatchSplit(inputSymbol.toScrut, pattern)
          ((consumedOutput, remainingOutput, bindings) => Split.Else:
            makeMatchResult(tup(fld(consumedOutput()), fld(remainingOutput()))), failure)
        log(s"Translated `unapplyStringPrefix`: ${topmost.prettyPrint}")
        makeUnapplyRecordStatements("unapplyStringPrefix", patternParams, inputSymbol, topmost)
      Term.Rcd(false, unapply ::: unapplyStringPrefix)
