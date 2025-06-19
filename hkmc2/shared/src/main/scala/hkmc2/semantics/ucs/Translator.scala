package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import Split.display, ucs.Normalization
import syntax.{Fun, Keyword, Literal, ParamBind, Tree}, Tree.*, Keyword.`as`
import scala.collection.mutable.{Buffer, Set as MutSet}
import Elaborator.{Ctx, State}

object Translator:
  /** String range bounds must be single characters. */
  def isInvalidStringBounds(lo: StrLit, hi: StrLit)(using Raise): Bool =
    val ds = Buffer.empty[(Message, Option[Loc])]
    if lo.value.length != 1 then
      ds += msg"String range bounds must have only one character." -> lo.toLoc
    if hi.value.length != 1 then
      ds += msg"String range bounds must have only one character." -> hi.toLoc
    if ds.nonEmpty then error(ds.toSeq*)
    ds.nonEmpty

import Translator.*

/** This class translates a tree describing a pattern into functions that can
 *  perform pattern matching on terms described by the pattern.
 */
class Translator(val elaborator: Elaborator)(using State, Ctx) extends DesugaringBase:
  import elaborator.term, elaborator.tl.*, HelperExtractors.*, Pattern.MatchMode
  
  /** Each scrutinee is represented by a function that creates a reference to
   *  the scrutinee symbol. It is sufficient for current implementation.
   */
  private type Scrut = () => Term.Ref
  
  private type CaptureMap = Map[Param, Term.Ref]
  
  private type Inner = CaptureMap => Split
  
  private type PrefixInner = (CaptureMap, Scrut) => Split
  
  private lazy val lteq = State.builtinOpsMap("<=")
  private lazy val lt = State.builtinOpsMap("<")
  private lazy val eq = State.builtinOpsMap("==")
  
  private def makeRange(scrut: Scrut, lo: Literal, hi: Literal, rightInclusive: Bool, inner: Inner) =
    def scrutFld = fld(scrut())
    val test1 = app(lteq.ref(), tup(fld(Term.Lit(lo)), scrutFld), "gtLo")
    val upperOp = if rightInclusive then lteq else lt
    val test2 = app(upperOp.ref(), tup(scrutFld, fld(Term.Lit(hi))), "ltHi")
    plainTest(test1, "gtLo")(plainTest(test2, "ltHi")(inner(Map.empty)))
  
  /** Generate a split that consumes the entire scrutinee. */
  private def full(scrut: Scrut, pat: Tree, inner: Inner)(using patternParams: Ls[Param], raise: Raise): Split = trace(
    pre = s"full <<< $pat", 
    post = (split: Split) => s"full >>> $split"
  ):
    pat.deparenthesized match
      case lhs or rhs => full(scrut, lhs, inner) ~~: full(scrut, rhs, inner)
      case (lo: StrLit) to (incl, hi: StrLit) => if isInvalidStringBounds(lo, hi) then failure else
        makeRange(scrut, lo, hi, incl, inner)
      case (lo: IntLit) to (incl, hi: IntLit) => makeRange(scrut, lo, hi, incl, inner) 
      case (lo: DecLit) to (incl, hi: DecLit) => makeRange(scrut, lo, hi, incl, inner)
      case (lo: Literal) to (_, hi: Literal) =>
        error(msg"Incompatible range types: ${lo.describe} to ${hi.describe}" -> pat.toLoc)
        failure
      case lit: Literal => Branch(scrut(), Pattern.Lit(lit), inner(Map.empty)) ~: Split.End
      case App(Ident("-"), Tup(IntLit(value) :: Nil)) =>
        Branch(scrut(), Pattern.Lit(IntLit(-value)), inner(Map.empty)) ~: Split.End
      case App(Ident("-"), Tup(DecLit(value) :: Nil)) =>
        Branch(scrut(), Pattern.Lit(DecLit(-value)), inner(Map.empty)) ~: Split.End
      case prefix ~ postfix => stringPrefix(scrut, prefix, (captures1, postfixScrut) =>
        full(postfixScrut, postfix, captures2 => inner(captures2 ++ captures1)))
      case Under() => inner(Map.empty)
      case ctor @ (_: Ident | _: Sel) =>
        val ctorTrm = term(ctor)
        val pattern = Pattern.ClassLike(ctorTrm, N, MatchMode.Default, false)(ctor)
        Branch(scrut(), pattern, inner(Map.empty)) ~: Split.End
      case App(ctor @ (_: Ident | _: Sel), Tup(params)) =>
        // TODO(rp/str): handle input params
        val ctorTrm = term(ctor)
        val pattern = Pattern.ClassLike(ctorTrm, N, MatchMode.Default, false)(ctor)
        Branch(scrut(), pattern, inner(Map.empty)) ~: Split.End
      case pat =>
        error(msg"Unrecognized pattern (${pat.describe})" -> pat.toLoc)
        errorSplit
  
  /** Generate a split that consumes the prefix of the scrutinee. */
  private def stringPrefix(scrut: Scrut, pat: Tree, inner: PrefixInner)(using Raise): Split = trace(
    pre = s"stringPrefix <<< $pat", 
    post = (split: Split) => s"stringPrefix >>> $split"
  ):
    pat.deparenthesized match
    case lhs or rhs => stringPrefix(scrut, lhs, inner) ~~: stringPrefix(scrut, rhs, inner)
    case (lo: StrLit) to (incl, hi: StrLit) => if isInvalidStringBounds(lo, hi) then failure else
      val emptyTest = app(eq.ref(), tup(fld(scrut()), fld(str(""))), "test empty")
      val headTerm = callStringGet(scrut(), 0, "head")
      val tailTerm = callStringDrop(scrut(), 1, "tail")
      plainTest(emptyTest, "emptyTest")(failure) ~~:
        tempLet("head", headTerm): headSym =>
          tempLet("tail", tailTerm): tailSym =>
            makeRange(() => headSym.ref(), lo, hi, incl, captures =>
              inner(Map.empty, () => tailSym.ref()))
    case (lo: IntLit) to (incl, hi: IntLit) => Split.End
    case (lo: DecLit) to (incl, hi: DecLit) => Split.End
    case (lo: Literal) to (_, hi: Literal) =>
      error(msg"Incompatible range types: ${lo.describe} to ${hi.describe}" -> pat.toLoc)
      errorSplit
    case lit @ StrLit(value) =>
      plainTest(callStringStartsWith(scrut(), Term.Lit(lit), "startsWith")):
        tempLet("sliced", callStringDrop(scrut(), value.length, "sliced")): slicedSym =>
          inner(Map.empty, () => slicedSym.ref())
    case prefix ~ postfix =>
      stringPrefix(scrut, prefix, (captures1, postfixScrut1) =>
        stringPrefix(postfixScrut1, postfix, (captures2, postfixScrut2) =>
          inner(captures2 ++ captures1, postfixScrut2)))
    case Under() => inner(Map.empty, scrut) // TODO: check if this is correct
    case ctor @ (_: Ident | _: Sel) =>
      val ctorTrm = term(ctor)
      val prefixSymbol = new TempSymbol(N, "prefix")
      val postfixSymbol = new TempSymbol(N, "postfix")
      val mode = MatchMode.StringPrefix(prefixSymbol, postfixSymbol)
      val pattern = Pattern.ClassLike(ctorTrm, N, mode, false)(ctor)
      Branch(scrut(), pattern, inner(Map.empty, () => postfixSymbol.ref())) ~: Split.End
    case pat =>
      error(msg"Unrecognized pattern (${pat.describe})" -> pat.toLoc)
      errorSplit
  
  /** Create a function that compiles the resulting term of each case. It checks
   *  the captured references and sort them in the order of parameters.
   */
  private def success(params: Ls[Param])(using Raise): Inner =
    val paramIndexMap = params.zipWithIndex.toMap
    captures => trace(
      pre = s"success <<< ${params.iterator.map(_.sym).mkString(", ")}", 
      post = (split: Split) => s"success >>> ${display(split)}"
    ):
      require(captures.forall(_._1 |> paramIndexMap.contains))
      if captures.size != params.size then
        // TODO: report uncaptured parameters and add tests after captures/extraction is done
        error(msg"Unmatched number of captures and parameters." -> N)
        Split.Else(Term.Error)
      else
        val fields = captures.toList.sortBy(_._1 |> paramIndexMap).map:
          case (_, ref) => Fld(FldFlags.empty, ref, N)
        Split.Else(makeMatchResult(Term.Tup(fields)(Tup(Nil))))
  
  /* The successful matching result used in prefix matching functions. */
  private def prefixSuccess(params: Ls[Param])(using Raise): PrefixInner =
    val paramIndexMap = params.zipWithIndex.toMap
    (captures, postfixScrut) => trace(
      pre = s"prefixSuccess <<< ${params.iterator.map(_.sym).mkString(", ")}", 
      post = (split: Split) => s"prefixSuccess >>> ${display(split)}"
    ):
      require(captures.forall(_._1 |> paramIndexMap.contains))
      if captures.size != params.size then
        // TODO: report uncaptured parameters
        error(msg"Unmatched number of captures and parameters." -> N)
        Split.Else(Term.Error)
      else
        val fields = captures.toList.sortBy(_._1 |> paramIndexMap).map:
          case (_, ref) => Fld(FldFlags.empty, ref, N)
        val head = Fld(FldFlags.empty, postfixScrut(), N)
        Split.Else(makeMatchResult(Term.Tup(head :: fields)(Tup(Nil))))
  
  /** Failed matctching result. */
  private def failure: Split = Split.Else(makeMatchFailure)
  
  private def errorSplit: Split = Split.Else(Term.Error)
  
  /** Create a function definition from the given UCS splits. */
  private def makeMatcher(name: Str, scrut: VarSymbol, topmost: Split)(using Raise): TermDefinition =
    val sym = BlockMemberSymbol(name, Nil)
    val ps = PlainParamList(Param(FldFlags.empty, scrut, N, Modulefulness.none) :: Nil)
    val body = Term.IfLike(Keyword.`if`, topmost)
    val res = FlowSymbol(s"result of $name")
    TermDefinition(N, Fun, sym, ps :: Nil, N, N, S(body), res, TermDefFlags.empty, Modulefulness.none, Nil)
  
  /** Translate a list of extractor/matching functions for the given pattern.
   *  There are currently two functions: `unapply` and `unapplyStringPrefix`.
   *  
   *  - `unapply` is used for matching the entire scrutinee. It returns the
   *    captured/extracted values.
   *  - `unapplyStringPrefix` is used for matching the string prefix of the
   *    scrutinee. It returns the remaining string and the captured/extracted
   *    values. If the given tree does not represent a string pattern, this
   *    function will not be generated.
   */
  def apply(patternParams: Ls[Param], params: Ls[Param], body: Tree)(using Raise): Ls[TermDefinition] = trace(
    pre = s"Translator <<< ${params.mkString(", ")} $body", 
    post = (blk: Ls[TermDefinition]) => s"Translator >>> $blk"
  ):
    if patternParams.nonEmpty then
      // Temporarily disable the translation of pattern with pattern parameters.
      // TODO(rp): pass pattern parameters as objects to the `unapply` function
      Nil
    else
      val unapply = scoped("ucs:cp"):
        val scrutSym = VarSymbol(Ident("scrut"))
        val topmost = full(() => scrutSym.ref(), body, success(params))(using patternParams, raise) ~~: failure
        log(s"Translated `unapply`: ${display(topmost)}")
        makeMatcher("unapply", scrutSym, topmost)
      val unapplyStringPrefix = scoped("ucs:cp"):
        // We don't report errors here because they are already reported in the
        // translation of `unapply` function.
        given Raise = Function.const(())
        val scrutSym = VarSymbol(Ident("topic"))
        stringPrefix(() => scrutSym.ref(), body, prefixSuccess(params)) match
        case Split.Else(Term.Error) =>
          makeMatcher("unapplyStringPrefix", scrutSym, failure)
        case split =>
          val topmost = split ~~: failure
          log(s"Translated `unapplyStringPrefix`: ${display(topmost)}")
          makeMatcher("unapplyStringPrefix", scrutSym, topmost)
      unapply :: unapplyStringPrefix :: Nil
