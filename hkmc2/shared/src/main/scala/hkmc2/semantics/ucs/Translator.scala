package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import Split.display, ucs.Normalization
import syntax.{Fun, Keyword, Literal, ParamBind, Tree}, Tree.*, Keyword.`as`
import scala.collection.mutable.{Buffer, Set as MutSet}

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
class Translator(val elaborator: Elaborator)
    (using state: Elaborator.State, c: Elaborator.Ctx) extends DesugaringBase:
  import elaborator.tl.*, HelperExtractors.*
  
  /** Each scrutinee is represented by a function that creates a reference to
   *  the scrutinee symbol. It is sufficient for current implementation.
   */
  private type Scrut = () => Term.Ref
  
  private type CaptureMap = Map[Param, Term.Ref]
  
  private type Inner = CaptureMap => Split
  
  private type PrefixInner = (CaptureMap, Scrut) => Split
  
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
      case App(Ident("~"), Tup(prefix :: postfix :: Nil)) =>
        stringPrefix(scrut, prefix, (captures1, postfixScrut) =>
          full(postfixScrut, postfix, captures2 => inner(captures2 ++ captures1)))
      case Under() => inner(Map.empty)
      case ctor @ (_: Ident | _: Sel) =>
        lazy val resolved =
          val clsTrm = elaborator.cls(ctor, inAppPrefix = false)
          clsTrm.symbol.flatMap(_.asClsLike) match
          case S(cls: (ClassSymbol | ModuleSymbol)) =>
            Branch(scrut(), Pattern.ClassLike(cls, clsTrm, N, false)(ctor), inner(Map.empty)) ~: Split.End
          case S(psym: PatternSymbol) =>
            makeUnapplyBranch(scrut(), clsTrm, inner(Map.empty))(Split.End)
          case _ =>
            error(msg"Cannot use this ${ctor.describe} as an extractor" -> ctor.toLoc)
            errorSplit
        ctor match
        case Ident(ctorName) => patternParams.find(_.sym.nme == ctorName) match
          case S(Param(_, symbol, _)) => failure // TODO: handle input patterns
          case N => resolved
        case ctor: Sel => resolved
      case App(ctor @ (_: Ident | _: Sel), Tup(params)) =>
        lazy val resolved =
          val clsTrm = elaborator.cls(ctor, inAppPrefix = false)
          clsTrm.symbol.flatMap(_.asClsLike) match
          case S(cls: (ClassSymbol | ModuleSymbol)) =>
            // TODO: handle parameters
            Branch(scrut(), Pattern.ClassLike(cls, clsTrm, N, false)(ctor), inner(Map.empty)) ~: Split.End
          case S(psym: PatternSymbol) =>
            // TODO: handle parameters
            makeUnapplyBranch(scrut(), clsTrm, inner(Map.empty))(Split.End)
          case _ =>
            error(msg"Cannot use this ${ctor.describe} as an extractor" -> ctor.toLoc)
            errorSplit
        ctor match
        case Ident(ctorName) => patternParams.find(_.sym.nme == ctorName) match
          case S(Param(_, symbol, _)) => failure // TODO: handle input patterns
          case N => resolved
        case ctor: Sel => resolved
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
    case App(Ident("~"), Tup(prefix :: postfix :: Nil)) =>
      stringPrefix(scrut, prefix, (captures1, postfixScrut1) =>
        stringPrefix(postfixScrut1, postfix, (captures2, postfixScrut2) =>
          inner(captures2 ++ captures1, postfixScrut2)))
    case Under() => inner(Map.empty, scrut) // TODO: check if this is correct
    case ctor @ (_: Ident | _: Sel) =>
      val clsTrm = elaborator.cls(ctor, inAppPrefix = false)
      clsTrm.symbol.flatMap(_.asClsLike) match
      case S(cls: (ClassSymbol | ModuleSymbol)) =>
        val kind = cls match { case _: ClassSymbol => "class" case _ => "module" }
        error(msg"Cannot treat this $kind as a string prefix" -> ctor.toLoc)
        errorSplit
      case S(psym: PatternSymbol) =>
        makeUnapplyStringPrefixBranch(scrut(), clsTrm, postfixSym =>
          inner(Map.empty, () => postfixSym.ref())
        )(Split.End)
      case _ =>
        error(msg"Cannot use this ${ctor.describe} as an extractor" -> ctor.toLoc)
        errorSplit
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
  private def makeMatcher(name: Str, scrut: TermSymbol, topmost: Split)(using Raise): TermDefinition =
    val normalize = new Normalization(elaborator)
    val sym = BlockMemberSymbol(name, Nil)
    val ps = PlainParamList(Param(FldFlags.empty, scrut, N) :: Nil)
    val body = Term.IfLike(Keyword.`if`, topmost)(normalize(topmost))
    val res = FlowSymbol(s"result of $name")
    TermDefinition(N, Fun, sym, ps :: Nil, N, S(body), res, TermDefFlags.empty, Nil)
  
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
    val unapply = scoped("ucs:cp"):
      val scrutSym = TermSymbol(ParamBind, N, Ident("scrut"))
      val topmost = full(() => scrutSym.ref(), body, success(params))(using patternParams, raise) ~~: failure
      log(s"Translated `unapply`: ${display(topmost)}")
      makeMatcher("unapply", scrutSym, topmost)
    val unapplyStringPrefix = scoped("ucs:cp"):
      // We don't report errors here because they are already reported in the
      // translation of `unapply` function.
      given Raise = Function.const(())
      val scrutSym = TermSymbol(ParamBind, N, Ident("topic"))
      stringPrefix(() => scrutSym.ref(), body, prefixSuccess(params)) match
      case Split.Else(Term.Error) =>
        makeMatcher("unapplyStringPrefix", scrutSym, failure)
      case split =>
        val topmost = split ~~: failure
        log(s"Translated `unapplyStringPrefix`: ${display(topmost)}")
        makeMatcher("unapplyStringPrefix", scrutSym, topmost)
    unapply :: unapplyStringPrefix :: Nil
