package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import Split.display, ucs.Normalization
import syntax.{Fun, Keyword, Literal, ParamBind, Tree}, Tree.*, Keyword.`as`
import scala.collection.mutable.{Buffer, Set as MutSet}

object Translator:
  /** A helper extractor for matching the tree of `x | y`. */
  object or:
    infix def unapply(tree: Tree): Opt[(Tree, Tree)] = tree match
      case App(Ident("|"), Tup(lhs :: rhs :: Nil)) => S(lhs, rhs)
      case _ => N
  
  /** A helper extractor for matching the tree of `x ..= y` and `x ..< y`.
   *  The Boolean value indicates whether the range is inclusive.
   */
  object to:
    infix def unapply(tree: Tree): Opt[(Tree, (Bool, Tree))] = tree match
      case App(Ident("..="), Tup(lhs :: rhs :: Nil)) => S(lhs, (true, rhs))
      case App(Ident("..<"), Tup(lhs :: rhs :: Nil)) => S(lhs, (false, rhs))
      case _ => N
      
  private def error(msgs: (Message, Option[Loc])*)(using Raise): Unit =
    raise(ErrorReport(msgs.toList))
  
  private def warn(msgs: (Message, Option[Loc])*)(using Raise): Unit =
    raise(WarningReport(msgs.toList))

/** This class translates a tree describing a pattern into functions that can
 *  perform pattern matching on terms described by the pattern.
 */
class Translator(val elaborator: Elaborator)
    (using state: Elaborator.State, c: Elaborator.Ctx) extends DesugaringBase:
  import elaborator.tl.*, Translator.*
  
  extension (split: Split)
    private def ~~:(fallback: Split): Split =
      if fallback == Split.End || split.isFull then
        split
      else (split match
        case Split.Cons(head, tail) => Split.Cons(head, tail ~~: fallback)
        case Split.Let(name, term, tail) => Split.Let(name, term, tail ~~: fallback)
        case Split.Else(_) /* impossible */ | Split.End => fallback)
  
  /** Each scrutinee is represented by a function that creates a reference to
   *  the scrutinee symbol. It is sufficient for current implementation.
   */
  private type Scrut = () => Term.Ref
  
  private type CaptureMap = Map[Param, Term.Ref]
  
  private type Inner = CaptureMap => Split
  
  private type PrefixInner = (CaptureMap, Scrut) => Split
  
  private def matchResult(captures: Term) =
    app(matchResultClass._1, tup(fld(captures)), FlowSymbol("result of `MatchResult`"))
  
  private def matchFailure() =
    app(matchFailureClass._1, tup(), FlowSymbol("result of `MatchFailure`"))
  
  private lazy val lteq = state.builtinOpsMap("<=")
  private lazy val lt = state.builtinOpsMap("<")
  private lazy val eq = state.builtinOpsMap("==")
  
  private def makeRange(scrut: Scrut, lo: Literal, hi: Literal, rightInclusive: Bool, inner: Inner) =
    def scrutFld = fld(scrut())
    val test1 = app(lteq.ref(), tup(fld(Term.Lit(lo)), scrutFld), "gtLo")
    val upperOp = if rightInclusive then lteq else lt
    val test2 = app(upperOp.ref(), tup(scrutFld, fld(Term.Lit(hi))), "ltHi")
    plainTest(test1, "gtLo")(plainTest(test2, "ltHi")(inner(Map.empty)))
  
  /** String range bounds must be single characters. */
  private def isInvalidStringBounds(lo: StrLit, hi: StrLit)(using Raise): Bool =
    val ds = Buffer.empty[(Message, Option[Loc])]
    if lo.value.length != 1 then
      ds += msg"String range bounds must have only one character." -> lo.toLoc
    if hi.value.length != 1 then
      ds += msg"String range bounds must have only one character." -> hi.toLoc
    if ds.nonEmpty then error(ds.toSeq*)
    ds.nonEmpty
  
  /** Generate a split that consumes the entire scrutinee. */
  private def full(scrut: Scrut, pat: Tree, inner: Inner)(using Raise): Split = trace(
    pre = s"full <<< $pat", 
    post = (split: Split) => s"full >>> $split"
  ):
    pat match
      case lhs or rhs => full(scrut, lhs, inner) ~~: full(scrut, rhs, inner)
      case (lo: StrLit) to (incl, hi: StrLit) => if isInvalidStringBounds(lo, hi) then failure else
        makeRange(scrut, lo, hi, incl, inner)
      case (lo: IntLit) to (incl, hi: IntLit) => makeRange(scrut, lo, hi, incl, inner) 
      case (lo: DecLit) to (incl, hi: DecLit) => makeRange(scrut, lo, hi, incl, inner)
      case (lo: Literal) to (_, hi: Literal) =>
        error(msg"Incompatible range types: ${lo.describe} to ${hi.describe}" -> pat.toLoc)
        failure
      case lit: StrLit => Branch(scrut(), Pattern.Lit(lit), inner(Map.empty)) ~: Split.End
      case App(Ident("~"), Tup(prefix :: postfix :: Nil)) =>
        stringPrefix(scrut, prefix, (captures1, postfixScrut) =>
          full(postfixScrut, postfix, captures2 => inner(captures2 ++ captures1)))
      case ctor @ (_: Ident | _: Sel) =>
        val clsTrm = elaborator.cls(ctor, inAppPrefix = false)
        clsTrm.symbol.flatMap(_.asClsLike) match
        case S(cls: (ClassSymbol | ModuleSymbol)) =>
          Branch(scrut(), Pattern.ClassLike(cls, clsTrm, N, false)(ctor), inner(Map.empty)) ~: Split.End
        case S(psym: PatternSymbol) =>
          makeUnapplyBranch(scrut(), clsTrm, inner(Map.empty))(Split.End)
        case _ =>
          error(msg"Cannot use this ${ctor.describe} as an extractor" -> ctor.toLoc)
          errorSplit
      case _ =>
        error(msg"Unrecognized pattern." -> pat.toLoc)
        errorSplit
  
  /** Generate a split that consumes the prefix of the scrutinee. */
  private def stringPrefix(scrut: Scrut, pat: Tree, inner: PrefixInner)(using Raise): Split = trace(
    pre = s"stringPrefix <<< $pat", 
    post = (split: Split) => s"stringPrefix >>> $split"
  ):
    pat match
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
    case _ =>
      error(msg"Unrecognized pattern." -> pat.toLoc)
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
        Split.Else(matchResult(Term.Tup(fields)(Tup(Nil))))
  
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
        Split.Else(matchResult(Term.Tup(head :: fields)(Tup(Nil))))
  
  /** Failed matctching result. */
  private def failure: Split = Split.Else(matchFailure())
  
  private def errorSplit: Split = Split.Else(Term.Error)
  
  /** Create a function definition from the given UCS splits. */
  private def makeMatcher(name: Str, scrut: TermSymbol, topmost: Split)(using Raise): TermDefinition =
    val normalize = new Normalization(elaborator.tl)
    val sym = BlockMemberSymbol(name, Nil)
    val ps = PlainParamList(Param(FldFlags.empty, scrut, N) :: Nil)
    val body = Term.IfLike(Keyword.`if`, topmost)(normalize(topmost))
    val res = FlowSymbol(s"result of $name")
    TermDefinition(N, Fun, sym, ps :: Nil, N, S(body), res, TermDefFlags.empty)
  
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
  def apply(params: Ls[Param], body: Tree)(using Raise): Ls[TermDefinition] = trace(
    pre = s"Translator <<< ${params.mkString(", ")} $body", 
    post = (blk: Ls[TermDefinition]) => s"Translator >>> $blk"
  ):
    val unapply =
      val scrutSym = TermSymbol(ParamBind, N, Ident("scrut"))
      val topmost = full(() => scrutSym.ref(), body, success(params)) ~~: failure
      log(s"Translated `unapply`: ${display(topmost)}")
      makeMatcher("unapply", scrutSym, topmost)
    val unapplyStringPrefix =
      // We don't report errors here because they are already reported in the
      // translation of `unapply` function.
      given Raise = Function.const(())
      val scrutSym = TermSymbol(ParamBind, N, Ident("topic"))
      stringPrefix(() => scrutSym.ref(), body, prefixSuccess(params)) match
      case Split.End => N
      case split =>
        val topmost = split ~~: failure
        log(s"Translated `unapplyStringPrefix`: ${display(topmost)}")
        S(makeMatcher("unapplyStringPrefix", scrutSym, topmost ~~: failure))
    unapply :: unapplyStringPrefix.toList
