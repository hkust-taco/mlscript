package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.Tree.*, Elaborator.{Ctxl, ctx}, Elaborator.State

// TODO(ucs): remove useless methods before merging the PR
/** Contains some helpers that makes UCS desugaring easier. */
trait DesugaringBase(using state: State):
  protected final def sel(p: Term, k: Ident): Term.SynthSel =
    (Term.SynthSel(p, k)(N): Term.SynthSel).withIArgs(Nil)
  protected final def sel(p: Term, k: Ident, s: FieldSymbol): Term.SynthSel =
    (Term.SynthSel(p, k)(S(s)): Term.SynthSel).withIArgs(Nil)
  protected final def sel(p: Term, k: Str): Term.SynthSel = sel(p, Ident(k): Ident)
  protected final def sel(p: Term, k: Str, s: FieldSymbol): Term.SynthSel = sel(p, Ident(k): Ident, s)
  protected final def int(i: Int) = Term.Lit(IntLit(BigInt(i)))
  protected final def str(s: Str) = Term.Lit(StrLit(s))
  protected final def fld(t: Term) = Fld(FldFlags.empty, t, N)
  protected final def tup(xs: Fld*): Term.Tup = Term.Tup(xs.toList)(Tup(Nil))
  protected final def app(l: Term, r: Term, label: Str): Term.App = app(l, r, FlowSymbol(label))
  protected final def app(l: Term, r: Term, s: FlowSymbol): Term.App =
    (Term.App(l, r)(App(Dummy, Dummy), N, s): Term.App).withIArgs(Nil)
    
  private lazy val runtimeRef: Term.Ref = state.runtimeSymbol.ref().withIArgs(Nil)

  /** Make a term that looks like `runtime.MatchResult` with its symbol. */
  protected lazy val matchResultClass: Ctxl[(Term.SynthSel, ClassSymbol)] =
    val classRef: Term.SynthSel = Term.SynthSel(runtimeRef, Ident("MatchResult"))(S(State.matchResultClsSymbol))
    (classRef.withIArgs(Nil), State.matchResultClsSymbol)

  /** Make a pattern that looks like `runtime.MatchResult.class`. */
  protected def matchResultPattern(parameters: Opt[List[BlockLocalSymbol]]): Ctxl[Pattern.ClassLike] =
    val (classRef, classSym) = matchResultClass
    val classSel = Term.SynthSel(classRef, Ident("class"))(S(classSym)).withIArgs(Nil)
    Pattern.ClassLike(classSel, parameters)
    // Pattern.ClassLike(classSym, classSel, parameters.map(_.map(S.apply)), false)(Empty())

  /** Make a term that looks like `runtime.MatchFailure` with its symbol. */
  protected lazy val matchFailureClass: Ctxl[(Term.Sel | Term.SynthSel, ClassSymbol)] =
    val classRef: Term.SynthSel = Term.SynthSel(runtimeRef, Ident("MatchFailure"))(S(State.matchFailureClsSymbol))
    (classRef.withIArgs(Nil), State.matchFailureClsSymbol)

  /** Make a pattern that looks like `runtime.MatchFailure.class`. */
  protected def matchFailurePattern(parameters: Opt[List[BlockLocalSymbol]]): Ctxl[Pattern.ClassLike] =
    val (classRef, classSym) = matchResultClass
    val classSel = Term.SynthSel(classRef, Ident("class"))(S(classSym)).withIArgs(Nil)
    Pattern.ClassLike(classSel, parameters)
    // Pattern.ClassLike(classSym, classSel, parameters.map(_.map(S.apply)), false)(Empty())

  protected lazy val tupleSlice = sel(sel(runtimeRef, "Tuple"), "slice")
  protected lazy val tupleGet = sel(sel(runtimeRef, "Tuple"), "get")
  protected lazy val stringStartsWith = sel(sel(runtimeRef, "Str"), "startsWith")
  protected lazy val stringGet = sel(sel(runtimeRef, "Str"), "get")
  protected lazy val stringDrop = sel(sel(runtimeRef, "Str"), "drop")

  /** Make a term that looks like `runtime.Tuple.get(t, i)`. */
  protected final def callTupleGet(t: Term, i: Int, label: Str): Ctxl[Term] =
    callTupleGet(t, i, FlowSymbol(label))

  /** Make a term that looks like `runtime.Tuple.slice(t, i)`. */
  protected final def callTupleGet(t: Term, i: Int, s: FlowSymbol): Ctxl[Term] =
    app(tupleGet, tup(fld(t), fld(int(i))), s)

  /** Make a term that looks like `runtime.Str.startsWith(t, p)`. */
  protected final def callStringStartsWith(t: Term.Ref, p: Term, label: Str): Ctxl[Term] =
    app(stringStartsWith, tup(fld(t), fld(p)), FlowSymbol(label))

  /** Make a term that looks like `runtime.Str.get(t, i)`. */
  protected final def callStringGet(t: Term.Ref, i: Int, label: Str): Ctxl[Term] =
    app(stringGet, tup(fld(t), fld(int(i))), FlowSymbol(label))

  /** Make a term that looks like `runtime.Str.drop(t, n)`. */
  protected final def callStringDrop(t: Term.Ref, n: Int, label: Str): Ctxl[Term] =
    app(stringDrop, tup(fld(t), fld(int(n))), FlowSymbol(label))

  protected final def tempLet(dbgName: Str, term: Term)(inner: TempSymbol => Split): Split =
    val s = TempSymbol(N, dbgName)
    Split.Let(s, term, inner(s))

  protected final def plainTest(cond: Term, dbgName: Str = "cond")(inner: => Split): Split =
    val s = TempSymbol(N, dbgName)
    Split.Let(s, cond, Branch(s.ref(), inner) ~: Split.End)
    
  protected lazy val lteq = state.builtinOpsMap("<=")
  protected lazy val lt = state.builtinOpsMap("<")
  protected lazy val eq = state.builtinOpsMap("==")
  
  def makeMatchResult(captures: Term)(using Elaborator.Ctx) =
    app(matchResultClass._1, tup(fld(captures)), FlowSymbol("result of `MatchResult`")).withIArgs(Nil)
    
  def makeMatchFailure(using Elaborator.Ctx) =
    app(matchFailureClass._1, tup(), FlowSymbol("result of `MatchFailure`")).withIArgs(Nil)

  /** Make a `Branch` that calls `Pattern` symbols' `unapply` functions. */
  def makeLocalPatternBranch(
      scrut: => Term.Ref,
      localPatternSymbol: BlockLocalSymbol,
      inner: => Split,
  )(fallback: Split): Ctxl[Split] =
    val call = app(localPatternSymbol.ref().withIArgs(Nil), tup(fld(scrut)), FlowSymbol(s"result of ${localPatternSymbol.nme}"))
    tempLet("matchResult", call): resultSymbol =>
      Branch(resultSymbol.ref().withIArgs(Nil), matchResultPattern(N), inner) ~: fallback

  /** Make a `Branch` that calls `Pattern` symbols' `unapply` functions. */
  def makeUnapplyBranch(
      scrut: => Term.Ref,
      clsTerm: Term,
      inner: => Split,
      method: Str = "unapply"
  )(fallback: Split): Ctxl[Split] =
    val call = app(sel(clsTerm, method).withIArgs(Nil), tup(fld(scrut)), FlowSymbol(s"result of $method")).withIArgs(Nil)
    tempLet("matchResult", call): resultSymbol =>
      Branch(resultSymbol.ref().withIArgs(Nil), matchResultPattern(N), inner) ~: fallback

  /** Make a `Branch` that calls `Pattern` symbols' `unapplyStringPrefix` functions. */
  def makeUnapplyStringPrefixBranch_OLD(
      scrut: => Term.Ref,
      clsTerm: Term,
      inner: TempSymbol => Split,
      method: Str = "unapplyStringPrefix"
  )(fallback: Split): Ctxl[Split] =
    val call = app(sel(clsTerm, method), tup(fld(scrut)), FlowSymbol(s"result of $method"))
    tempLet("matchResult", call): resultSymbol =>
      val argSym = TempSymbol(N, "arg")
      Branch(
        resultSymbol.ref().withIArgs(Nil),
        matchResultPattern(S(argSym :: Nil)),
        tempLet("postfix", callTupleGet(argSym.ref().withIArgs(Nil), 0, "postfix"))(inner)
      ) ~: fallback
  
  /** Make a `Branch` that calls `Pattern` symbols' `unapplyStringPrefix` functions. */
  def makeUnapplyStringPrefixBranch_NEW(
      scrut: => Term.Ref,
      clsTerm: Term,
      postfixSymbol: TempSymbol,
      inner: => Split,
      method: Str = "unapplyStringPrefix"
  )(fallback: Split): Ctxl[Split] =
    val call = app(sel(clsTerm, method).withIArgs(Nil), tup(fld(scrut)), FlowSymbol(s"result of $method")).withIArgs(Nil)
    tempLet("matchResult", call): resultSymbol =>
      // let `matchResult` be the return value
      val argSym = TempSymbol(N, "arg")
      // let `arg` be the first element of `matchResult`
      Branch(
        resultSymbol.ref().withIArgs(Nil),
        matchResultPattern(S(argSym :: Nil)),
        Split.Let(postfixSymbol, callTupleGet(argSym.ref().withIArgs(Nil), 0, "postfix"), inner)
      ) ~: fallback
  
  
  private lazy val fldFlagVal = FldFlags(false, false, false, false, true)
  
  protected lazy val matchResultClassParamOpt: Opt[ParamList] = S:
    PlainParamList(Param(fldFlagVal, VarSymbol(Ident("captures")), N, Modulefulness(N)(false)) :: Nil)
  
  protected lazy val matchFailureClassParamOpt: Opt[ParamList] = S:
    PlainParamList(Param(fldFlagVal, VarSymbol(Ident("errors")), N, Modulefulness(N)(false)) :: Nil)
