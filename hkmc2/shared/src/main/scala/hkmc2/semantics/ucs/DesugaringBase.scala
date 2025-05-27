package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.Tree.*, Elaborator.{Ctx, ctx}, Elaborator.State

/** Contains some helpers that makes UCS desugaring easier. */
trait DesugaringBase(using Ctx, State):
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
    
  private lazy val runtimeRef: Term.Ref = State.runtimeSymbol.ref().withIArgs(Nil)

  /** Make a term that looks like `runtime.MatchResult` with its symbol. */
  protected lazy val matchResultClass =
    sel(runtimeRef, "MatchResult", State.matchResultClsSymbol)

  /** Make a pattern that looks like `runtime.MatchResult.class`. */
  protected def matchResultPattern(parameters: Opt[Ls[BlockLocalSymbol]]): Pattern.ClassLike =
    Pattern.ClassLike(sel(matchResultClass, "class", State.matchResultClsSymbol), parameters)

  /** Make a term that looks like `runtime.MatchFailure` with its symbol. */
  protected lazy val matchFailureClass =
    sel(runtimeRef, "MatchFailure", State.matchFailureClsSymbol)

  /** Make a pattern that looks like `runtime.MatchFailure.class`. */
  protected def matchFailurePattern(parameters: Opt[Ls[BlockLocalSymbol]]): Pattern.ClassLike =
    Pattern.ClassLike(sel(matchFailureClass, "class", State.matchFailureClsSymbol), parameters)

  protected lazy val tupleSlice = sel(sel(runtimeRef, "Tuple"), "slice")
  protected lazy val tupleGet = sel(sel(runtimeRef, "Tuple"), "get")
  protected lazy val stringStartsWith = sel(sel(runtimeRef, "Str"), "startsWith")
  protected lazy val stringGet = sel(sel(runtimeRef, "Str"), "get")
  protected lazy val stringDrop = sel(sel(runtimeRef, "Str"), "drop")

  /** Make a term that looks like `runtime.Tuple.get(t, i)`. */
  protected final def callTupleGet(t: Term, i: Int, label: Str): Term =
    callTupleGet(t, i, FlowSymbol(label))

  /** Make a term that looks like `runtime.Tuple.slice(t, i)`. */
  protected final def callTupleGet(t: Term, i: Int, s: FlowSymbol): Term =
    app(tupleGet, tup(fld(t), fld(int(i))), s)

  /** Make a term that looks like `runtime.Str.startsWith(t, p)`. */
  protected final def callStringStartsWith(t: Term.Ref, p: Term, label: Str) =
    app(stringStartsWith, tup(fld(t), fld(p)), label)

  /** Make a term that looks like `runtime.Str.get(t, i)`. */
  protected final def callStringGet(t: Term.Ref, i: Int, label: Str) =
    app(stringGet, tup(fld(t), fld(int(i))), label)

  /** Make a term that looks like `runtime.Str.drop(t, n)`. */
  protected final def callStringDrop(t: Term.Ref, n: Int, label: Str) =
    app(stringDrop, tup(fld(t), fld(int(n))), label)

  protected final def tempLet(dbgName: Str, term: Term)(inner: TempSymbol => Split): Split =
    val s = TempSymbol(N, dbgName)
    Split.Let(s, term, inner(s))

  protected final def plainTest(cond: Term, dbgName: Str = "cond")(inner: => Split): Split =
    val s = TempSymbol(N, dbgName)
    Split.Let(s, cond, Branch(s.ref(), inner) ~: Split.End)
  
  protected final def makeMatchResult(captures: Term) =
    app(matchResultClass, tup(fld(captures)), "result of `MatchResult`")
    
  protected final def makeMatchFailure =
    app(matchFailureClass, tup(), "result of `MatchFailure`")

  /** Make a `Branch` that calls `Pattern` symbols' `unapply` functions. */
  def makeLocalPatternBranch(
      scrut: => Term.Ref,
      localPatternSymbol: BlockLocalSymbol,
      inner: => Split,
  )(fallback: Split): Split =
    val call = app(localPatternSymbol.ref().withIArgs(Nil), tup(fld(scrut)), s"result of ${localPatternSymbol.nme}")
    tempLet("matchResult", call): resultSymbol =>
      Branch(resultSymbol.ref().withIArgs(Nil), matchResultPattern(N), inner) ~: fallback

  /** Make a `Branch` that calls `Pattern` symbols' `unapply` functions. */
  protected final def makeUnapplyBranch(
      scrut: => Term.Ref,
      clsTerm: Term,
      inner: => Split,
      method: Str = "unapply"
  )(fallback: Split): Split =
    val call = app(sel(clsTerm, method).withIArgs(Nil), tup(fld(scrut)), s"result of $method")
    tempLet("matchResult", call): resultSymbol =>
      Branch(resultSymbol.ref().withIArgs(Nil), matchResultPattern(N), inner) ~: fallback
  
  /** Make a `Branch` that calls `Pattern` symbols' `unapplyStringPrefix` functions. */
  protected final def makeUnapplyStringPrefixBranch(
      scrut: => Term.Ref,
      clsTerm: Term,
      postfixSymbol: TempSymbol,
      inner: => Split,
      method: Str = "unapplyStringPrefix"
  )(fallback: Split): Split =
    val call = app(sel(clsTerm, method), tup(fld(scrut)), s"result of $method")
    tempLet("matchResult", call): resultSymbol =>
      // let `matchResult` be the return value
      val argSym = TempSymbol(N, "arg")
      // let `arg` be the first element of `matchResult`
      Branch(
        resultSymbol.ref().withIArgs(Nil),
        matchResultPattern(S(argSym :: Nil)),
        Split.Let(postfixSymbol, callTupleGet(argSym.ref().withIArgs(Nil), 0, "postfix"), inner)
      ) ~: fallback
