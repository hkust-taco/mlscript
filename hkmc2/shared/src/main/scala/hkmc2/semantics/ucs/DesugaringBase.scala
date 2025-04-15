package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.Tree.*, Elaborator.{Ctxl, ctx}, Elaborator.State

/** Contains some helpers that makes UCS desugaring easier. */
trait DesugaringBase(using state: State):
  val elaborator: Elaborator

  import elaborator.tl.*

  protected final def sel(p: Term, k: Ident): Term.SynthSel = Term.SynthSel(p, k)(N)
  protected final def sel(p: Term, k: Ident, s: FieldSymbol): Term.SynthSel = Term.SynthSel(p, k)(S(s))
  protected final def sel(p: Term, k: Str): Term.SynthSel = sel(p, Ident(k): Ident)
  protected final def sel(p: Term, k: Str, s: FieldSymbol): Term.SynthSel = sel(p, Ident(k): Ident, s)
  protected final def int(i: Int) = Term.Lit(IntLit(BigInt(i)))
  protected final def str(s: Str) = Term.Lit(StrLit(s))
  protected final def fld(t: Term) = Fld(FldFlags.empty, t, N)
  protected final def tup(xs: Fld*): Term.Tup = Term.Tup(xs.toList)(Tup(Nil))
  protected final def app(l: Term, r: Term, label: Str): Term.App = app(l, r, FlowSymbol(label))
  protected final def app(l: Term, r: Term, s: FlowSymbol): Term.App = Term.App(l, r)(App(Empty(), Empty()), s)

  /** Make a term that looks like `runtime.MatchResult` with its symbol. */
  protected lazy val matchResultClass: Ctxl[(Term.Sel | Term.SynthSel, ClassSymbol)] =
    (State.runtimeSymbol.ref().selNoSym("MatchResult", synth=true), State.matchResultClsSymbol)

  /** Make a pattern that looks like `runtime.MatchResult.class`. */
  protected def matchResultPattern(parameters: Opt[List[BlockLocalSymbol]]): Ctxl[Pattern.ClassLike] =
    val (classRef, classSym) = matchResultClass
    val classSel = Term.SynthSel(classRef, Ident("class"))(S(classSym))
    Pattern.ClassLike(classSym, classSel, parameters, false)(Empty())

  /** Make a term that looks like `runtime.MatchFailure` with its symbol. */
  protected lazy val matchFailureClass: Ctxl[(Term.Sel | Term.SynthSel, ClassSymbol)] =
    (State.runtimeSymbol.ref().selNoSym("MatchFailure", synth=true), State.matchFailureClsSymbol)

  /** Make a pattern that looks like `runtime.MatchFailure.class`. */
  protected def matchFailurePattern(parameters: Opt[List[BlockLocalSymbol]]): Ctxl[Pattern.ClassLike] =
    val (classRef, classSym) = matchResultClass
    val classSel = Term.SynthSel(classRef, Ident("class"))(S(classSym))
    Pattern.ClassLike(classSym, classSel, parameters, false)(Empty())

  protected lazy val tupleSlice = sel(sel(state.runtimeSymbol.ref(), "Tuple"), "slice")
  protected lazy val tupleGet = sel(sel(state.runtimeSymbol.ref(), "Tuple"), "get")
  protected lazy val stringStartsWith = sel(sel(state.runtimeSymbol.ref(), "Str"), "startsWith")
  protected lazy val stringGet = sel(sel(state.runtimeSymbol.ref(), "Str"), "get")
  protected lazy val stringDrop = sel(sel(state.runtimeSymbol.ref(), "Str"), "drop")

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
    app(matchResultClass._1, tup(fld(captures)), FlowSymbol("result of `MatchResult`"))
    
  def makeMatchFailure(using Elaborator.Ctx) =
    app(matchFailureClass._1, tup(), FlowSymbol("result of `MatchFailure`"))
  
  /** Make a `Branch` that calls `Pattern` symbols' `unapply` functions. */
  def makeLocalPatternBranch(
      scrut: => Term.Ref,
      localPatternSymbol: BlockLocalSymbol,
      inner: => Split,
  )(fallback: Split): Ctxl[Split] =
    val call = app(localPatternSymbol.ref(), tup(fld(scrut)), FlowSymbol(s"result of ${localPatternSymbol.nme}"))
    tempLet("matchResult", call): resultSymbol =>
      Branch(resultSymbol.ref(), matchResultPattern(N), inner) ~: fallback

  /** Make a `Branch` that calls `Pattern` symbols' `unapply` functions. */
  def makeUnapplyBranch(
      scrut: => Term.Ref,
      clsTerm: Term,
      inner: => Split,
      method: Str = "unapply"
  )(fallback: Split): Ctxl[Split] =
    val call = app(sel(clsTerm, method), tup(fld(scrut)), FlowSymbol(s"result of $method"))
    tempLet("matchResult", call): resultSymbol =>
      Branch(resultSymbol.ref(), matchResultPattern(N), inner) ~: fallback

  /** Make a `Branch` that calls `Pattern` symbols' `unapplyStringPrefix` functions. */
  def makeUnapplyStringPrefixBranch(
      scrut: => Term.Ref,
      clsTerm: Term,
      inner: TempSymbol => Split,
      method: Str = "unapplyStringPrefix"
  )(fallback: Split): Ctxl[Split] =
    val call = app(sel(clsTerm, method), tup(fld(scrut)), FlowSymbol(s"result of $method"))
    tempLet("matchResult", call): resultSymbol =>
      val argSym = TempSymbol(N, "arg")
      Branch(
        resultSymbol.ref(),
        matchResultPattern(S(argSym :: Nil)),
        tempLet("postfix", callTupleGet(argSym.ref(), 0, "postfix"))(inner)
      ) ~: fallback
