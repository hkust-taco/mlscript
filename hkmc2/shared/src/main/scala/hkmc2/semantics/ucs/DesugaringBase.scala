package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.Tree.*, Elaborator.{Ctxl, ctx}

/** Contains some helpers that makes UCS desugaring easier. */
trait DesugaringBase(using state: Elaborator.State):
  val elaborator: Elaborator

  import elaborator.tl.*, state.globalThisSymbol

  protected transparent inline def sel(p: Term, k: Ident): Term.SynthSel = Term.SynthSel(p, k)(N)
  protected transparent inline def sel(p: Term, k: Ident, s: FieldSymbol): Term.SynthSel = Term.SynthSel(p, k)(S(s))
  protected transparent inline def sel(p: Term, k: Str): Term.SynthSel = sel(p, Ident(k): Ident)
  protected transparent inline def sel(p: Term, k: Str, s: FieldSymbol): Term.SynthSel = sel(p, Ident(k): Ident, s)
  protected transparent inline def int(i: Int) = Term.Lit(IntLit(BigInt(i)))
  protected transparent inline def str(s: Str) = Term.Lit(StrLit(s))
  protected transparent inline def fld(t: Term) = Fld(FldFlags.empty, t, N)
  protected transparent inline def tup(xs: Fld*): Term.Tup = Term.Tup(xs.toList)(Tup(Nil))
  protected transparent inline def app(l: Term, r: Term, label: Str): Term.App = app(l, r, FlowSymbol(label))
  protected transparent inline def app(l: Term, r: Term, s: FlowSymbol): Term.App = Term.App(l, r)(App(Empty(), Empty()), s)

  /** Get the class symbol defined in the `Predef` module. */
  protected def resolvePredefMember(name: Str): Ctxl[(Term.SynthSel, ClassSymbol)] =
    val predefSymbol = ctx.Builtins.Predef
    val innerSel = sel(globalThisSymbol.ref(), "Predef", predefSymbol)
    val memberSymbol = predefSymbol.tree.definedSymbols.get(name).flatMap(_.asCls).getOrElse:
      lastWords(s"Cannot resolve `$name` in `Predef`.")
    (sel(innerSel, name, memberSymbol), memberSymbol)

  /** Make a term looks like `globalThis.Predef.MatchResult` with its symbol. */
  protected lazy val matchResultClass: Ctxl[(Term.SynthSel, ClassSymbol)] = resolvePredefMember("MatchResult")

  /** Make a pattern looks like `globalThis.Predef.MatchResult.class`. */
  protected def matchResultPattern(parameters: Opt[List[BlockLocalSymbol]]): Ctxl[Pattern.ClassLike] =
    val (classRef, classSym) = matchResultClass
    val classSel = Term.SynthSel(matchResultClass._1, Ident("class"))(S(classSym))
    Pattern.ClassLike(classSym, classSel, parameters, false)(Empty())

  /** Make a term looks like `globalThis.Predef.MatchFailure` with its symbol. */
  protected lazy val matchFailureClass: Ctxl[(Term.SynthSel, ClassSymbol)] = resolvePredefMember("MatchFailure")

  /** Make a pattern looks like `globalThis.Predef.MatchFailure.class`. */
  protected def matchFailurePattern(parameters: Opt[List[BlockLocalSymbol]]): Ctxl[Pattern.ClassLike] =
    val (classRef, classSym) = matchResultClass
    val classSel = Term.SynthSel(matchResultClass._1, Ident("class"))(S(classSym))
    Pattern.ClassLike(classSym, classSel, parameters, false)(Empty())

  /** Create a term that selects a method in the `Predef` module. */
  protected transparent inline def selectPredefMethod =
    sel(sel(globalThisSymbol.ref(), "Predef"), _: Str)

  protected lazy val tupleSlice = selectPredefMethod("tupleSlice")
  protected lazy val tupleGet = selectPredefMethod("tupleGet")
  protected lazy val stringStartsWith = selectPredefMethod("stringStartsWith")
  protected lazy val stringGet = selectPredefMethod("stringGet")
  protected lazy val stringDrop = selectPredefMethod("stringDrop")

  /** Make a term that looks like `tupleGet(t, i)`. */
  protected transparent inline def callTupleGet(t: Term, i: Int, label: Str): Ctxl[Term] =
    callTupleGet(t, i, FlowSymbol(label))

  /** Make a term that looks like `tupleGet(t, i)`. */
  protected transparent inline def callTupleGet(t: Term, i: Int, s: FlowSymbol): Ctxl[Term] =
    app(tupleGet, tup(fld(t), fld(int(i))), s)

  /** Make a term that looks like `stringStartsWith(t, p)`. */
  protected transparent inline def callStringStartsWith(t: Term, p: Term, label: Str): Ctxl[Term] =
    app(stringStartsWith, tup(fld(t), fld(p)), FlowSymbol(label))

  /** Make a term that looks like `stringStartsWith(t, i)`. */
  protected transparent inline def callStringGet(t: Term, i: Int, label: Str): Ctxl[Term] =
    app(stringGet, tup(fld(t), fld(int(i))), FlowSymbol(label))

  /** Make a term that looks like `stringStartsWith(t, n)`. */
  protected transparent inline def callStringDrop(t: Term, n: Int, label: Str): Ctxl[Term] =
    app(stringDrop, tup(fld(t), fld(int(n))), FlowSymbol(label))

  protected transparent inline def tempLet(dbgName: Str, term: Term)(inner: TempSymbol => Split): Split =
    val s = TempSymbol(N, dbgName)
    Split.Let(s, term, inner(s))

  protected transparent inline def plainTest(cond: Term, dbgName: Str = "cond")(inner: => Split): Split =
    val s = TempSymbol(N, dbgName)
    Split.Let(s, cond, Branch(s.ref(), inner) ~: Split.End)

  /** Make a `Branch` that calls `Pattern` symbols' `unapply` functions. */
  def makeUnapplyBranch(
      scrut: => Term.Ref,
      psym: PatternSymbol,
      inner: => Split,
      method: Str = "unapply"
  )(fallback: Split): Ctxl[Split] =
    val func = sel(sel(globalThisSymbol.ref(), psym.nme, psym), method)
    val call = app(func, tup(fld(scrut)), FlowSymbol(s"result of $method"))
    tempLet("matchResult", call): resultSymbol =>
      Branch(resultSymbol.ref(), matchResultPattern(N), inner) ~: fallback

  /** Make a `Branch` that calls `Pattern` symbols' `unapplyStringPrefix` functions. */
  def makeUnapplyStringPrefixBranch(
      scrut: => Term.Ref,
      psym: PatternSymbol,
      inner: TempSymbol => Split,
      method: Str = "unapplyStringPrefix"
  )(fallback: Split): Ctxl[Split] =
    val func = sel(sel(globalThisSymbol.ref(), psym.nme, psym), method)
    val call = app(func, tup(fld(scrut)), FlowSymbol(s"result of $method"))
    tempLet("matchResult", call): resultSymbol =>
      val argSym = TempSymbol(N, "arg")
      Branch(
        resultSymbol.ref(),
        matchResultPattern(S(argSym :: Nil)),
        tempLet("postfix", callTupleGet(argSym.ref(), 0, "postfix"))(inner)
      ) ~: fallback
