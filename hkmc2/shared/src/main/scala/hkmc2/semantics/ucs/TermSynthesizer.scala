package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import syntax.Tree, Tree.*, Elaborator.{Ctx, State, ctx}

/** This trait includes some helpers for synthesizing `Term`s which look like 
  * they have already been processed by the `Resolver`. Its methods should only
  * be called in stages after the `Resolver`. Currently, its derived classes are
  * `Normalization`, `Compiler`, and `SplitCompiler`. */
trait TermSynthesizer(using State):
  protected final def sel(p: Term, k: Ident): Term.SynthSel =
    (Term.SynthSel(p, k)(N, N): Term.SynthSel).resolve
  protected final def sel(p: Term, k: Ident, s: FieldSymbol): Term.SynthSel =
    (Term.SynthSel(p, k)(S(s), N): Term.SynthSel).resolve
  protected final def sel(p: Term, k: Str): Term.SynthSel = sel(p, Ident(k): Ident)
  protected final def sel(p: Term, k: Str, s: FieldSymbol): Term.SynthSel = sel(p, Ident(k): Ident, s)
  protected final def int(i: Int) = Term.Lit(IntLit(BigInt(i)))
  protected final def str(s: Str) = Term.Lit(StrLit(s))
  protected final def `null` = Term.Lit(UnitLit(true))
  protected final def fld(t: Term) = Fld(FldFlags.empty, t, N)
  protected final def tup(xs: List[Term]): Term.Tup =
    Term.Tup(xs.iterator.map(fld).toList)(DummyTup)
  protected final def tup(xs: Fld*): Term.Tup = Term.Tup(xs.toList)(DummyTup)
  protected final def app(l: Term, r: Term, label: Str): Term.App = app(l, r, FlowSymbol(label))
  protected final def app(l: Term, r: Term, s: FlowSymbol): Term.App =
    (Term.App(l, r)(App(Dummy, Dummy), N, s): Term.App).resolve
  protected final def rcd(fields: RcdField*): Term.Rcd = Term.Rcd(false, fields.toList)
  
  protected final def splitLet(sym: BlockLocalSymbol, term: Term)(inner: Split): Split =
    Split.Let(sym, term, inner)
  
  protected final def param = Param(FldFlags.empty, _, N, Modulefulness.none)
  protected final def paramList(params: Param*) = PlainParamList(params.toList)
    
  private lazy val runtimeRef: Term.Ref = State.runtimeSymbol.ref().resolve

  /** Make a term that looks like `runtime.MatchSuccess` with its symbol. */
  protected lazy val matchSuccessClass =
    sel(runtimeRef, "MatchSuccess", State.matchSuccessClsSymbol)

  /** Make a pattern that looks like `runtime.MatchSuccess.class`. */
  protected def matchSuccessPattern(parametersOpt: Opt[Ls[BlockLocalSymbol]]): FlatPattern.ClassLike =
    val constructor = sel(matchSuccessClass, "class", State.matchSuccessClsSymbol)
    val parameters = parametersOpt.map(_.map(_ -> N))
    FlatPattern.ClassLike(constructor, State.matchSuccessClsSymbol, parameters, false)(Tree.Dummy)

  /** Make a term that looks like `runtime.MatchFailure` with its symbol. */
  protected lazy val matchFailureClass =
    sel(runtimeRef, "MatchFailure", State.matchFailureClsSymbol)

  /** Make a pattern that looks like `runtime.MatchFailure.class`. */
  protected def matchFailurePattern(parametersOpt: Opt[Ls[BlockLocalSymbol]]): FlatPattern.ClassLike =
    val constructor = sel(matchFailureClass, "class", State.matchFailureClsSymbol)
    val parameters = parametersOpt.map(_.map(_ -> N))
    FlatPattern.ClassLike(constructor, State.matchFailureClsSymbol, parameters, false)(Tree.Dummy)

  protected lazy val tupleSlice = sel(sel(runtimeRef, "Tuple"), "slice")
  protected lazy val tupleLazySlice = sel(sel(runtimeRef, "Tuple"), "lazySlice")
  protected lazy val tupleGet = sel(sel(runtimeRef, "Tuple"), "get")
  protected lazy val stringStartsWith = sel(sel(runtimeRef, "Str"), "startsWith")
  protected lazy val stringGet = sel(sel(runtimeRef, "Str"), "get")
  protected lazy val stringTake = sel(sel(runtimeRef, "Str"), "take")
  protected lazy val stringLeave = sel(sel(runtimeRef, "Str"), "leave")

  /** Make a term that looks like `runtime.Tuple.get(t, i)`. */
  protected final def callTupleGet(t: Term, i: Int, label: Str): Term =
    callTupleGet(t, i, FlowSymbol(label))

  /** Make a term that looks like `runtime.Tuple.slice(t, i)`. */
  protected final def callTupleGet(t: Term, i: Int, s: FlowSymbol): Term =
    app(tupleGet, tup(fld(t), fld(int(i))), s)
  
  /** Make a term that looks like `runtime.Tuple.slice(t, i, j)`. */
  protected final def callTupleSlice(t: Term, i: Int, j: Int, label: Str): Term =
    app(tupleSlice, tup(fld(t), fld(int(i)), fld(int(j))), label)

  /** Make a term that looks like `runtime.Str.startsWith(t, p)`. */
  protected final def callStringStartsWith(t: Term.Ref, p: Term, label: Str) =
    app(stringStartsWith, tup(fld(t), fld(p)), label)

  /** Make a term that looks like `runtime.Str.get(t, i)`. */
  protected final def callStringGet(t: Term.Ref, i: Int, label: Str) =
    app(stringGet, tup(fld(t), fld(int(i))), label)

  /** Make a term that looks like `runtime.Str.drop(t, n)`. */
  protected final def callStringTake(t: Term.Ref, n: Int, label: Str) =
    app(stringTake, tup(fld(t), fld(int(n))), label)
  
  /** Make a term that looks like `runtime.Str.drop(t, n)`. */
  protected final def callStringDrop(t: Term.Ref, n: Int, label: Str) =
    app(stringLeave, tup(fld(t), fld(int(n))), label)

  protected final def tempLet(dbgName: Str, term: Term)(inner: TempSymbol => Split): Split =
    val s = TempSymbol(N, dbgName)
    Split.Let(s, term, inner(s))

  protected final def plainTest(cond: Term, dbgName: Str = "cond")(inner: => Split): Split =
    val s = TempSymbol(N, dbgName)
    Split.Let(s, cond, Branch(s.safeRef, inner) ~: Split.End)
  
  protected final def makeMatchSuccess(output: Term) =
    app(matchSuccessClass, tup(fld(output), fld(rcd())), "result of `MatchSuccess`")
  
  protected final def makeMatchSuccess(output: Term, bindings: Term) =
    app(matchSuccessClass, tup(fld(output), fld(bindings)), "result of `MatchSuccess`")
  
  protected final def makeMatchSuccess(output: Term, fields: Ls[RcdField | RcdSpread]) =
    app(matchSuccessClass, tup(fld(output), fld(Term.Rcd(false, fields))), "result of `MatchSuccess`")
    
  protected final def makeMatchFailure(errors: Term = Term.Lit(UnitLit(true))) =
    app(matchFailureClass, tup(fld(errors)), "result of `MatchFailure`")

  /** Make a `Branch` that calls `Pattern` symbols' `unapply` functions. */
  def makeLocalPatternBranch(
      scrut: => Term.Ref,
      localPatternSymbol: BlockLocalSymbol,
      inner: => Split,
  )(fallback: Split): Split =
    val call = app(localPatternSymbol.safeRef, tup(fld(scrut)), s"result of ${localPatternSymbol.nme}")
    tempLet("matchSuccess", call): resultSymbol =>
      Branch(resultSymbol.safeRef, matchSuccessPattern(N), inner) ~: fallback
  
  protected final def makeTupleBranch(
    scrut: => Term.Ref,
    subScrutinees: Ls[BlockLocalSymbol],
    consequent: => Split,
    alternative: Split
  ): Split =
    Branch(scrut, FlatPattern.Tuple(subScrutinees.size, false),
      subScrutinees.iterator.zipWithIndex.foldRight(consequent):
        case ((arg, index), innerSplit) =>
          val label = s"the $index-th element of the match result"
          Split.Let(arg, callTupleGet(scrut, index, label), innerSplit)
    ) ~: alternative
  
  protected final def makeTupleBranch(
    scrut: => Term.Ref,
    leading: Ls[BlockLocalSymbol],
    spread: BlockLocalSymbol,
    trailing: Ls[BlockLocalSymbol],
    consequent: => Split,
    alternative: Split
  ): Split =
    val split0 = trailing.iterator.zipWithIndex.foldRight(consequent):
      case ((arg, index), innerSplit) =>
        val reverseIndex = trailing.size - index
        val label = s"the last $reverseIndex-th element of the tuple"
        Split.Let(arg, callTupleGet(scrut, -reverseIndex, label), innerSplit)
    val split1 = Split.Let(spread, callTupleSlice(
      scrut, leading.size, trailing.size, "the middle part of the tuple"), split0)
    val split2 = leading.iterator.zipWithIndex.foldRight(split1):
      case ((arg, index), innerSplit) =>
        val label = s"the first ${index + 1}-th element of the tuple"
        Split.Let(arg, callTupleGet(scrut, index, label), innerSplit)
    Branch(scrut, FlatPattern.Tuple(leading.size + trailing.size, true), split2) ~: alternative
