package hkmc2
package semantics
package ucs

import hkmc2.utils.*, shorthands.*
import syntax.Tree, Tree.*, Elaborator.{Ctx, State, ctx}

/** Build matcher terms after resolution. Nominal references carry their known
  * targets; accesses to generated records and pattern protocols use structural
  * lookup. These terms are lowered directly, without another resolution pass. */
trait TermSynthesizer(using State):
  protected final def ref(target: DefinitionSymbol[?]): Term.MemberRef =
    val member = target.bms.getOrElse(lastWords("A generated member reference requires a block member"))
    val ref = new Term.MemberRef(member)(N, FlowSymbol.memSym(member))
    ref.resolvedTargets = target :: Nil
    ref
  
  /** These fields have runtime names but no nominal member declarations.
    * Their receivers are generated records/pattern objects, or strings guarded
    * by prefix matching before their length is read. */
  protected final def sel(p: Term, k: Ident): Term.NewSel =
    val sel = new Term.NewSel(p, k, N)(FlowSymbol.synthSel(k.name))
    sel.hasDynamicTarget = true
    sel
  protected final def sel(p: Term, k: Str): Term.NewSel = sel(p, Ident(k): Ident)
  protected final def sel(p: Term, target: DefinitionSymbol[?]): Term.NewSel =
    val member = target.bms.getOrElse(lastWords("A generated member selection requires a block member"))
    val sel = new Term.NewSel(p, Ident(member.nme), N)(FlowSymbol.synthSel(member.nme))
    sel.resolvedTargets = target :: Nil
    sel.resolvedMembers = member :: Nil
    sel
  protected final def int(i: Int) = Term.Lit(IntLit(BigInt(i)))
  protected final def str(s: Str) = Term.Lit(StrLit(s))
  protected final def `null` = Term.Lit(UnitLit(true))
  protected final def fld(t: Term) = Fld(FldFlags.empty, t, N)
  protected final def tup(xs: List[Term]): Term.Tup =
    Term.Tup(xs.iterator.map(fld).toList)(DummyTup)
  protected final def tup(xs: Fld*): Term.Tup = Term.Tup(xs.toList)(DummyTup)
  protected final def app(l: Term, r: Term, label: Str): Term.App = app(l, r, FlowSymbol(label))
  protected final def app(l: Term, r: Term, s: FlowSymbol): Term.App =
    Term.App(l, r)(App(Dummy, Dummy), N, s)
  protected final def `new`(cls: Term, args: Ls[Term], label: Str): Term.New = 
    Term.New(cls, args, N)(FlowSymbol.neww(), N)
  protected final def rcd(fields: RcdField*): Term.Rcd = Term.Rcd(false, fields.toList)
  
  protected final def splitLet(sym: LocalVarSymbol, term: Term)(inner: Split): Split =
    Split.Let(sym, term, inner)
  
  protected final def param = Param.simple
  protected final def paramList(params: Param*) = PlainParamList(params.toList)(N)
    
  private lazy val runtimeRef: Term.SimpleRef = Term.SimpleRef(State.runtimeSymbol)(N)

  /** Make a term that looks like `runtime.MatchSuccess` with its symbol. */
  protected lazy val matchSuccessClass =
    sel(runtimeRef, State.matchSuccessClsSymbol)

  /** Make a pattern that looks like `runtime.MatchSuccess.class`. */
  protected def matchSuccessPattern(parametersOpt: Opt[Ls[LocalVarSymbol]]): FlatPattern.ClassLike =
    val parameters = parametersOpt.map(_.map(_ -> N))
    FlatPattern.ClassLike(matchSuccessClass, State.matchSuccessClsSymbol, parameters, false)(Tree.Dummy)

  /** Make a term that looks like `runtime.MatchFailure` with its symbol. */
  protected lazy val matchFailureClass =
    sel(runtimeRef, State.matchFailureClsSymbol)

  /** Make a pattern that looks like `runtime.MatchFailure.class`. */
  protected def matchFailurePattern(parametersOpt: Opt[Ls[LocalVarSymbol]]): FlatPattern.ClassLike =
    val parameters = parametersOpt.map(_.map(_ -> N))
    FlatPattern.ClassLike(matchFailureClass, State.matchFailureClsSymbol, parameters, false)(Tree.Dummy)

  protected lazy val tupleSlice = sel(sel(runtimeRef, State.tupleSymbol), State.tupleSliceSymbol)
  protected lazy val tupleLazySlice = sel(sel(runtimeRef, State.tupleSymbol), State.tupleLazySliceSymbol)
  protected lazy val tupleGet = sel(sel(runtimeRef, State.tupleSymbol), State.tupleGetSymbol)
  protected lazy val stringStartsWith = sel(sel(runtimeRef, State.strSymbol), State.strStartsWithSymbol)
  protected lazy val stringGet = sel(sel(runtimeRef, State.strSymbol), State.strGetSymbol)
  protected lazy val stringTake = sel(sel(runtimeRef, State.strSymbol), State.strTakeSymbol)
  protected lazy val stringLeaveOut = sel(sel(runtimeRef, State.strSymbol), State.strLeaveOutSymbol)

  /** Make a term that looks like `runtime.Tuple.get(t, i)`. */
  protected final def callTupleGet(t: Term, i: Int, label: Str): Term =
    callTupleGet(t, i, FlowSymbol(label))

  /** Make a term that looks like `runtime.Tuple.get(t, i)`. */
  protected final def callTupleGet(t: Term, i: Int, s: FlowSymbol): Term =
    app(tupleGet, tup(fld(t), fld(int(i))), s)
  
  /** Make a term that looks like `runtime.Tuple.slice(t, i, j)`. */
  protected final def callTupleSlice(t: Term, i: Int, j: Int, label: Str): Term =
    app(tupleSlice, tup(fld(t), fld(int(i)), fld(int(j))), label)

  /** Make a term that looks like `runtime.StrOps.startsWith(t, p)`. */
  protected final def callStringStartsWith(t: Term.SimpleRef, p: Term, label: Str) =
    app(stringStartsWith, tup(fld(t), fld(p)), label)

  /** Make a term that looks like `runtime.StrOps.get(t, i)`. */
  protected final def callStringGet(t: Term.SimpleRef, i: Int, label: Str) =
    app(stringGet, tup(fld(t), fld(int(i))), label)

  /** Make a term that looks like `runtime.StrOps.take(t, n)`. */
  protected final def callStringTake(t: Term.SimpleRef, n: Int, label: Str) =
    app(stringTake, tup(fld(t), fld(int(n))), label)
  
  /** Make a term that looks like `runtime.StrOps.leaveOut(t, n)`. */
  protected final def callStringDrop(t: Term.SimpleRef, n: Int, label: Str) =
    app(stringLeaveOut, tup(fld(t), fld(int(n))), label)

  protected final def tempLet(dbgName: Str, term: Term)(inner: TempSymbol => Split): Split =
    val s = TempSymbol(N, erasedType = N, dbgName)
    Split.Let(s, term, inner(s))

  protected final def plainTest(cond: Term, dbgName: Str = "cond")(inner: => Split): Split =
    val s = TempSymbol(N, erasedType = N, dbgName)
    Split.Let(s, cond, Branch(s.safeRef, inner) ~: Split.End)

  protected final def makeBindings(fields: Ls[RcdField | RcdSpread]): Term =
    if fields.isEmpty then `null` else Term.Rcd(false, fields)
  
  protected final def makeMatchSuccess(output: Term) =
    `new`(matchSuccessClass, tup(fld(output), fld(`null`)) :: Nil, "result of `MatchSuccess`")
  
  protected final def makeMatchSuccess(output: Term, bindings: Term) =
    `new`(matchSuccessClass, tup(fld(output), fld(bindings)) :: Nil, "result of `MatchSuccess`")
  
  protected final def makeMatchSuccess(output: Term, fields: Ls[RcdField | RcdSpread]) =
    `new`(matchSuccessClass, tup(fld(output), fld(makeBindings(fields))) :: Nil, "result of `MatchSuccess`")
    
  protected final def makeMatchFailure(errors: Term = Term.Lit(UnitLit(true))) =
    `new`(matchFailureClass, tup(fld(errors)) :: Nil, "result of `MatchFailure`")

  /** Make a `Branch` that calls `Pattern` symbols' `unapply` functions. */
  def makeLocalPatternBranch(
      scrut: => Term.SimpleRef,
      localPatternSymbol: LocalVarSymbol,
      inner: => Split,
  )(fallback: Split): Split =
    val call = app(localPatternSymbol.safeRef, tup(fld(scrut)), s"result of ${localPatternSymbol.nme}")
    tempLet("matchSuccess", call): resultSymbol =>
      Branch(resultSymbol.safeRef, matchSuccessPattern(N), inner) ~: fallback
  
  protected final def makeTupleBranch(
    scrut: => Term.SimpleRef,
    subScrutinees: Ls[LocalVarSymbol],
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
    scrut: => Term.SimpleRef,
    leading: Ls[LocalVarSymbol],
    spread: LocalVarSymbol,
    trailing: Ls[LocalVarSymbol],
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
