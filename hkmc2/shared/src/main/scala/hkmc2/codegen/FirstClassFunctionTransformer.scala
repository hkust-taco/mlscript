package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import utils.*
import semantics.*
import syntax.Tree
import semantics.Elaborator.{ctx, State}
import hkmc2.Message.MessageContext

import collection.mutable.HashMap


class FirstClassFunctionTransformer
      (using Elaborator.State, Elaborator.Ctx, Raise, DebugPrinter)
    extends BlockTransformer(new SymbolSubst):
  // Anonymous lambdas' parameter lists cannot be retrieved from the term symbol
  private val funDefns = HashMap.empty[BlockMemberSymbol, FunDefn] 
  class CollectFunDefns extends BlockTraverser:
    override def applyFunDefn(fun: FunDefn) =
      funDefns += (fun.sym -> fun)
      super.applyFunDefn(fun)

  private def generateFCFunctionClass(p: Path, params: LoweredParamList) =
    val clsSym = ClassSymbol(
      syntax.Tree.DummyTypeDef(syntax.Cls),
      syntax.Tree.Ident("Function$")
    )
    val defSym = new BlockMemberSymbol("Function$", Nil, false)
    // The wrapper and the wrapped function each bind their own parameters. Refresh the symbols
    // before building forwarding arguments so each read refers to the wrapper's binding.
    val bindings = collection.mutable.Map.empty[Symbol, Symbol]
    new SymbolRefresherWalker(bindings).refreshParamList(params)
    val wrapperParams = new SymbolMapTransformer(bindings).applyParamList(params)
    val forwarding = OptionalParams.forwarding(wrapperParams, fixedArity = false)
    val callDef = FunDefn.withFreshSymbol(Some(clsSym), new BlockMemberSymbol("call", Nil, true), forwarding.params :: Nil, N,
      Return(Call.of(p, forwarding.args :: Nil)(CallMetadata.defaultMlsFun, N)))(N, annotations = Nil)
    ClsLikeDefn(None, clsSym, defSym, None, syntax.Cls, None, Nil,
      Some(State.globalThisSymbol.asThis.sel(ctx.builtins.Function)),
      callDef :: Nil, Nil, Nil, Assign.discard(
        // The parent is the JavaScript `Function` class, whose constructor is called without arguments.
        Call(State.builtinOpsMap("super").asSimpleRef, Nil :: Nil)(
          ErasedFuncSignature.Signature(ErasedParamList(Nil, N) :: Nil, ErasedResult.Direct(S(ErasedType.Unit))),
          CallMetadata.defaultFun, N),
        End()), End(), None, None, None, methodKeys = Map.empty)(N, annotations = Nil)

  private def getParamList(l: BlockMemberSymbol): Option[LoweredParamList] = funDefns.get(l) match
    case Some(fd) => fd.params.headOption
    case _ => l.tsym.flatMap(getParamList)

  private def getParamList(ts: TermSymbol): Option[LoweredParamList] =
    ts.irFunDefn.flatMap(_.params.headOption).orElse:
      // FIXME: remove this fallback once imported functions have their `irFunDefn` properly linked.
      ts.defn.collectFirst:
        case TermDefinition(k = syntax.Fun, params = params @ (_ :: _)) =>
          LoweredParamList.callingConvention(params.head)
  
  private def isGetter(l: BlockMemberSymbol): Bool = funDefns.get(l) match
    case Some(fd) => fd.params.isEmpty
    case _ => l.tsym.exists(isGetter)
  
  private def isGetter(ts: TermSymbol): Bool =
    ts.irFunDefn.exists(_.params.isEmpty) ||
      // FIXME: remove this fallback once imported functions have their `irFunDefn` properly linked.
      ts.defn.exists:
        case TermDefinition(k = syntax.Fun, params = Nil) => true
        case _ => false
  
  private def etaExpandPath(p: Path, params: LoweredParamList)(k: Path => Block): Block =
    val clsDef = generateFCFunctionClass(p, params)
    val tmp = new TempSymbol(None, initErasedType = S(ErasedType.ValueLike(rsc = S(false), clsDef.isym.asClsOrMod.get)))
    val cls = clsDef.sym.asMemberRef(clsDef.isym)
    Scoped(Set(clsDef.sym, tmp), Define(clsDef, Assign(tmp, Instantiate(false, cls, Nil :: Nil)(InstantiateMetadata.empty, p.toLoc), k(tmp.asSimpleRef.withLoc(p.toLoc)))))
  
  override def applyPath(p: Path)(k: Path => Block): Block = p match
    case ref @ Value.MemberRef(l, disamb) => disamb match
      case s: TermSymbol if s.k is syntax.Fun =>
        if isGetter(l) then k(p)
        else etaExpandPath(ref, getParamList(l).getOrElse(lastWords(s"Cannot get ${l.nme}'s parameter list.")))(k)
      case _ => k(p)
    case sel: Select => sel.symbol match
      case Some(s: TermSymbol) if (s.k is syntax.Fun) => etaExpandMethod(sel, s)(k)
      case Some(_) => k(p)
      case _ =>
        raise(ErrorReport(msg"Cannot determine if ${sel.name.name} is a function." -> sel.toLoc :: Nil,
          source = Diagnostic.Source.Compilation))
        k(p)
    // * A member selected through its runtime key, such as an `@jsSymbol` method, is a method
    // * reference just like a resolved `Select`.
    case DynSelect(_, _, DynSelectKind.Member(s)) if s.k is syntax.Fun => etaExpandMethod(p, s)(k)
    case _ => k(p)
  
  private def etaExpandMethod(p: Path, s: TermSymbol)(k: Path => Block): Block =
    if isGetter(s) then k(p)
    else
      val params = getParamList(s).getOrElse:
        raise:
          ErrorReport(msg"Cannot get ${s.nme}'s parameter list."
            -> p.toLoc :: Nil,
            source = Diagnostic.Source.Compilation)
        LoweredParamList.plain(Nil)(N)
      etaExpandPath(p, params)(k)
  
  /** Whether a call of the resolved member `s` calls a function object that the member holds, as opposed
    * to a function member, which is called directly. */
  private def holdsFunctionObject(s: TermSymbol): Bool = !(s.k is syntax.Fun)

  override def applyResult(r: Result)(k: Result => Block): Block = r match
    // * A member read applies nothing, so its selection is not a function object.
    case Call(_, Nil) => super.applyResult(r)(k)
    case c @ Call(fun, argss) => applyListOf(argss, (args, k2) => applyArgs(args)(k2)): argss2 =>
      def call(f: Path): Block = FirstClassFunctionTransformer.bindCall(c, f, argss2)(k)
      def callObject(obj: Path): Block = FirstClassFunctionTransformer.bindObjectCall(c, obj, argss2)(k)
      fun match
        case ref @ Value.SimpleRef(sym) => sym match
          case _: VarSymbol |  _: TempSymbol => callObject(ref)
          case _ => call(fun)
        case ref @ Value.MemberRef(_, _) => call(fun)
        case sel: Select => sel.symbol match
          case Some(s: TermSymbol) => if holdsFunctionObject(s) then callObject(fun) else call(fun)
          case _ =>
            raise(ErrorReport(msg"Cannot determine if ${sel.name.name} is a function object." -> fun.toLoc :: Nil,
                source = Diagnostic.Source.Compilation))
            call(fun)
        case DynSelect(_, _, DynSelectKind.Member(s)) => if holdsFunctionObject(s) then callObject(fun) else call(fun)
        case s: DynSelect =>
          raise(ErrorReport(msg"Cannot determine if the dynamic selection is a function object." -> s.toLoc :: Nil,
              source = Diagnostic.Source.Compilation))
          call(fun)
        case _ => call(fun)
    case _: Lambda => lastWords("Lambda functions should be rewritten into function definitions first.")
    case _ => super.applyResult(r)(k)
  
  class DesugarMultipleParamList extends BlockTransformer(new SymbolSubst):
    override def applyFunDefn(fd: FunDefn): FunDefn = fd.params match
      case Nil => fd
      case _ :: Nil => fd
      case head :: tail =>
        def rec(params: List[LoweredParamList]): Block = params match
          case head :: rest =>
            val newBody = rec(rest)
            val funSym = new BlockMemberSymbol("lambda$", Nil, false)
            val funDef = FunDefn.withFreshSymbol(None, funSym, head :: Nil, N, newBody)(N, annotations = Nil)
            Scoped(Set(funSym), Define(funDef, Return(funDef.sym.asMemberRef(funDef.dSym))))
          case Nil => fd.body
        // The curried definition keeps its symbol under its new signature (see `TermSymbol.irErasure`).
        val signature = FunDefn.Signature.fromParams(head :: Nil, ErasedResult.fromAnnotations(N, fd.annotations))
        FunDefn(fd.owner, fd.sym, fd.dSym, signature, rec(tail))(fd.configOverride, fd.annotations)
  
  def transform(b: Block): Block =
    val desugared = new DesugarMultipleParamList().applyBlock(b)
    new CollectFunDefns().applyBlock(desugared)
    applyBlock(desugared)

object FirstClassFunctionTransformer:
  /** Binds every call in `block` to the signature that its callee publishes (see [[bindCall]]).
    *
    * Lowering groups the argument lists of a call by the parameter lists written for its callee, which staged
    * code also reflects. The pipeline runs this pass after staging, so that optimizers and backends see calls
    * that follow the conventions of the completed IR definitions, including imported ones.
    */
  def bindCalls(block: Block)(using State): Block =
    new BlockTransformer(SymbolSubst.Id):
      override def applyResult(r: Result)(k: Result => Block): Block = r match
        case c: Call => bindCall(c, c.fun, c.argss)(k)
        case _ => super.applyResult(r)(k)
    .applyBlock(block)
  
  /** Passes to `k` the call `c`, with `fun` as its callee and `argss` as its argument lists, under the signature
    * that `fun` publishes. A callee that publishes no signature keeps the signature of `c`.
    *
    * The function-object transform is the only pass that removes parameter lists from a definition that keeps its
    * symbol: the definition retains its first list and returns a function object for the lists that follow. A
    * callee that publishes fewer parameter lists than `argss` has was therefore transformed, in this compilation
    * unit or in the one that defines it. The call then applies the first list, and each later list applies the
    * `call` method of the object that the previous call returned (see [[applyCurried]]).
    */
  def bindCall(c: Call, fun: Path, argss: Ls[Ls[Arg]])(k: Result => Block)(using State): Block =
    Call.publishedSignature(fun).getOrElse(c.signature) match
      case entry: ErasedFuncSignature if argss.sizeCompare(entry.paramListCount) > 0 =>
        applyCurried(c, fun, argss, entry)(k)
      case target =>
        k(if (fun is c.fun) && (argss is c.argss) && (target is c.signature) then c
          else Call(fun, argss)(target, c.metadata, c.toLoc))
  
  /** Passes to `k` the call `c` of a function value, as a call of the function object `obj` that stands for
    * that value, applying `argss`.
    *
    * The `call` method of a function object takes one parameter list and returns the function object for the
    * lists that follow (see `DesugarMultipleParamList`). The signature of `c` can have several lists, when `c`
    * applies a curried definition through a function value. The call of the method then takes the signature of
    * the application of its first list, and each later list of `argss` applies the `call` method of the object
    * that the previous call returned.
    */
  def bindObjectCall(c: Call, obj: Path, argss: Ls[Ls[Arg]])(k: Result => Block)(using State): Block =
    c.signature match
      case source: ErasedFuncSignature => applyCurried(c, obj.selSN("call"), argss, source.firstApplication)(k)
      case _: ErasedGetterSignature => lastWords("A call that applies argument lists has a function signature")
  
  /** Applies `argss` to `fun`, a definition converted to function objects, whose signature `entry` has a single
    * parameter list. The signature of `c`, which groups the lists as the source definition does, supplies the
    * parameter and result types of the `call` methods.
    */
  private def applyCurried(c: Call, fun: Path, argss: Ls[Ls[Arg]], entry: ErasedFuncSignature)
        (k: Result => Block)(using State): Block =
    assert(entry.paramListCount == 1, "A definition converted to function objects takes one parameter list")
    val source = c.signature match
      case s: ErasedFuncSignature => s
      case _ => lastWords("A curried application needs a function signature")
    def applyLists(callee: Path, signature: ErasedFuncSignature, lists: Ls[Ls[Arg]],
          remainingParams: Ls[ErasedParamList[ErasedValueType]]): Block = lists match
      case args :: Nil => k(Call(callee, args :: Nil)(signature, c.metadata, c.toLoc))
      case args :: rest =>
        val prefix = Call(callee, args :: Nil)(signature, c.metadata.copy(annotations = Nil), c.toLoc)
        val tmp = TempSymbol(N, initErasedType = prefix.erasedType, "callPrefix")
        val result = if remainingParams.tail.isEmpty then source.result
          else ErasedResult.Direct(S(ErasedType.Function(S(false))))
        val next = ErasedFuncSignature.Signature(remainingParams.head :: Nil, result)
        Scoped(Set.single(tmp), Assign(tmp, prefix,
          applyLists(tmp.asSimpleRef.selSN("call"), next, rest, remainingParams.tail)))
      case Nil => lastWords("A curried application needs an argument list")
    applyLists(fun, entry, argss, source.paramLists.tail)
