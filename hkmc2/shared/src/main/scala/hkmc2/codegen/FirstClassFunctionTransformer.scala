package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import utils.*
import semantics.*
import syntax.Tree
import semantics.Elaborator.{ctx, State}


class FirstClassFunctionTransformer
      (using Elaborator.State, Elaborator.Ctx, Raise, DebugPrinter)
    extends BlockTransformer(SymbolSubst.Id):
  
  // A binding may also name a class or module. Only the resolved definition identifies the function and its layout.
  // External declarations have no IR body, but still supply the physical layout of their forwarding wrappers.
  private def paramLists(sym: TermSymbol): Opt[Ls[LoweredParamList]] =
    sym.irFunDefn.map(_.params).orElse:
      sym.defn.map(_.params.map(LoweredParamList.callingConvention))
  
  private def function(p: Path): Opt[(TermSymbol, LoweredParamList)] =
    p.targetSymbol.collect { case sym: TermSymbol if sym.k is syntax.Fun => sym }.flatMap: sym =>
      paramLists(sym).flatMap(_.headOption).map(sym -> _)
  
  private def freshParam(p: Param): Param =
    val sym = VarSymbol(p.sym.id, erasedType = p.sym.erasedType, mut = p.sym.mut)
    p.copy(sym = sym)(p.toLoc).withSignTypeOf(p)
  
  private def save(p: Path, name: Str)(k: Path => Block): Block =
    val tmp = TempSymbol(N, initErasedType = p.erasedType, name)
    Scoped(Set.single(tmp), Assign(tmp, p, k(tmp.asSimpleRef.withLocOf(p))))
  
  private def stable(p: Path, name: Str)(k: Path => Block): Block =
    if p.isStable then k(p) else save(p, name)(k)
  
  private def undefined: Path = Value.Lit(Tree.UnitLit(false))(N)
  
  /** Save a receiver before both selecting its function and passing it as the explicit JS receiver.
    * Array indexing produces a value through the runtime's indexing operation, not a JS property reference.
    */
  private def withReceiver(p: Path)(k: (Path, Path) => Block): Block = p match
    case sel: Select => stable(sel.qual, "receiver"): qual =>
      k(sel.copy(qual = qual)(sel.symbol, sel.toLoc)(sel.sanitize), qual)
    case sel: SuperSelect => stable(sel.qual, "receiver"): qual =>
      k(sel.copy(qual = qual)(sel.symbol, sel.toLoc), qual)
    case sel @ DynSelect(qual, fld, kind) if !kind.isArrayIdx => stable(qual, "receiver"): qual =>
      k(sel.copy(qual = qual)(sel.toLoc), qual)
    case cast: CastPath => withReceiver(cast.value): (value, receiver) =>
      k(Cast.path(value, cast.target, cast.check)(cast.toLoc), receiver)
    case _ => k(p, undefined)
  
  private def generateFCFunctionClass(params: LoweredParamList, body: Ls[Arg] => Block) =
    val clsSym = ClassSymbol(
      syntax.Tree.DummyTypeDef(syntax.Cls),
      syntax.Tree.Ident("Function$")
    )
    val defSym = new BlockMemberSymbol("Function$", Nil, false)
    // Forwarding parameters bind independently of the original definition. Optional arguments remain raw so a
    // foreign callee, rather than this wrapper, decides what omitted arguments mean.
    val fresh = params.copy(params = params.params.map(freshParam), restParam = params.restParam.map(freshParam))(params.toLoc)
    val forwarding = OptionalParams.forwarding(fresh, fixedArity = false)
    val thisArg = Param.simple(VarSymbol(Tree.Ident("thisArg"), erasedType = N, mut = false))
    val callParams = forwarding.params.copy(params = thisArg :: forwarding.params.params)(forwarding.params.toLoc)
    // Native functions consume thisArg through Function.prototype.call. A closure already captures its receiver;
    // its call method ignores the explicit argument and uses its own `this` to access captured values.
    val callDef = FunDefn.withFreshSymbol(Some(clsSym), new BlockMemberSymbol("call", Nil, true), callParams :: Nil,
      body(forwarding.args))(N, annotations = Nil)
    ClsLikeDefn(None, clsSym, defSym, None, syntax.Cls, None, Nil,
      Some(State.globalThisSymbol.asThis.sel(ctx.builtins.Function)),
      callDef :: Nil, Nil, Nil, Assign.discard(
        Call(State.builtinOpsMap("super").asSimpleRef, Nil ne_:: Nil)(CallMetadata.defaultFun, N),
        End()), End(), None, None, None, methodKeys = Map.empty)(N, annotations = Nil)
  
  private def etaExpand(p: Path, sym: TermSymbol, params: LoweredParamList)(k: Path => Block): Block =
    // Methods in a declared class may lack their own declare modifier; only an implementation promises
    // the MLscript result convention. Generated functions supply that implementation through their IR definition.
    val isMlsFun = sym.irFunDefn.isDefined || sym.defn.exists(d =>
      d.hasDeclareModifier.isEmpty && (d.body.isDefined || sym.isInstanceOf[ClassCtorSymbol]))
    val metadata = CallMetadata(isMlsFun, true, Nil)
    def wrap(body: Ls[Arg] => Block): Block =
      val clsDef = generateFCFunctionClass(params, body)
      val tmp = TempSymbol(N, initErasedType = S(ErasedType.ValueLike(rsc = S(false), clsDef.isym.asClsOrMod.get)), "function")
      Scoped(Set(clsDef.sym, tmp), Define(clsDef,
        Assign(tmp, Instantiate(false, clsDef.sym.asMemberRef(clsDef.isym), Nil :: Nil)(InstantiateMetadata.empty, p.toLoc),
          k(tmp.asSimpleRef.withLocOf(p)))))
    p match
      case _: Value.MemberRef => wrap(args => Return(Call(p, args ne_:: Nil)(metadata, p.toLoc)))
      case _ => withReceiver(p): (callee, receiver) =>
        // Reading a method value binds both the current function and its receiver now, even if the receiver variable
        // or a foreign method property changes before the closure is invoked.
        save(callee, "method"): method =>
          val thisArg = if sym.owner.isEmpty then undefined else receiver
          wrap(args => Return(Call(method.selSN("call"), (thisArg.asArg :: args) ne_:: Nil)(metadata, p.toLoc)))
  
  override def applyPath(p: Path)(k: Path => Block): Block =
    super.applyPath(p): p2 =>
      function(p2) match
        case S((sym, params)) => etaExpand(p2, sym, params)(k)
        case N => k(p2)
  
  override def applyResult(r: Result)(k: Result => Block): Block = r match
    case c @ Call(fun, argss) =>
      // Transform the receiver and computed key without turning the callee itself into a function object.
      super.applyPath(fun): fun2 =>
        val direct = fun2 match
          case Value.SimpleRef(_: BuiltinSymbol) => true
          case _ => function(fun2).isDefined
        if direct then applyArgss(argss): argss2 =>
          k(if (fun2 is fun) && (argss2 is argss) then c else Call(fun2, argss2)(c.metadata, c.toLoc))
        else
          // Lowering separates applications of unknown callees. Each returned function value needs its own
          // dispatch through `.call`, since it may be a native function or a generated closure.
          softAssert(argss.tail.isEmpty, "Unknown callees must be lowered to separate calls")
          withReceiver(fun2): (callee, receiver) =>
            // Preserve callee lookup before transformations of argument values introduce their own bindings.
            save(callee, "callee"): callee =>
              applyArgs(argss.head): args =>
                k(Call(callee.selSN("call"), (receiver.asArg :: args) ne_:: Nil)(c.metadata, c.toLoc))
    case _: Lambda => lastWords("Lambda functions should be rewritten into function definitions first.")
    case _ => super.applyResult(r)(k)
  
  // Preserve curried signatures and multi-calls for saturation analysis, inlining, and worker-wrapper optimization.
  // Escaping partial applications return native functions, which accept the same `.call(thisArg, ...)` convention.
  def transform(b: Block): Block = applyBlock(b)
