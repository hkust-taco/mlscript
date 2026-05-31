package hkmc2
package semantics


import scala.collection.mutable
import scala.annotation.tailrec
import scala.language.implicitConversions

import mlscript.utils.*, shorthands.*
import utils.TraceLogger

import syntax.*
import Tree.*
import BracketKind.*
import Term.{ Blk, Rcd }
import hkmc2.Message.MessageContext

import Keyword.{`let`, `set`}
import hkmc2.utils.Scope


object Elaborator:
  
  val binaryOps = Set(
    ",", // * Not currently used directly; but `;` (below) maps to it
    "+", "-", "*", "/", "%",
    "==", "!=", "<", "<=", ">", ">=",
    "===", "!==",
    "&&", "||")
  val unaryOps = Set("-", "+", "!", "~", "typeof")
  val anyOps = Set("super")
  val builtins = binaryOps ++ unaryOps ++ anyOps
  val aliasOps = Map(
    ";" -> ",",
    "+." -> "+",
    "-." -> "-",
    "*." -> "*",
    "/." -> "/")
  private val builtinBinOps = aliasOps ++ (binaryOps.map: op =>
    op -> op).toMap

  val reservedNames = binaryOps.toSet ++ aliasOps.keySet + "NaN" + "Infinity"
  
  // TODO: rename to ScopeKind?
  enum OuterCtx:
    case Function(returnHandlerSymbol: TempSymbol)
    case InnerScope(innerSymbol: InnerSymbol)
    case LocalScope(nameHint: Str)
    case LambdaOrHandlerBlock
    case NonReturnContext
    
    def showDbg: Str = this match
      case Function(sym) => s"fun:${sym.nme}"
      case InnerScope(inner) => inner.toString
      case LocalScope(hint) => hint
      case LambdaOrHandlerBlock => "LambdaOrHandlerBlock"
      case NonReturnContext => "NonReturnContext"
    
    def inner: Opt[InnerSymbol] = this match
      case InnerScope(inner) => S(inner)
      case _ => N
  
  /** Label metadata threaded through elaboration. */
  final case class LabelBinding(
      labelSymbol: LabelSymbol,
      resultSymbol: TempSymbol,
      nonLocalHandlerSymbol: TempSymbol,
      nonLocalBreakMethodMarker: TempSymbol,
      nonLocalContinueMethodMarker: TempSymbol,
  )
  
  /** Result of label lookup:
    * - `Found`: label is in direct lexical scope
    * - `AcrossBoundary`: label exists but crossing function/lambda/handler boundaries is required
    * - `NotFound`: no such label
    */
  enum LabelLookup:
    case Found(binding: LabelBinding)
    case AcrossBoundary(binding: LabelBinding)
    case NotFound
  
  enum ReturnHandler:
    case Required(handler: TempSymbol)
    case Direct
    case NotInFunction
    case Forbidden
  
  /** Context used to keep track of underscores representing lambda shorthands, eg in `_ + 1`. */
  // TODO later: use TempSymbol instead of VarSymbol? (currently, trying that creates lot of problems)
  class UnderCtx(val unders: Opt[mutable.ArrayBuffer[VarSymbol]])
  
  case class Ctx(
      outer: OuterCtx,
      parent: Opt[Ctx],
      env: Map[Str, Ctx.Elem],
      mode: Mode,
      labels: Map[LabelSymbol, LabelBinding],
  ):
    
    override def toString: Str = s"${parent.fold("")(_.toString+"/")}${outer.showDbg}"
    
    lazy val scope: SrcScope = SrcScope(outer, parent.map(_.scope))
    
    def +(local: Str -> Symbol): Ctx =
      copy(env = env + local.mapSecond(Ctx.RefElem(_)))
    def ++(locals: IterableOnce[Str -> Symbol]): Ctx =
      copy(env = env ++ locals.mapValues(Ctx.RefElem(_)))
    def elem_++(locals: IterableOnce[Str -> Ctx.Elem]): Ctx =
      copy(env = env ++ locals.iterator.filter: kv =>
        // * Imports should not shadow symbols defined in the same scope;
        // * but they should be allowed to shadow previous imports.
        env.get(kv._1).forall(_.isImport))
    
    def withMembers(members: Iterable[Str -> MemberSymbol]): Ctx =
      copy(env = env ++ members.map:
        case (nme, sym) =>
          val elem = outer.inner match
            case S(outer) => Ctx.SelElem(outer, sym.nme, S(sym), isImport = false)
            case N => Ctx.RefElem(sym)
          nme -> elem
      )
    
    def withLabel(
        labelSym: LabelSymbol,
        resultSym: TempSymbol,
        nonLocalHandlerSym: TempSymbol,
        nonLocalBreakMethodMarker: TempSymbol,
        nonLocalContinueMethodMarker: TempSymbol,
    ): Ctx =
      copy(
        env = env + (labelSym.nme -> Ctx.RefElem(labelSym)),
        labels = labels + (labelSym -> LabelBinding(
          labelSym, resultSym, nonLocalHandlerSym, nonLocalBreakMethodMarker, nonLocalContinueMethodMarker))
      )
    
    def nest(outerCtx: OuterCtx): Ctx = Ctx(outerCtx, Some(this), Map.empty, mode, Map.empty)
    def nestLocal(nameHint: Str): Ctx = nest(OuterCtx.LocalScope(nameHint))
    def nestInner(inner: InnerSymbol): Ctx = nest(OuterCtx.InnerScope(inner))
    
    def get(name: Str): Opt[Ctx.Elem] =
      env.get(name).orElse(parent.flatMap(_.get(name)))
    def lookupLabel(name: Str): LabelLookup =
      @tailrec
      def go(
          current: Opt[Ctx],
          crossedFunction: Bool,
          crossedLambdaOrHandler: Bool,
      ): LabelLookup = current match
        case N => LabelLookup.NotFound
        case S(ctx) =>
          ctx.env.get(name) match
            case S(elem) =>
              elem.symbol match
                case S(labelSym: LabelSymbol) =>
                  ctx.labels.get(labelSym) match
                    case S(binding) =>
                      if crossedFunction || crossedLambdaOrHandler
                      then LabelLookup.AcrossBoundary(binding)
                      else LabelLookup.Found(binding)
                    case N =>
                      // Defensive internal consistency check. This path should be unreachable:
                      // every label inserted into `env` via `withLabel` is inserted into
                      // `labels` in the same step. If this fires, context construction is broken.
                      lastWords(s"Missing label binding for symbol ${labelSym.nme} in context ${ctx.outer.showDbg}.")
                case _ =>
                  LabelLookup.NotFound
            case N =>
              val nextCrossedFunction = crossedFunction || (ctx.outer match
                case _: OuterCtx.Function => true
                case _ => false)
              val nextCrossedLambdaOrHandler = crossedLambdaOrHandler || (ctx.outer match
                case OuterCtx.LambdaOrHandlerBlock => true
                case _ => false)
              go(ctx.parent, nextCrossedFunction, nextCrossedLambdaOrHandler)
      go(S(this), false, false)
    def getOuter: Opt[InnerSymbol] = outer.inner.orElse(parent.flatMap(_.getOuter))
    def getNonLocalRetHandler: Opt[TempSymbol] = outer match
      case OuterCtx.Function(sym) => S(sym)
      case _ => parent.flatMap(_.getNonLocalRetHandler)
    def getRetHandler: ReturnHandler = outer match
      case OuterCtx.Function(sym) => ReturnHandler.Direct
      case _: (OuterCtx.LambdaOrHandlerBlock.type | OuterCtx.InnerScope) =>
        getNonLocalRetHandler.fold(ReturnHandler.NotInFunction)(ReturnHandler.Required(_))
      case OuterCtx.NonReturnContext => ReturnHandler.Forbidden
      case _: OuterCtx.LocalScope =>
        parent.fold(ReturnHandler.NotInFunction)(_.getRetHandler)
    
    // * Invariant: We expect that the top-level context only contain hard-coded symbols like `globalThis`
    // * and that built-in symbols like Int and Str be imported into another nested context on top of it.
    // * It should not be possible to shadow these built-in symbols, so user code should always be compiled
    // * in further nested contexts.
    lazy val preludeCtx: Ctx =
      parent match
      case N => lastWords("Cannot find prelude context.")
      case S(par) => if par.parent.isEmpty then this else par.preludeCtx
    
    // * Method `getBuiltin` is used to look up built-in symbols in the context of builtin symbols.
    def getBuiltin(nme: Str): Opt[Ctx.Elem] =
      preludeCtx.env.get(nme)
    
    lazy val builtins: Ctx#MkBuiltins = preludeCtx.MkBuiltins
    private object MkBuiltins extends MkBuiltins
    
    class MkBuiltins:
      assert(Ctx.this is preludeCtx)
      private def assumeBuiltin(nme: Str): Symbol =
        getBuiltin(nme)
          .getOrElse(throw new NoSuchElementException(s"builtin $nme not in ${parent.map(_.env.keySet)}"))
          .symbol.getOrElse(throw new NoSuchElementException(s"builtin symbol $nme"))
      private def assumeBuiltinTpe(nme: Str): TypeSymbol =
        assumeBuiltin(nme).asTpe.getOrElse(throw new NoSuchElementException(
          s"builtin type symbol $nme"))
      private def assumeBuiltinCls(nme: Str): ClassSymbol =
        assumeBuiltin(nme).asCls.getOrElse(throw new NoSuchElementException(
          s"builtin class symbol $nme"))
      private def assumeBuiltinObj(nme: Str): ModuleOrObjectSymbol =
        assumeBuiltin(nme).asObj.getOrElse(throw new NoSuchElementException(
          s"builtin object symbol $nme"))
      private def assumeBuiltinMod(nme: Str): ModuleOrObjectSymbol =
        assumeBuiltin(nme).asMod.getOrElse(throw new NoSuchElementException(
          s"builtin module symbol $nme"))
      val Int = assumeBuiltinCls("Int")
      // TODO(Derppening): Can we move the Int31 builtin in the wasm module?
      val Int31 = assumeBuiltinCls("Int31")
      val Num = assumeBuiltinCls("Num")
      val Str = assumeBuiltinCls("Str")
      val BigInt = assumeBuiltinCls("BigInt")
      val Function = assumeBuiltinCls("Function")
      val Error = assumeBuiltinCls("Error")
      val Bool = assumeBuiltinCls("Bool")
      val Object = assumeBuiltinCls("Object")
      val Array = assumeBuiltinCls("Array")
      val TypedArray = assumeBuiltinCls("TypedArray")
      val Symbol = assumeBuiltinCls("Symbol")
      // println(s"Builtins: $Int, $Num, $Str, $untyped")
      class VirtualModule(val module: ModuleOrObjectSymbol):
        val bms = getBuiltin(module.nme) match
          case S(Ctx.RefElem(bms: BlockMemberSymbol)) => bms
          case huh => wat(huh)
        protected def assumeObject(nme: Str): BlockMemberSymbol =
          module.tree.definedSymbols.get(nme).getOrElse:
            throw new NoSuchElementException(
              s"builtin module symbol source.$nme")
      object SymbolModule extends VirtualModule(assumeBuiltinMod("Symbol")):
        val `for` = assumeObject("for")
        val iterator = assumeObject("iterator")
      object source extends VirtualModule(assumeBuiltinMod("source")):
        val line = assumeObject("line")
        val name = assumeObject("name")
        val file = assumeObject("file")
      object js extends VirtualModule(assumeBuiltinMod("js")):
        val bitand = assumeObject("bitand")
        val bitnot = assumeObject("bitnot")
        val bitor = assumeObject("bitor")
        val shl = assumeObject("shl")
        val try_catch = assumeObject("try_catch")
      object wasm extends VirtualModule(assumeBuiltinMod("wasm")):
        val plus_impl = assumeObject("plus_impl")
        val minus_impl = assumeObject("minus_impl")
        val times_impl = assumeObject("times_impl")
        val div_impl = assumeObject("div_impl")
        val mod_impl = assumeObject("mod_impl")
        val eq_impl = assumeObject("eq_impl")
        val neq_impl = assumeObject("neq_impl")
        val lt_impl = assumeObject("lt_impl")
        val le_impl = assumeObject("le_impl")
        val gt_impl = assumeObject("gt_impl")
        val ge_impl = assumeObject("ge_impl")
        val neg_impl = assumeObject("neg_impl")
        val pos_impl = assumeObject("pos_impl")
        val not_impl = assumeObject("not_impl")
      object debug extends VirtualModule(assumeBuiltinMod("debug")):
        val printStack = assumeObject("printStack")
      object annotations extends VirtualModule(assumeBuiltinMod("annotations")):
        val untyped = assumeObject("untyped")
        val tailrec = assumeObject("tailrec")
        val tailcall = assumeObject("tailcall")
        val inline = assumeObject("inline")
        val compile = assumeObject("compile")
        val buffered = assumeObject("buffered")
        val bufferable = assumeObject("bufferable")
      object scope extends VirtualModule(assumeBuiltinMod("scope")):
        val locally = assumeObject("locally")
      object runtime extends VirtualModule(assumeBuiltinMod("runtime")):
        val suspend = assumeObject("suspend")
        val handle_suspension = assumeObject("handle_suspension")
      def getBuiltinOp(op: Str): Opt[Str] =
        if getBuiltin(op).isDefined then builtinBinOps.get(op) else N
      object BuiltInOpIdent:
        def unapply(id: Ident): Opt[Str] =
          getBuiltinOp(id.name)
      /** Classes that do not use `instanceof` in pattern matching. */
      val virtualClasses = Set(Int, Num, Str, Bool, TypedArray)
  
  object Ctx:
    abstract class Elem:
      def nme: Str
      def ref(id: Ident)(using Elaborator.State, Ctx): Resolvable
      def symbol: Opt[Symbol]
      def isImport: Bool
    final case class RefElem(sym: Symbol) extends Elem:
      val nme = sym.nme
      def ref(id: Ident)(using Elaborator.State, Ctx): Resolvable =
        // * Note: due to symbolic ops, we may have `id.name =/= nme`;
        // * e.g., we can have `id.name = "|>"` and `nme = "pipe"`.
        Term.Ref(sym)(id, 666, N) // FIXME: 666 is a temporary placeholder
      def symbol = S(sym)
      def isImport: Bool = false
    final case class SelElem(base: Elem, nme: Str, symOpt: Opt[MemberSymbol], isImport: Bool) extends Elem:
      def ref(id: Ident)(using Elaborator.State, Ctx): Resolvable =
        // * Same remark as in RefElem#ref
        Term.SynthSel(base.ref(Ident(base.nme)),
          new Ident(nme).withLocOf(id))(symOpt, FlowSymbol.synthSel(nme), N, S(summon))
      def symbol = symOpt
    given Conversion[Symbol, Elem] = RefElem(_)
    val empty: Ctx = Ctx(OuterCtx.LocalScope("top-level"), N, Map.empty, Mode.Full, Map.empty)
    
  enum Mode:
    case Full
    case Light
  
  type Ctxl[A] = Ctx ?=> Cfg[A]
  
  transparent inline def ctx(using Ctx): Ctx = summon
  
  class State:
    val suid = new Uid.Symbol.State
    given State = this
    val globalThisSymbol = TopLevelSymbol("globalThis")
    val unitSymbol = ModuleOrObjectSymbol(DummyTypeDef(syntax.Obj), Ident("Unit"))
    // Stable symbol for the synthetic Wasm Unit singleton
    val unitBlockMemberSymbol = BlockMemberSymbol("Unit", Nil)
    val loopEndSymbol = ModuleOrObjectSymbol(DummyTypeDef(syntax.Obj), Ident("LoopEnd"))
    val tupleSymbol = ModuleOrObjectSymbol(DummyTypeDef(syntax.Mod), Ident("Tuple"))
    val strSymbol = ModuleOrObjectSymbol(DummyTypeDef(syntax.Mod), Ident("Str"))
    // In JavaScript, `import` can be used for getting current file path, as `import.meta`
    val importSymbol = new VarSymbol(Ident("import"))
    val noSymbol = NoSymbol()
    val runtimeSymbol = TempSymbol(N, "runtime")
    val definitionMetadataSymbol = TempSymbol(N, "definitionMetadata")
    val prettyPrintSymbol = TempSymbol(N, "prettyPrint")
    val termSymbol = TempSymbol(N, "Term")
    val blockSymbol = TempSymbol(N, "Block")
    val optionSymbol = TempSymbol(N, "option")
    val wasmSymbol = TempSymbol(N, "wasm")
    val nonLocalRetHandlerTrm =
      val id = new Ident("NonLocalReturn")
      val sym = ClassSymbol(DummyTypeDef(syntax.Cls), id)
      val bsym = BlockMemberSymbol("ret", Nil, true)
      val defn = ClassDef(N, syntax.Cls, sym, bsym, N, Nil, Nil, N, ObjBody(Blk(Nil, Term.Lit(UnitLit(false)))), Nil, N, auxCtorParams = Nil)
      sym.defn = S(defn)
      Term.SynthSel(runtimeSymbol.ref(), id)(S(sym), FlowSymbol.synthSel(id.name), N, N)
    val nonLocalRet =
      val id = new Ident("ret")
      BlockMemberSymbol(id.name, Nil, true)
    val unreachableSymbol = TermSymbol(syntax.ImmutVal, N, new Ident("unreachable"))
    val tupleGetSymbol = createFunSymbolInMod("get", "xs" :: "i" :: Nil, tupleSymbol)
    val tupleSliceSymbol = createFunSymbolInMod("slice", "xs" :: "i" :: "j" :: Nil, tupleSymbol)
    val tupleLazySliceSymbol = createFunSymbolInMod("lazySlice", "xs" :: "i" :: "j" :: Nil, tupleSymbol)
    val strStartsWithSymbol = createFunSymbolInMod("startsWith", "string" :: "prefix" :: Nil, strSymbol)
    val strGetSymbol = createFunSymbolInMod("get", "string" :: "i" :: Nil, strSymbol)
    val strTakeSymbol = createFunSymbolInMod("take", "string" :: "n" :: Nil, strSymbol)
    val strLeaveSymbol = createFunSymbolInMod("leave", "string" :: "n" :: Nil, strSymbol)
    val (matchSuccessClsSymbol, matchSuccessTrmSymbol) =
      val id = new Ident("MatchSuccess")
      val td = TypeDef(syntax.Cls, App(id, Tup(Ident("output") :: Ident("bindings") :: Nil)), N)
      val cs = ClassSymbol(td, id)
      val ts = TermSymbol(syntax.Fun, N, id)
      val flag = FldFlags.empty.copy(isVal = true)
      val ps = PlainParamList(
        Param(flag, VarSymbol(Ident("output")), N, Modulefulness(N)(false)) ::
        Param(flag, VarSymbol(Ident("bindings")), N, Modulefulness(N)(false)) ::
        Nil)
      val ctsym = ClassCtorSymbol(Fun, S(cs), cs.id)
      cs.defn = S(ClassDef.Parameterized(N, syntax.Cls, cs, BlockMemberSymbol(cs.name, Nil), S(ctsym),
        Nil, ps, Nil, N, ObjBody(Blk(Nil, Term.Lit(UnitLit(false)))), N, Nil))
      cs -> ts
    val (matchFailureClsSymbol, matchFailureTrmSymbol) =
      val id = new Ident("MatchFailure")
      val td = DummyTypeDef(syntax.Cls)
      val cs = ClassSymbol(td, id)
      val ts = TermSymbol(syntax.Fun, N, id)
      val flag = FldFlags.empty.copy(isVal = true)
      val ps = PlainParamList(Param(flag, VarSymbol(Ident("errors")), N, Modulefulness(N)(false)) :: Nil)
      val ctsym = ClassCtorSymbol(Fun, S(cs), cs.id)
      cs.defn = S(ClassDef.Parameterized(N, syntax.Cls, cs, BlockMemberSymbol(cs.name, td :: Nil), S(ctsym),
        Nil, ps, Nil, N, ObjBody(Blk(Nil, Term.Lit(UnitLit(false)))), N, Nil))
      cs -> ts
    val builtinOpsMap =
      val baseBuiltins = builtins.map: op =>
          op -> BuiltinSymbol(op,
            binary = binaryOps(op),
            unary = unaryOps(op),
            nullary = false,
            functionLike = anyOps(op))
        .toMap
      baseBuiltins ++ aliasOps.map:
        case (alias, base) => alias -> baseBuiltins(base)
    val andSymbol = builtinOpsMap("&&")
    val orSymbol = builtinOpsMap("||")
    def init(using State): Ctx = Ctx.empty.copy(env = Map(
      "globalThis" -> globalThisSymbol,
    ))
    val superSymbol = builtinOpsMap("super")
    def dbg: Bool = false
    def dbgRefNum(num: Int): Str =
      if dbg then s"#$num" else ""
    def dbgUid(uid: Uid[Symbol]): Str =
      if dbg then s"‹$uid›" else ""
      // ^ we do not display the uid by default to avoid polluting diff-test outputs
    // Create a term symbol for a function defined in the given module
    private def createFunSymbolInMod(name: Str, paramNames: List[Str], mod: ModuleOrObjectSymbol) =
      val sym = TermSymbol(syntax.Fun, N, Ident(name))
      val bsym = BlockMemberSymbol(name, Nil, true)
      val ps = PlainParamList(paramNames.map(s => Param.simple(VarSymbol(Ident(s)))))
      sym.defn = S(TermDefinition(syntax.Fun, bsym, sym, ps :: Nil, N, N, N,
        TermDefFlags(true), Modulefulness(S(mod))(false), Nil, N))
      sym
  transparent inline def State(using state: State): State = state
  
  /** Extracts all parameter lists from a `constructor(...)...` declaration.
    *
    * Constructor declarations are parsed as applied round braces or tuples;
    * for example, `constructor(x, y)(u, v)` becomes
    * `App(Bra(Round, Block(x, y)), Tup(u, v))`.
    */
  private object ConstructorParamDecl:
    def mkTup(inner: Tree): Tree = inner match
      case t: Tup => t
      case Block(stmts) => Tup(stmts)
      case other => Tup(other :: Nil)

    def unapply(tree: Tree): Opt[Ls[Tree]] = tree match
      case Bra(Round, inner) =>
        S(mkTup(inner) :: Nil)
      case App(lhs, rhs @ (_: Tup)) =>
        unapply(lhs).map(_ :+ rhs)
      case App(lhs, Bra(Round, inner)) =>
        unapply(lhs).map(_ :+ mkTup(inner))
      case _ => N
  
end Elaborator


import Elaborator.*


class Elaborator(val tl: TraceLogger, val wd: io.Path, val prelude: Ctx)
(using val raise: Raise, val state: State, val cctx: CompilerCtx, val config: Config)
extends Importer with ucs.SplitElaborator:
  import tl.*
  given TraceLogger = tl
  
  lazy val illegalMemberNameTail =
    msg"Member names must start with a letter or underscore, followed by letters, digits, or underscores." -> N
    :: Nil
  
  def mkLetBinding(kw: Tree.Keywrd[?], sym: LocalVarSymbol | TermSymbol, rhs: Term, annotations: Ls[Annot]): Ls[Statement] =
    LetDecl(sym, annotations).mkLocWith(kw, sym) :: DefineVar(sym, rhs) :: Nil
  
  def resolveField(srcTree: Tree, base: Opt[Symbol], nme: Ident): Opt[MemberSymbol] =
    base match
    case S(psym: BlockMemberSymbol) =>
      psym.modOrObjTree match
      case S(cls) =>
        cls.definedSymbols.get(nme.name) match
        case s @ S(clsSym) => s
        case N =>
          raise(ErrorReport(msg"${cls.k.desc.capitalize} '${cls.symbol.nme
            }' does not contain member '${nme.name}'" -> srcTree.toLoc :: Nil))
          S(ErrorSymbol(nme.name, srcTree))
      case N =>
        N
    case _ => N
  
  def annot(tree: Tree): Ctxl[Opt[Annot]] = tree match
    case Keywrd(kw @ (
      Keyword.`abstract`
      | Keyword.`declare`
      | Keyword.`data`
      | Keyword.`staged`
      | Keyword.`virtual`
      | Keyword.`public`
      | Keyword.`private`
    )) => S(Annot.Modifier(kw))
    case App(Ident("config"), Tup(args)) =>
      val modify = ConfigParser.parseOverrides(args)
      S(Annot.Config(modify))
    case _ => term(tree) match
      case Term.Error => N
      case trm =>
        trm.symbol match
        case S(sym) =>
          sym match
          case ctx.builtins.annotations.untyped =>
            return S(Annot.Untyped)
          case ctx.builtins.annotations.tailcall =>
            return S(Annot.TailCall)
          case ctx.builtins.annotations.tailrec =>
            return S(Annot.TailRec)
          case ctx.builtins.annotations.inline =>
            return S(Annot.Inline)
          case _ => ()
        case _ => ()
        S(Annot.Trm(trm))
  
  private final case class EffectHandlerMethodSpec(
      methodName: Str,
      valueParamName: Opt[Str],
      methodBody: Opt[VarSymbol] => Term,
  )
  
  private def requireEffectMethodValue(methodName: Str, valueSym: Opt[VarSymbol]): Term =
    valueSym match
      case S(sym) => sym.ref(Ident("value"))
      case N => lastWords(s"Missing value parameter for non-local effect handler method '$methodName'.")
  
  /** Mark a handler method as used via symbol direct references, without emitting code. */
  private def markEffectMethodUsed(methodMarker: TempSymbol, callSiteId: Ident): Unit =
    methodMarker.ref(callSiteId)
    ()
  
  /** Use a synthesized selection so the sentinel object can be referenced without field-access sanity checks. */
  private def nonLocalContinueSentinel(using Ctx): Term =
    State.runtimeSymbol.ref().selNoSym("Continue", synth = true)
  
  /** Build an effect handler around `body` for non-local control flow. */
  private def mkEffectHandleAbortive(
      handlerSymbol: TempSymbol,
      effectClassName: Str,
      methods: Ls[EffectHandlerMethodSpec],
      body: Term,
  )(using State): Term =
    val clsSym = ClassSymbol(DummyTypeDef(Cls), Ident(effectClassName))
    val htds = methods.map: spec =>
      val valueSym = spec.valueParamName.map(nme => VarSymbol(Ident(nme)))
      val resumeSym = VarSymbol(Ident("resume"))
      val mtdSym = BlockMemberSymbol(spec.methodName, Nil, true)
      val tsym = TermSymbol(Fun, N, Ident(spec.methodName))
      val td = TermDefinition(
        Fun,
        mtdSym,
        tsym,
        PlainParamList(valueSym.fold(Nil)(sym => Param(FldFlags.empty, sym, N, Modulefulness.none) :: Nil)) :: Nil,
        N,
        N,
        S(spec.methodBody(valueSym)),
        TermDefFlags.empty,
        Modulefulness.none,
        Nil,
        N,
      )
      tsym.defn = S(td)
      mtdSym.tsym = S(tsym)
      HandlerTermDefinition(resumeSym, td)
    Term.Handle(handlerSymbol, state.nonLocalRetHandlerTrm, Nil, clsSym, htds, body)
  
  /** Build a non-local effect invocation on `handlerSymbol`. */
  private def mkNonLocalEffectInvocation(
      handlerSymbol: TempSymbol,
      methodName: Str,
      callSiteId: Ident,
      argTrees: Ls[Tree],
      argTerms: Ls[Term],
  )(using Ctx): Term =
    val rs = FlowSymbol.app()
    val mtdTree = new Ident(methodName)
    val argTree = new Tup(argTrees)
    Term.App(
      Term.Sel(handlerSymbol.ref(callSiteId), mtdTree)(
        S(state.nonLocalRet), FlowSymbol.sel(callSiteId.name), N, S(summon)),
      Term.Tup(argTerms.map(term => PlainFld(term)))(argTree),
    )(Tree.DummyApp, N, rs)
  
  private def mkNonLocalContinueInvocation(
      binding: LabelBinding,
      nme: Ident,
  )(using Ctx): Term =
    markEffectMethodUsed(binding.nonLocalContinueMethodMarker, nme)
    mkNonLocalEffectInvocation(binding.nonLocalHandlerSymbol, "continue", nme, Nil, Nil)
  
  private def wrapNonLocalLabelHandlers(
      body: Term,
      nonLocalHandlerSym: TempSymbol,
      nonLocalBreakMethodMarker: TempSymbol,
      nonLocalContinueMethodMarker: TempSymbol,
  )(using State, Ctx): Term =
    val methods =
      (if nonLocalBreakMethodMarker.directRefs.isEmpty then Nil else
        EffectHandlerMethodSpec("break", S("value"), requireEffectMethodValue("break", _)) :: Nil) :::
      (if nonLocalContinueMethodMarker.directRefs.isEmpty then Nil else
        EffectHandlerMethodSpec("continue", N, _ => nonLocalContinueSentinel) :: Nil)
    if methods.isEmpty then body else
      mkEffectHandleAbortive(nonLocalHandlerSym, "NonLocalLabelEffect", methods, body)
  
  def term(tree: Tree): Ctxl[Term] =
  trace[Term](s"Elab term ${tree.showDbg}", r => s"~> $r"):
    val unders = mutable.ArrayBuffer.empty[VarSymbol]
    given UnderCtx = new UnderCtx(S(unders))
    val st = subterm(tree)
    val params = unders.iterator.map: sym =>
        Param(FldFlags.empty, sym, N, Modulefulness.none)
      .toList
    if params.isEmpty then st
    else Term.Lam(PlainParamList(params), st)
  
  def subterm(tree: Tree): Ctxl[UnderCtx ?=> Term] =
  trace[Term](s"Elab subterm ${tree.showDbg}", r => s"~> $r"):
    
    /** Fallback to a normal selection + application when label-specific handling does not apply. */
    def mkNonLabelSelectionApp(tree: App, sel: Sel, args: Ls[Tree]): Term =
      val sym = FlowSymbol.app()
      val lt = subterm(sel)
      val rt = subterm(Tup(args))
      Term.App(lt, rt)(tree, N, sym)
    
    def elaborateSelection(tree: Sel): Term =
      val preTrm = subterm(tree.prefix)
      val sym = resolveField(tree.name, preTrm.symbol, tree.name)
      if sym.contains(ctx.builtins.source.line) then
        val loc = tree.toLoc.getOrElse(???)
        val (line, _, _) = loc.origin.fph.getLineColAt(loc.spanStart)
        Term.Lit(IntLit(loc.origin.startLineNum + line))
      else if sym.contains(ctx.builtins.source.name) then
        Term.Lit(StrLit(ctx.getOuter.map(_.nme).getOrElse("")))
      else if sym.contains(ctx.builtins.source.file) then
        val loc = tree.toLoc.getOrElse(???)
        Term.Lit(StrLit(loc.origin.fileName.toString))
      else
        Term.Sel(preTrm, tree.name)(sym, FlowSymbol.sel(tree.name.name), N, S(summon))
    
    tree.desugared match
    case Trm(term) => term
    case unt @ Unt() => unit.withLocOf(unt)
    case Bra(k, e) =>
      k match
      case Round =>
      case Curly =>
      case _ =>
        raise(ErrorReport(msg"Unsupported ${k.name} in this position" -> tree.toLoc :: Nil))
      term(e) // * not `subterm` as `e` could be a lambda shorthand
    case b: Block =>
      ctx.nestLocal("‹block›").givenIn:
        block(b, hasResult = true)._1 match
        case Term.Blk(Nil, res) => res
        case res => res
    case lit: Literal =>
      Term.Lit(lit)
    case d: Def =>
      subterm(Block(d :: Unt() :: Nil))
    case LetLike(kw @ Keywrd(`let`), lhs, rhso, S(bod)) =>
      subterm(Block(LetLike(kw, lhs, rhso, N) :: bod :: Nil))
    case LetLike(kw @ Keywrd(`let`), lhs, rhso, N) =>
      raise(ErrorReport(
        msg"Expected a body for let bindings in expression position" ->
          tree.toLoc :: Nil))
      block(LetLike(kw, lhs, rhso, N) :: Nil, hasResult = true)._1
    case LetLike(Keywrd(`set`), lhs, S(rhs), N) =>
      Term.Assgn(subterm(lhs), subterm(rhs))
    case LetLike(Keywrd(`set`), lhs, N, N) =>
      raise(ErrorReport(
        msg"Expected a right-hand side for this assignment" ->
          tree.toLoc :: Nil))
      Term.Error
    case LetLike(Keywrd(`set`), lhs, S(rhs), S(bod)) =>
      // * Backtracking assignment
      if config.effectHandlers.isDefined then
        raise(ErrorReport(
          msg"Backtracking assignment is not supported with effect handlers enabled" ->
            tree.toLoc :: Nil))
        Term.Error
      else
        val lt = subterm(lhs)
        val sym = TempSymbol(S(lt), "old")
        Blk(
          LetDecl(sym, Nil) :: DefineVar(sym, lt) :: Nil, Term.Try(Blk(
            Term.Assgn(lt, subterm(rhs)) :: Nil,
            subterm(bod),
        ), Term.Assgn(lt, sym.ref())))
    case (hd @ Hndl(id: Ident, c, Block(sts_), S(bod))) => ctx.nest(OuterCtx.LambdaOrHandlerBlock).givenIn:
      
      val sym = VarSymbol(id)
      log(s"Processing `handle` statement $id (${sym}) ${ctx.outer}")
      
      val derivedClsSym = ClassSymbol(Tree.DummyTypeDef(syntax.Cls), Tree.Ident(s"Handler$$${id.name}$$"))
      derivedClsSym.defn = S(ClassDef(
        N, syntax.Cls, derivedClsSym,
        BlockMemberSymbol(derivedClsSym.name, Nil), N,
        Nil, Nil, N, ObjBody(Blk(Nil, Term.Lit(Tree.UnitLit(false)))), Nil, N, auxCtorParams = Nil))
      
      val elabed = ctx.nestInner(derivedClsSym).givenIn:
        block(sts_, hasResult = false)._1
      
      elabed.res match
      case Term.Lit(UnitLit(false)) => 
      case trm => raise(WarningReport(msg"Terms in handler block do nothing" -> trm.toLoc :: Nil))
      
      val tds = elabed.stats.map {
          case td @ TermDefinition(Fun, sym, tsym, params, tparams, sign, body, flags, mf, annotations, comp) =>
            params.reverse match
              case ParamList(_, value :: Nil, _) :: newParams =>
                if newParams.isEmpty then
                  raise(ErrorReport(msg"Handler function cannot be a getter" -> td.toLoc :: Nil))
                val newTd = TermDefinition(Fun, sym, tsym, newParams.reverse, tparams, sign, body, flags, mf, annotations, comp)
                S(HandlerTermDefinition(value.sym, newTd))
              case _ => 
                raise(ErrorReport(msg"Handler function is missing resumption parameter" -> td.toLoc :: Nil))
                None
              
          case st => 
            raise(ErrorReport(msg"Only function definitions are allowed in handler blocks" -> st.toLoc :: Nil))
            None
        }.collect { case Some(x) => x }
      
      val (cp, p) = c match
        case App(c, Tup(params)) =>
          (subterm(c), params.map(subterm(_)))
        case c =>
          (subterm(c), Nil)
      
      (ctx + (id.name -> sym)).givenIn:
        Term.Handle(sym, cp, p, derivedClsSym, tds, subterm(bod))
    case h: Hndl =>
      raise(ErrorReport(
        msg"Unsupported handle binding shape" ->
          h.toLoc :: Nil))
      Term.Error
    case id @ Ident("this") =>
      ctx.getOuter match
      case S(sym) => sym.ref(id)
      case N =>
        raise:
          ErrorReport(msg"Cannot use 'this' outside of an object scope" -> tree.toLoc :: Nil)
        Term.Error
    case id @ Ident("|" | "&") =>
      raise:
        ErrorReport(msg"Unexpected use of special operator '${id.name}'" -> id.toLoc :: Nil)
      Term.Error
    case id @ Ident(name) => ident(id).getOrElse:
      raise(ErrorReport(msg"Name not found: $name" -> id.toLoc :: Nil))
      Term.Error
    case TyApp(lhs, targs) =>
      Term.TyApp(subterm(lhs), targs.map {
        case Modified(Keywrd(Keyword.`in`), arg) => Term.WildcardTy(S(subterm(arg)), N)
        case Modified(Keywrd(Keyword.`out`), arg) => Term.WildcardTy(N, S(subterm(arg)))
        case Tup(Modified(Keywrd(Keyword.`in`), arg1) :: Modified(Keywrd(Keyword.`out`), arg2) :: Nil) =>
          Term.WildcardTy(S(subterm(arg1)), S(subterm(arg2)))
        case arg => subterm(arg)
      })(N).withLocOf(tree)
    case InfixApp(TyTup(tvs), Keywrd(Keyword.`->`), body) =>
      val boundVars = mutable.HashMap.empty[Str, VarSymbol]
      def genSym(id: Tree.Ident) =
        val sym = VarSymbol(id)
        sym.decl = S(TyParam(FldFlags.empty, N, sym)) // TODO vce
        boundVars += id.name -> sym
        sym
      val syms = (tvs.collect:
        case id: Tree.Ident => (genSym(id), N, N)
        case InfixApp(id: Tree.Ident, Keywrd(Keyword.`extends`), ub) => (genSym(id), S(ub), N)
        case InfixApp(id: Tree.Ident, Keywrd(Keyword.`restricts`), lb) => (genSym(id), N, S(lb))
        case InfixApp(InfixApp(id: Tree.Ident, Keywrd(Keyword.`extends`), ub), Keywrd(Keyword.`restricts`), lb) => (genSym(id), S(ub), S(lb))
      )
      val outer = (tvs.collect:
        case Outer(S(name: Tree.Ident)) => genSym(name)
        case Outer(N) => genSym(Tree.Ident("outer"))
      ) match
        case ot :: Nil => S(ot)
        case _ :: rest =>
          raise(ErrorReport(msg"Only one outer variable can be bound." -> tree.toLoc :: Nil))
          N
        case Nil => N
      
      if syms.length + outer.count(_ => true) =/= tvs.length then
        raise(ErrorReport(msg"Illegal forall annotation." -> tree.toLoc :: Nil))
        Term.Error
      else
        given Ctx = ctx ++ boundVars
        val bds = syms.map:
          case (sym, ub, lb) =>
            QuantVar(sym, ub.map(ub => subterm(ub)), lb.map(lb => subterm(lb)))
        Term.Forall(bds, outer, subterm(body))
    case InfixApp(lhs, Keywrd(Keyword.`->`), Effectful(eff, rhs)) =>
      Term.FunTy(subterm(lhs), subterm(rhs), S(subterm(eff)))
    case InfixApp(lhs, Keywrd(Keyword.`->`), rhs) =>
      Term.FunTy(subterm(lhs), subterm(rhs), N)
    case InfixApp(lhs, Keywrd(Keyword.`=>`), rhs) =>
      lhs match
      case Tup(_) =>
        ctx.nest(OuterCtx.LambdaOrHandlerBlock).givenIn:
          val (syms, nestCtx) = funParams(lhs)
          Term.Lam(syms, term(rhs)(using nestCtx))
      case TyTup(tys) =>
        val constraints = tys.flatMap(maybeConstraint)
        val body = term(rhs)
        Term.Constrained(constraints, body)
    case InfixApp(lhs, Keywrd(Keyword.`as`), rhs) =>
      Term.Asc(subterm(lhs), subterm(rhs))
    case InfixApp(lhs, Keywrd(Keyword.`:`), rhs) =>
      block(tree :: Nil, hasResult = false)._1
    case PrefixApp(kw @ Keywrd(Keyword.`not`), rhs) =>
      Term.App(State.builtinOpsMap("!").ref(new Ident("not").withLocOf(kw)), Term.Tup(
        PlainFld(subterm(rhs)) :: Nil)(DummyTup))(DummyApp, N, FlowSymbol("not-app"))
    case tree @ InfixApp(lhs, Keywrd(Keyword.`is` | Keyword.`and` | Keyword.`or`), rhs) =>
      Term.IfLike(Keyword.`if`, IfLikeForm.ReturningIf, shorthandSplit(tree))
    case InfixApp(Sel(pre, idn: Ident), Keywrd(Keyword.`#`), idp: Ident) =>
      val c = subterm(idn)
      val f = c.symbol.flatMap(_.asCls) match
        case S(cls: ClassSymbol) =>
          cls.tree.allSymbols.get(idp.name) match
          case S(fld: MemberSymbol) => S(fld)
          case _ =>
            raise(ErrorReport(msg"Class '${cls.nme}' does not contain member '${idp.name}'." -> idp.toLoc :: Nil))
            N
        case _ =>
          raise(ErrorReport(msg"Identifier `${idn.name}` does not name a known class symbol." -> idn.toLoc :: Nil))
          N
      Term.SelProj(subterm(pre), c, idp)(f, FlowSymbol.selProj(idp.name), N, S(summon))
    case InfixApp(lhs, kw, rhs) =>
      raise:
        ErrorReport(msg"Unexpected infix use of keyword '${kw.name}' here" -> tree.toLoc :: Nil)
      Term.Error
    case OpApp(lhs, Ident("|"), rhs :: Nil) =>
      Term.CompType(subterm(lhs), subterm(rhs), true)
    case OpApp(lhs, Ident("&"), rhs :: Nil) =>
      Term.CompType(subterm(lhs), subterm(rhs), false)
    case OpApp(lhs, Ident(":="),rhs :: Nil) =>
      Term.SetRef(subterm(lhs), subterm(rhs))
    case App(Ident("!"), Tup(rhs :: Nil)) =>
      Term.Deref(subterm(rhs))
    case App(Ident("~"), Tup(rhs :: Nil)) =>
      Term.Neg(subterm(rhs))
    case App(Ident("|" | "&"), Tup(rhs :: Nil)) =>
      subterm(rhs)
    case tree @ OpSplit(lhs, rhss) =>
      val tree = rhss.foldLeft(lhs):
        case (acc, rhs) =>
          rhs.splitOn(acc)
      subterm(tree)
    case tree @ App(sel @ Sel(labelId @ Ident(labelName), nme @ Ident("break")), Tup(args)) =>
      val value = args match
        case Nil => N
        case arg :: Nil => S(subterm(arg))
        case _ =>
          raise(ErrorReport(msg"'break' expects at most one argument." -> tree.toLoc :: Nil))
          N
      ctx.lookupLabel(labelName) match
      case LabelLookup.Found(binding) =>
        Term.Break(binding.labelSymbol, binding.resultSymbol, value)
      case LabelLookup.AcrossBoundary(binding) =>
        if config.effectHandlers.isEmpty then
          mkNonLabelSelectionApp(tree, sel, args)
        else
          markEffectMethodUsed(binding.nonLocalBreakMethodMarker, nme)
          mkNonLocalEffectInvocation(
            binding.nonLocalHandlerSymbol,
            "break",
            nme,
            args,
            value.toList,
          )
      case LabelLookup.NotFound =>
        mkNonLabelSelectionApp(tree, sel, args)
    case tree @ App(sel @ Sel(labelId @ Ident(labelName), nme @ Ident("continue")), Tup(args)) =>
      def checkNoArgs: Unit = if args.nonEmpty then raise:
        ErrorReport(msg"'continue' does not take arguments." -> tree.toLoc :: Nil)
      ctx.lookupLabel(labelName) match
      case LabelLookup.Found(binding) =>
        checkNoArgs
        Term.Continue(binding.labelSymbol)
      case LabelLookup.AcrossBoundary(binding) =>
        checkNoArgs
        if config.effectHandlers.isEmpty then
          raise:
            ErrorReport(msg"Non-local 'continue' is only supported with effect handlers enabled."
              -> labelId.toLoc :: Nil)
          Term.Error
        else
          mkNonLocalContinueInvocation(binding, nme)
      case LabelLookup.NotFound =>
        mkNonLabelSelectionApp(tree, sel, args)
    case tree @ App(lhs, rhs) =>
      val sym = FlowSymbol.app()
      val lt = subterm(lhs)
      val rt = subterm(rhs)
      Term.App(lt, rt)(tree, N, sym)
    case tree @ OpApp(lhs, op, rhss) =>
      val sym = FlowSymbol.app()
      val lt = subterm(lhs)
      val ot = subterm(op)
      val rts = rhss.map(r => PlainFld(subterm(r)))
      Term.App(ot, Term.Tup(PlainFld(lt) :: rts)(DummyTup))(
        DummyApp, N, sym)
    case SynthSel(pre, nme) =>
      val preTrm = subterm(pre)
      val sym = resolveField(nme, preTrm.symbol, nme)
      Term.SynthSel(preTrm, nme)(sym, FlowSymbol.synthSel(nme.name), N, S(summon)).withLocOf(tree)
    case Sel(Empty(), nme) =>
      Term.LeadingDotSel(nme)(S(summon)).withLocOf(tree)
    case sel @ Sel(labelId @ Ident(labelName), nme @ Ident("break")) =>
      ctx.lookupLabel(labelName) match
      case LabelLookup.Found(binding) =>
        Term.Break(binding.labelSymbol, binding.resultSymbol, N)
      case LabelLookup.AcrossBoundary(binding) =>
        if config.effectHandlers.isEmpty then
          raise:
            ErrorReport(msg"Non-local 'break' is only supported with effect handlers enabled."
              -> labelId.toLoc :: Nil)
          Term.Error
        else
          markEffectMethodUsed(binding.nonLocalBreakMethodMarker, nme)
          mkNonLocalEffectInvocation(binding.nonLocalHandlerSymbol, "break", nme, Nil, Nil)
      case LabelLookup.NotFound =>
        elaborateSelection(sel)
    case sel @ Sel(labelId @ Ident(labelName), nme @ Ident("continue")) =>
      ctx.lookupLabel(labelName) match
      case LabelLookup.Found(binding) =>
        Term.Continue(binding.labelSymbol)
      case LabelLookup.AcrossBoundary(binding) =>
        if config.effectHandlers.isEmpty then
          raise:
            ErrorReport(msg"Non-local 'continue' is only supported with effect handlers enabled."
              -> labelId.toLoc :: Nil)
          Term.Error
        else
          mkNonLocalContinueInvocation(binding, nme)
      case LabelLookup.NotFound =>
        elaborateSelection(sel)
    case sel @ Sel(pre, nme) =>
      elaborateSelection(sel)
    case MemberProj(ct, nme) =>
      val c = subterm(ct)
      val f = c.symbol.flatMap(_.asCls) match
        case S(cls: ClassSymbol) =>
          cls.tree.allSymbols.get(nme.name) match
          case S(fld: MemberSymbol) => S(fld)
          case _ =>
            raise(ErrorReport(msg"Class '${cls.nme}' does not contain member '${nme.name}'." -> nme.toLoc :: Nil))
            N
        case _ =>
          raise:
            ErrorReport:
              msg"${ct.describe.capitalize} is not a known class." -> ct.toLoc ::
              msg"Note: any expression of the form `‹expression›::‹identifier›` is a member projection;" -> N ::
              msg"  add a space before ‹identifier› to make it an operator application." -> N ::
              Nil
          N
      val self = VarSymbol(Ident("self"))
      val args = VarSymbol(Ident("args"))
      val ps = ParamList(ParamListFlags.empty,
        Param(FldFlags.empty, self, N, Modulefulness.none) :: Nil,
        S:
          Param(FldFlags.empty, args, N, Modulefulness.none)
      )
      val rs = FlowSymbol.app()
      Term.Lam(ps,
        Term.App(Term.SelProj(self.ref(), c, nme)(f, FlowSymbol.selProj(nme.name), N, S(summon)), args.ref())(
          App(nme, Tup(Nil)) // FIXME
          , N, rs)
      )
    case tree @ Tup(TermDef(Ins, f, N) :: fs) =>
      Term.CtxTup((f :: fs).map(fld(_)))(tree)
    case Modified(kw @ Keywrd(Keyword.`mut`), tree @ Tup(fields)) =>
      Term.Mut(Term.Tup(fields.map(fld(_)))(tree)).mkLocWith(kw)
    case tree @ Tup(fields) =>
      Term.Tup(fields.map(fld(_)))(tree)
      
    case DynamicNew(Apps(c, args)) =>
      val (mut, c2) = c match
        case Modified(Keywrd(Keyword.`mut`), c) => (true, c)
        case c => (false, c)
      val base = new Term.DynNew(subterm(c2), args.map(subterm(_))).withLocOf(tree)
      if mut then Term.Mut(base) else base
    // case New(c, rfto) =>
    //   assert(rfto.isEmpty)
    //   Term.New(cls(subterm(c), inAppPrefix = inAppPrefix), params.map(subterm(_)), bodo).withLocOf(tree)
    case ProperNew(body, rfto) => // TODO handle Under
      lazy val bodo = rfto.map: rft =>
        val clsSym = new ClassSymbol(DummyTypeDef(syntax.Cls), Ident("$anon"))
        ctx.nestInner(clsSym).givenIn:
          clsSym ->
            // TODO integrate context inherited from cls
            // TODO make context with var symbols for class parameters
            ObjBody(block(rft, hasResult = false)._1)
      body match
      case S(Apps(c, args)) =>
        val (mut, c2) = c match
          case Modified(Keywrd(Keyword.`mut`), c) => (true, c)
          case c => (false, c)
        val inner = new Term.New(
          subterm(c2), // * Note: we'll catch bad `new` targets during type checking
          args.map(subterm(_)),
          bodo
        )(N).withLocOf(tree)
        if mut then Term.Mut(inner) else inner
      case N =>
        val objectRef = ctx.builtins.Object.bms.get.ref(Ident("Object"))
        Term.New(objectRef, Nil, bodo)(N).withLocOf(tree)
      // case _ =>
      //   raise(ErrorReport(msg"Illegal new expression." -> tree.toLoc :: Nil))
      
    case tree: IfLike => split(tree)
    
    case Assert(kw, rhs, thno, els) =>
      val (fl, ln) = kw.toLoc match
        case S(loc) =>
          val org = loc.origin
          (org.fileName.relativeTo(config.baseDir).getOrElse(org.fileName).toString,
            (org.startLineNum + org.fph.getLineColAt(loc.spanStart)._1).toString)
        case N => ("‹unknown›", "‹unknown›")
      val elsPart = els.fold(PrefixApp(Keywrd(Keyword.`else`), Tree.Trm(
        State.runtimeSymbol.ref().selNoSym("assertFail")
          .app(Term.Lit(StrLit(fl)), Term.Lit(StrLit(ln)))
      )))(PrefixApp.apply.tupled)
      subterm:
        IfLike(new Keywrd(Keyword.`if`).withLocOf(kw), Block(
          InfixApp(rhs, new Keywrd(Keyword.`then`), thno.getOrElse(Unt())) :: elsPart :: Nil))
      
    case Quoted(body) => Term.Quoted(subterm(body))
    case Unquoted(body) => Term.Unquoted(subterm(body))
    case tree @ Case(kw, _) =>
      val scrut = VarSymbol(Ident("caseScrut"))
      val body = caseSplit(scrut, tree)
      val params = Param(FldFlags.empty, scrut, N, Modulefulness.none) :: Nil
      Term.Lam(PlainParamList(params), body).mkLocWith(kw)
    case PrefixApp(kw @ Keywrd(Keyword.`return`), body) =>
      ctx.getRetHandler match
      case ReturnHandler.Required(sym) =>
        log(s"Non-local return: $sym")
        if config.effectHandlers.isEmpty then
          raise:
            ErrorReport(msg"Non-local return statements are only supported with effect handlers enabled." -> tree.toLoc :: Nil)
          Term.Error
        else
          val callSiteId = new Ident("return").withLocOf(kw)
          mkNonLocalEffectInvocation(sym, "ret", callSiteId, body :: Nil, subterm(body) :: Nil)
      case ReturnHandler.NotInFunction =>
        raise:
          ErrorReport(msg"Return statements are not allowed outside of functions." -> tree.toLoc :: Nil)
        Term.Error
      case ReturnHandler.Direct =>
        Term.Ret(subterm(body))
      case ReturnHandler.Forbidden =>
        raise:
          ErrorReport(msg"Return statements are not allowed in this context." -> tree.toLoc :: Nil)
        Term.Error
    case PrefixApp(kw @ Keywrd(Keyword.`throw`), body) =>
      Term.Throw(subterm(body)).mkLocWith(kw)
    case PrefixApp(kw @ Keywrd(Keyword.`do`), InfixApp(labelId: Ident, Keywrd(Keyword.`:`), body)) =>
      val labelSym = new LabelSymbol(N, labelId.name)
      val resultSym = new TempSymbol(N, s"${labelId.name}$$result")
      val nonLocalHandlerSym = TempSymbol(N, s"nonLocalHandler$$${labelId.name}")
      val nonLocalBreakMethodMarker = TempSymbol(N, s"nonLocalBreakMethod$$${labelId.name}")
      val nonLocalContinueMethodMarker = TempSymbol(N, s"nonLocalContinueMethod$$${labelId.name}")
      val bodyTerm = ctx.withLabel(
        labelSym, resultSym, nonLocalHandlerSym, nonLocalBreakMethodMarker, nonLocalContinueMethodMarker).givenIn:
        subterm(body)
      val wrappedBodyTerm = wrapNonLocalLabelHandlers(
        bodyTerm, nonLocalHandlerSym, nonLocalBreakMethodMarker, nonLocalContinueMethodMarker)
      Term.Label(labelSym, resultSym, wrappedBodyTerm, nonLocalContinueMethodMarker.directRefs.nonEmpty).mkLocWith(kw, labelId)
    case PrefixApp(kw @ Keywrd(Keyword.`do`), body) =>
      Blk(subterm(body) :: Nil, unit).mkLocWith(kw)
    case PrefixApp(kw @ Keywrd(Keyword.`drop`), body) =>
      Term.Drop(subterm(body)).mkLocWith(kw)
    case Region(id: Ident, body) =>
      val sym = VarSymbol(id)
      given Ctx = ctx + (id.name -> sym)
      Term.Region(sym, subterm(body))
    case RegRef(reg, value) => Term.RegRef(subterm(reg), subterm(value))
    case Outer(S(_)) =>
      raise(ErrorReport(msg"Illegal outer binding." -> tree.toLoc :: Nil))
      Term.Error
    case Outer(N) => ctx.get("outer") match
      case S(sym) => sym.ref(Ident("outer"))
      case N =>
        raise(ErrorReport(msg"Illegal outer reference." -> tree.toLoc :: Nil))
        Term.Error
    case Empty() =>
      raise(ErrorReport(msg"A term was expected in this position, but no term was found." -> tree.toLoc :: Nil))
      Term.Error
    case Error() =>
      Term.Error
    case TermDef(k, nme, rhs) =>
      raise(ErrorReport(msg"Illegal definition in term position." -> tree.toLoc :: Nil))
      Term.Error
    case TypeDef(k, head, rhs) =>
      raise(ErrorReport(msg"Illegal type declaration in term position." -> tree.toLoc :: Nil))
      Term.Error
    case Modified(Keywrd(Keyword.`mut`), body: Block) =>
      blockOrRcd(body, hasResult = true) match
      case (Blk(Nil, Term.UnitVal()), ctx) =>
        Rcd(mut = true, Nil).withLocOf(body)
      case (blk: Blk, ctx) =>
        raise(ErrorReport(msg"Expected a record after 'mut' keyword; found a block" -> blk.toLoc :: Nil))
        blk
      case (rcd: Rcd, ctx) => rcd.copy(mut = true).withLocOf(rcd)
    case Modified(kw, body) =>
      raise(ErrorReport(msg"Illegal position for '${kw.name}' modifier." -> kw.toLoc :: Nil))
      subterm(body)
    case PrefixApp(kw, body) =>
      raise(ErrorReport(msg"Illegal position for prefix keyword '${kw.name}'." -> kw.toLoc :: Nil))
      subterm(body)
    case Jux(lhs, rhs) =>
      def go(acc: Term, trees: Ls[Tree]): Term =
        trees match
        case Nil => acc
        
        // * FIXME this `f.name.head.isLetter` test is a big hack...
        // * TODO would be better to keep the fixity of applications part of the Tree repr.
        case (ap @ App(f: Ident, tup @ Tup(lhs :: args))) :: trees if !f.name.head.isLetter =>
          val res = go(acc, lhs :: Nil)
          val sym = FlowSymbol.app()
          val fl = Fld(FldFlags.empty, res, N)
          val app = Term.App(subterm(f), Term.Tup(
            fl :: args.map(fld))(tup))(ap, N, sym)
          go(app, trees)
        case (ap @ App(f, tup @ Tup(args))) :: trees =>
          val sym = FlowSymbol.app()
          go(Term.App(subterm(f),
              Term.Tup(Fld(FldFlags.empty, acc, N) :: args.map(fld))(tup)
            )(ap, N, sym), trees)
        case Block(sts) :: trees =>
          go(acc, sts ::: trees)
        case tree :: trees =>
          raise(ErrorReport(msg"Illegal juxtaposition right-hand side (${tree.describe})." -> tree.toLoc :: Nil))
          go(acc, trees)
      
      go(subterm(lhs), rhs :: Nil)
    case Open(op) =>
      raise(ErrorReport(msg"Illegal position for 'open' statement." -> tree.toLoc :: Nil))
      Term.Error
    case OpenIn(op, body) =>
      subterm(Block(Open(op) :: body :: Nil))
    case DynAccess(obj, rhs) =>
      rhs match
      case Bra(bk @ (Round | Square), fld) => Term.DynSel(subterm(obj), subterm(fld), bk is Square)
      case fld: Literal => Term.DynSel(subterm(obj), subterm(fld), false)
      case id: Ident =>
        Term.DynSel(subterm(obj), Term.Lit(StrLit(id.name)).withLocOf(id), false)
      case _ =>
        raise(ErrorReport(msg"Illegal dynamic field access selector (${rhs.describe})." -> tree.toLoc :: Nil))
        Term.Error
    case Spread(kw, body) =>
      raise(ErrorReport(msg"Illegal position for '${kw.name}' spread operator." -> kw.toLoc :: Nil))
      Term.Error
    case und: Under =>
      summon[UnderCtx].unders match
      case N =>
        raise(ErrorReport(msg"Illegal position for '_' placeholder." -> tree.toLoc :: Nil))
        Term.Error
      case S(unds) =>
        val sym = VarSymbol(Ident("_" + unds.size))
        unds += sym
        sym.ref()
    case Annotated(lhs, rhs) =>
      annot(lhs).fold(subterm(rhs))(ann =>
        Term.Annotated(ann, subterm(rhs)))
    case Keywrd(kw) =>
      raise(ErrorReport(msg"Unexpected keyword '${kw.name}' in this position." -> tree.toLoc :: Nil))
      Term.Error
    case Constructor(delc) =>
      raise(ErrorReport(msg"Unsupported constructor in this position." -> tree.toLoc :: Nil))
      Term.Error
    // case _ =>
    //   ???
  
  def arg(tree: Tree)(using UnderCtx): Ctxl[Term] = tree match
    case u: Under => subterm(tree) // Note: currently `f(a, _, c)` is treated the same as `f of a, _, c`
    case _ => term(tree)
  def fld(tree: Tree)(using UnderCtx): Ctxl[Elem] = tree match
    case InfixApp(id: Ident, Keywrd(Keyword.`:`), rhs) =>
      Fld(FldFlags.empty, Term.Lit(StrLit(id.name).withLocOf(id)), S(arg(rhs)))
    case InfixApp(lhs, Keywrd(Keyword.`:`), rhs) =>
      Fld(FldFlags.empty, term(lhs), S(arg(rhs)))
    case Spread(Keywrd(Keyword.`..`), S(trm)) =>
      Spd(SpreadKind.Lazy, arg(trm))
    case Spread(Keywrd(Keyword.`...`), S(trm)) =>
      Spd(SpreadKind.Eager, arg(trm))
    case _ =>
      val t = arg(tree)
      var flags = FldFlags.empty
      Fld(flags, t, N)
  
  def unit: Term.UnitVal = Term.UnitVal()
  
  
  
  def block(sts: Ls[Tree], hasResult: Bool)(using UnderCtx): Ctxl[(Blk, Ctx)] =
    block(new Block(sts), hasResult)
  
  def block(blk: Block, hasResult: Bool)(using UnderCtx): Ctxl[(Blk, Ctx)] =
    blockOrRcd(blk, hasResult) match
    case (blk: Blk, ctx) => (blk, ctx)
    case (rcd: Rcd, ctx) => (Blk(Nil, rcd), ctx)
  
  val supportedOverloadings: Set[(OuterKind, OuterKind)] = Set(
    Cls -> Mod,
    Obj -> Mod,
    Als -> Mod,
  )
  val notYetSupportedOverloadings: Set[(OuterKind, OuterKind)] = Set(
    Fun -> Cls,
    Fun -> Mod,
    Pat -> Mod,
    ImmutVal -> Mod,
    MutVal -> Mod,
  )
  
  // * Some blocks do not have a meaningful result,
  // * e.g., constructor blocks or top-level blocks (in MLscript files and diff-tests);
  // * for these, elaborate with `hasResult = false`, which uses `undefined` as the result
  // * when there is no other result available. This is fine since the value is never used.
  // * These useless trailing `undefined`s are then removed by `Lowering`.
  def blockOrRcd(blk: Block, hasResult: Bool)(using UnderCtx)
    : Ctxl[(Blk | Rcd, Ctx)]
    = trace[(Blk | Rcd, Ctx)](
        pre = s"Elab block ${blk.desugStmts.toString.truncate(100, "[...]")} ${ctx.outer}", r => s"~> ${r._1}"
      ):
    
    val members = blk.definedSymbols.toMap
    val newSignatureTrees = mutable.Map.empty[Str, Tree] // * Store trees of signatures
    
    // * Check for double/incompatible definitions and declarations
    blk.definedSymbols.foreach: (name, sym) =>
      if sym.nme === name then // * This is not true when `name` is the symbolic name of a member
        
        sym.trees.foreach: td =>
          td.symbName match
          case S(R(id)) =>
            val mem = members.getOrElse(id.name, die)
            if mem isnt sym then raise:
              ErrorReport:
                msg"Symbolic name '${id.name}' of ${
                    td.name.fold(_ => "this definition", id => "definition '" + id.name + "'")
                  } is already used" -> td.toLoc
                :: msg"by sibling member '${mem.nme}'" -> mem.toLoc
                :: Nil
          case _ => ()
        
        val defns = sym.trees.collect:
          case td: TermDef if td.rhs.isDefined && td.name.exists(_.name === name) => td
          case td: TypeDef if td.name.exists(_.name === name) => td
        if defns.sizeCompare(1) > 0 then
          val groups = defns.groupMapReduce(_.k)(_ :: Nil)(_ ::: _)
          val sortedGroups = groups.toArray.sortBy(_._1)
          sortedGroups.iterator.foreach: (k, group) =>
            if group.size > 1 then
              raise(ErrorReport(msg"Multiple definitions of symbol '$name'" -> N ::
                group.map(msg"defined here" -> _.toLoc)))
            val mainDefn = group.head // * Safe since these `groupMapReduce` groups cannot be empty
            log(s"Processing overloadings for '$name'")
            defns.iterator.foreach: defn =>
              if defn.k > k then
                if !supportedOverloadings(k -> defn.k) then raise:
                  ErrorReport:
                    if notYetSupportedOverloadings(k -> defn.k)
                    then msg"Not yet supported: overloading of ${k.desc} '$name'" -> mainDefn.toLoc
                      :: msg"with ${defn.k.desc} of the same name" -> defn.toLoc
                      :: Nil
                    else msg"Illegal overloading of ${k.desc} '$name'" -> mainDefn.toLoc
                      :: msg"with ${defn.k.desc} of the same name" -> defn.toLoc
                      :: Nil
        
        val decls = sym.trees.collect:
          case td: TermDef if td.rhs.isEmpty => td
        if decls.length > 1 then
          raise(ErrorReport(msg"Multiple declarations of symbol '$name'" -> N ::
            decls.map(msg"declared here" -> _.toLoc)))
        val sig = decls.collectFirst:
          case td
            if td.annotatedResultType.isDefined
            && td.paramLists.isEmpty
            => td.annotatedResultType.get
        sig.foreach: sig =>
          newSignatureTrees += name -> sig
    
    // TODO extract this into a separate method
    // * @param funs:
    // *  While elaborating a block, we move all function definitions to the top (similar to JS function semantics)
    @tailrec
    def go(sts: Ls[Tree], annotations: Ls[Annot], acc: Ls[Statement]): Ctxl[(Blk | Rcd, Ctx)] =
      /** Call this function when the following term cannot be annotated. */
      def reportUnusedAnnotations: Unit = if annotations.nonEmpty then raise:
        WarningReport:
          msg"This annotation has no effect" -> (annotations.foldLeft[Opt[Loc]](N):
            case (acc, ann) => acc match
              case N => ann.toLoc
              case S(loc) => S(loc ++ ann.toLoc)
          ) :: (sts.headOption match
            case N => msg"A target term is expected at the end of block" -> blk.toLoc.map(_.right)
            case S(head) => msg"Annotations are not supported on ${head.describe} terms." -> head.toLoc
          ) :: Nil
      sts match
      case Nil =>
        reportUnusedAnnotations
        (mkBlk(acc, N, hasResult), ctx)
      case Constructor(Block(ctors)) :: sts =>
        // TODO properly handle (it currently desugars to sibling classes)
        go(sts, annotations, acc)
      case (ctorParams @ Constructor(ConstructorParamDecl(_))) :: sts =>
        // constructor(x, y) or constructor(x, y)(u, v) syntax: params are extracted during class elaboration
        ctx.getOuter match
        case S(_: ClassSymbol) =>
          go(sts, annotations, acc)
        case _ =>
          raise(ErrorReport(msg"'constructor(...)' declarations are only allowed in class bodies"
            -> ctorParams.toLoc :: Nil))
          go(sts, annotations, acc)
      case Open(bod) :: sts =>
        reportUnusedAnnotations
        bod match
          case Jux(bse, Block(sts)) =>
            some(bse -> some(sts))
          // * There could be other shapes of open statements...
          case bse: Ident =>
            some(bse -> N)
          case _ =>
            raise(ErrorReport(msg"Illegal 'open' statement shape." -> bod.toLoc :: Nil))
            N
        match
        case N => go(sts, annotations, acc)
        case S((base, importedTrees)) =>
          base match
          case baseId: Ident =>
            ctx.get(baseId.name) match
            case S(baseElem) =>
              val importedNames = importedTrees match
                case N => // "wilcard" open
                  baseElem.symbol match
                  case S(sym: BlockMemberSymbol) if sym.modOrObjTree.isDefined =>
                    sym.modOrObjTree.get.definedSymbols.map:
                      case (nme, sym) => nme -> Ctx.SelElem(baseElem, sym.nme, S(sym), isImport = true)
                  case _ =>
                    raise(ErrorReport(msg"Wildcard 'open' not supported for this kind of symbol." -> baseId.toLoc :: Nil))
                    Nil
                case S(sts) => sts.flatMap:
                  case id: Ident =>
                    if ctx.env.contains(id.name) then
                      raise(WarningReport(msg"Imported name '${id.name}' is shadowed by a name already defined in the same scope" -> id.toLoc :: Nil))
                    val sym = resolveField(id, baseElem.symbol, id)
                    val e = Ctx.SelElem(baseElem, id.name, sym, isImport = true)
                    id.name -> e :: Nil
                  case t =>
                    raise(ErrorReport(msg"Illegal 'open' statement element." -> t.toLoc :: Nil))
                    Nil
              (ctx elem_++ importedNames).givenIn:
                go(sts, Nil, acc)
            case N =>
              raise(ErrorReport(msg"Name not found: ${baseId.name}" -> baseId.toLoc :: Nil))
              go(sts, Nil, acc)
          case _ =>
            raise(ErrorReport(msg"Illegal 'open' statement base." -> base.toLoc :: Nil))
            go(sts, Nil, acc)
      case (m @ PrefixApp(Keywrd(Keyword.`import`), arg)) :: sts =>
        reportUnusedAnnotations
        val pathAndAlias: Opt[(Tree, Opt[Ident])] = arg match
          case InfixApp(pathArg, Keywrd(Keyword.`as`), alias: Ident) => S((pathArg, S(alias)))
          case InfixApp(pathArg, Keywrd(Keyword.`as`), Error()) => N
          case InfixApp(_, Keywrd(Keyword.`as`), badAlias) =>
            raise(ErrorReport(
              msg"Expected identifier after 'as' in import statement" ->
              badAlias.toLoc :: Nil))
            N
          case pathArg => S((pathArg, N))
        val (newCtx, newAcc) = pathAndAlias match
          case S((StrLit(path), alias)) =>
            val stmt = importPath(path, alias).withLocOf(m)
            (ctx + (stmt.sym.nme -> stmt.sym),
              stmt :: acc)
          case S((pathArg, _)) =>
            raise(ErrorReport(
              msg"Expected string literal after 'import' keyword" ->
              pathArg.toLoc :: Nil))
            (ctx, acc)
          case N => // errors have been reported above.
            (ctx, acc)
        newCtx.givenIn:
          go(sts, Nil, newAcc)
      
      case Spread(Keywrd(Keyword.`...`), S(body)) :: sts =>
        reportUnusedAnnotations
        go(sts, Nil, RcdSpread(term(body)) :: acc)
      case InfixApp(lhs, Keywrd(Keyword.`:`), rhs) :: sts =>
        var newCtx = ctx
        val (rlhs, rhs_t) = rhs match
          case _: Under => (lhs, subterm(rhs))
          case _ =>
            lhs match
            case Apps(base, tups) =>
              val rrhs = tups.foldRight(rhs):
                InfixApp(_, Keywrd(Keyword.`=>`), _)
              (base, term(rrhs))
        val newAcc = rlhs match
          case id: Ident =>
            val sym = new VarSymbol(id)
            newCtx += id.name -> sym
            RcdField(Term.Lit(StrLit(id.name)).withLocOf(id), sym.ref(id))
              :: DefineVar(sym, rhs_t)
              :: LetDecl(sym, annotations)
              :: acc
          case lit: Literal =>
            reportUnusedAnnotations
            RcdField(Term.Lit(lit).withLocOf(lit), rhs_t) :: acc
          case Bra(Round, inner) =>
            reportUnusedAnnotations
            RcdField(term(inner), rhs_t) :: acc
          case _ =>
            raise(ErrorReport(msg"Unexpected record key shape." -> rlhs.toLoc :: Nil))
            RcdField(Term.Error, rhs_t) :: acc
        newCtx.givenIn:
          go(sts, Nil, newAcc)
      case (hd @ LetLike(kw @ Keywrd(`let`), Apps(id: Ident, tups), rhso, N)) :: sts
      if tups.isEmpty || id.name.headOption.exists(_.isLower) =>
        val sym =
          fieldOrVarSym(LetBind, id)
        log(s"Processing `let` statement $id (${sym}) ${ctx.outer}")
        members.get(id.name).foreach: s =>
          raise(ErrorReport(msg"Name '${id.name}' is already used"
            -> hd.toLoc :: msg"by a member declared in the same block" -> s.toLoc :: Nil))
        val newAcc = rhso match
          case S(rhs) =>
            val rrhs = tups.foldRight(rhs):
              InfixApp(_, Keywrd(Keyword.`=>`), _)
            mkLetBinding(kw, sym, term(rrhs), annotations) reverse_::: acc
          case N =>
            if tups.nonEmpty then
              raise(ErrorReport(msg"Expected a right-hand side for let bindings with parameters" -> hd.toLoc :: Nil))
            LetDecl(sym, annotations).mkLocWith(kw) :: acc
        (ctx + (id.name -> sym)) givenIn:
          go(sts, Nil, newAcc)
      case (tree @ LetLike(Keywrd(`let`), lhs, _, N)) :: sts =>
        raise(ErrorReport(msg"Unsupported let binding shape" -> tree.toLoc :: Nil))
        go(sts, Nil, Term.Error :: acc)
      case Def(lhs, rhs) :: sts =>
        reportUnusedAnnotations
        lhs match
        case id: Ident =>
          val r = term(rhs)
          ctx.get(id.name) match
          case S(elem) =>
            elem.symbol match
            case S(sym: (LocalSymbol | TermSymbol)) => go(sts, Nil, DefineVar(sym, r) :: acc)
          case N =>
            // TODO lookup in members? inherited/refined stuff?
            raise(ErrorReport(msg"Name not found: ${id.name}" -> id.toLoc :: Nil))
            go(sts, Nil, Term.Error :: acc)
        case App(base, args) =>
          go(Def(base, InfixApp(args, Keywrd(Keyword.`=>`), rhs)) :: sts, Nil, acc)
        case _ =>
          raise(ErrorReport(msg"Unrecognized definitional assignment left-hand side: ${lhs.describe}"
            -> lhs.toLoc :: Nil)) // TODO BE
          go(sts, Nil, Term.Error :: acc)
      case (td @ TermDef(k, nme, rhs)) :: sts =>
        log(s"Processing term definition $nme")
        td.symbName match
        case S(L(d)) => raise(d)
        case _ => ()
        td.name match
          case R(id) =>
            val sym = members.getOrElse(id.name, die)
            val owner =
              // * Instance declarations are not meant to be exported as externally-available members,
              // * even when declared within some class or module.
              if (k is Ins) then N else ctx.outer.inner
            if (k is MutVal) && owner.isEmpty then
              raise:
                ErrorReport:
                  msg"Mutable 'val' definitions are only valid as members of a module, object, or class definition" -> td.toLoc
                  :: Nil
              return go(sts, Nil, acc)
            if owner.isDefined && !identifierPattern.matches(id.name) then
              raise:
                ErrorReport:
                  msg"Illegal ${k.desc} member name: '${id.name}'" -> nme.toLoc
                  :: illegalMemberNameTail
              return go(sts, Nil, acc)
            val isMethod = owner.exists(_.isInstanceOf[ClassSymbol])
            val tdf = ctx.nest(OuterCtx.NonReturnContext).givenIn: newCtx ?=>
              // * Add type parameters to context
              val (tps, newCtx1) = td.typeParams match
                case S(t) => 
                  val (tps, ctx) = typeParams(t)
                  (S(tps), ctx)
                case N => (N, ctx)
              // * Add parameters to context
              var newCtx = newCtx1
              val pss = td.paramLists.map: ps =>
                val (res, newCtx2) = funParams(ps)(using newCtx)
                newCtx = newCtx2
                res
              // * Elaborate signature
              val st = td.annotatedResultType.orElse(newSignatureTrees.get(id.name))
              val s = st.map:
                // unwrap possible module modifier
                // e.g, `fun f: module M`
                //              ^^^^^^
                case TypeDef(Mod, st, N) => term(st)(using newCtx)
                case st => term(st)(using newCtx)
              val body: Opt[Term] = rhs match
                case N => N
                case _ if ctx.mode is Mode.Light => S(Term.Missing)
                case S(rhs) => S:
                  val nonLocalRetHandler = TempSymbol(N, s"nonLocalRetHandler$$${id.name}")
                  newCtx.nest(OuterCtx.Function(nonLocalRetHandler)).givenIn: newCtx ?=>
                    val b = term(rhs)(using newCtx)
                    if nonLocalRetHandler.directRefs.isEmpty then b else
                      mkEffectHandleAbortive(
                        nonLocalRetHandler,
                        "‹non-local return effect›",
                        EffectHandlerMethodSpec("ret", S("value"), requireEffectMethodValue("ret", _)) :: Nil,
                        b,
                      )
              val r = FlowSymbol(s"‹result of ${sym}›")
              
              val mfn = st match
                // st.isModified(Mod) indicates if the function marks
                // its result as "module". e.g, `fun f: module M`
                //                                      ^^^^^^
                case S(st) if st.isModified(Mod) => 
                  Modulefulness.ofSign(s)(true)
                case _ =>
                  Modulefulness.none
              
              val tsym = TermSymbol(k, owner, id) // TODO?
              val tdf = TermDefinition(k, sym, tsym, pss, tps, s, body, 
                TermDefFlags.empty.copy(isMethod = isMethod), mfn, annotations, N).withLocOf(td)
              tsym.defn = S(tdf)
              sym.tsym = S(tsym)
              
              tdf
            go(sts, Nil, tdf :: acc)
          case L(d) =>
            reportUnusedAnnotations
            raise(d)
            go(sts, Nil, acc)
      case (td @ TypeDef(k, head, rhs)) :: sts =>
        val owner = ctx.outer.inner
        
        assert((k is Als) || (k is Cls) || (k is Mod) || (k is Obj) || (k is Pat), k)
        val body = td.withPart
        
        td.symbName match
        case S(L(d)) => raise(d)
        case _ => ()
        val nme = td.name match
          case R(id) => id
          case L(d) =>
            raise(d)
            return go(sts, Nil, acc)
        
        if owner.isDefined && !identifierPattern.matches(nme.name) then
          raise:
            ErrorReport:
              msg"Illegal ${k.desc} member name: '${nme.name}'" -> nme.toLoc
              :: illegalMemberNameTail
          return go(sts, Nil, acc)
        
        val sym = members.getOrElse(nme.name, lastWords(s"Symbol not found: ${nme.name}"))
        
        val outerCtx = ctx
        
        var newCtx = S(td.symbol).collectFirst:
            case s: InnerSymbol => s
          .fold(ctx.nest(OuterCtx.NonReturnContext))(ctx.nestInner(_))
        
        val tps = td.typeParams match
          case S(ts) =>
            ts.tys.flatMap: targ =>
              val (id, vce) = targ match
                case id: Ident =>
                  (id, N)
                case Modified(Keywrd(Keyword.`in`), id: Ident) =>
                  (id, S(false))
                case Modified(Keywrd(Keyword.`out`), id: Ident) =>
                  (id, S(true))
              val vs = VarSymbol(id)
              val res = TyParam(FldFlags.empty, vce, vs)
              vs.decl = S(res)
              res :: Nil
          case N => Nil
        
        newCtx ++= tps.map(tp => tp.sym.name -> tp.sym) // TODO: correct ++?
        
        val isDataClass = annotations.exists:
          case Annot.Modifier(Keyword.`data`) => true
          case _ => false
        
        val pss = td.paramLists.map: ps =>
          val (res, newCtx2) =
            given Ctx = newCtx
            params(ps, isDataClass, k is Pat)
          newCtx = newCtx2
          // Spread parameters are not supported in class parameters.
          res.restParam.foreach: rp =>
            raise(ErrorReport(
              msg"Spread parameters are not supported in class parameters." -> rp.toLoc :: Nil))
          res.copy(restParam = N)
        
        def withFields(extraParams: Ls[ParamList])(using Ctx)(fn: (Ctx) ?=> (Term.Blk, Ctx)): (Term.Blk, Ctx) =
          softAssert(pss.sizeCompare(td.clsParams) === 0,
            s"mismatched parameter list numbers ${pss} vs ${td.clsParams}")
          val fields: Ls[Statement] = pss.zip(td.clsParams).flatMap: (ps, cps) =>
            // TODO: handle this gracefully (could be caused by erroneous input code)
            softTODO(ps.params.sizeCompare(cps) === 0,
              s"mismatched param list lengths ${ps.params} vs ${cps}")
            ps.params.zip(cps).flatMap: (p, cp) =>
              // For class-like types, "desugar" the parameters into additional class fields.
              
              val owner = td.symbol match
                // Any MemberSymbol should be an InnerSymbol, except for TypeAliasSymbol, 
                // but type aliases should not call this function.
                case s: InnerSymbol => S(s)
                case _: TypeAliasSymbol => die
              
              if p.flags.isVal || isDataClass
              then
                val k = if p.flags.mut then MutVal else ImmutVal
                val fsym = BlockMemberSymbol(p.sym.nme, Nil)
                val tsym = cp
                cp.decl = S(p)
                val fdef = TermDefinition(
                  k,
                  fsym,
                  tsym,
                  Nil, N, N,
                  S(p.sym.ref()),
                  TermDefFlags.empty.copy(isMethod = (k is Cls)),
                  p.modulefulness,
                  Nil,
                  N,
                ).withLocOf(p)
                assert(p.fldSym.isEmpty)
                p.fldSym = S(fsym)
                fsym.tsym = S(tsym)
                tsym.defn = S(fdef)
                fdef :: Nil
              else
                val psym = TermSymbol(LetBind, owner, p.sym.id)
                val decl = LetDecl(psym, Nil)
                val defn = DefineVar(psym, p.sym.ref())
                p.fldSym = S(psym)
                decl :: defn :: Nil
          
          // Also create fields for constructor(...) params (always use LetBind path)
          val ctorFields: Ls[Statement] = extraParams.flatMap: ps =>
            ps.params.flatMap: p =>
              val owner = td.symbol match
                case s: InnerSymbol => S(s)
                case _: TypeAliasSymbol => die
              val psym = TermSymbol(LetBind, owner, p.sym.id)
              val decl = LetDecl(psym, Nil)
              val defn = DefineVar(psym, p.sym.ref())
              p.fldSym = S(psym)
              decl :: defn :: Nil
          
          val allFields = fields ::: ctorFields
          
          val ctxWithFields =
            val valParams = allFields.collect:
              case f: TermDefinition =>
                f.sym.nme -> f.sym
            val params = allFields.collect:
              case (f: LetDecl) =>
                f.sym.nme -> f.sym
            ctx.withMembers(valParams) ++ params
          
          val (blk, c) = fn(using ctxWithFields)
          val blkWithFields: Blk = blk.copy(stats = allFields ::: blk.stats)
          ObjBody.extractMembers(blkWithFields) match
            case R(_) =>
              (blkWithFields, c)
            case L(errs) =>
              errs.foreach(raise)
              (blk, c)
        
        def mkBody(extraParams: Ls[ParamList])(using Ctx) = withFields(extraParams):
          body match
          case N | S(Error()) => (new Blk(Nil, Term.Lit(UnitLit(false))), ctx)
          case S(b: Block) => block(b, hasResult = false)
          case S(t) =>
            raise(ErrorReport(
              msg"Illegal body of ${k.desc} definition (should be a block; found ${t.describe})." -> t.toLoc :: Nil))
            (new Blk(Nil, Term.Lit(UnitLit(false))), ctx)
        
        val defn = k match
        case Als =>
          val alsSym = td.symbol.asInstanceOf[TypeAliasSymbol] // TODO improve `asInstanceOf`
          // newCtx.nest(S(alsSym)).givenIn:
          newCtx.nestLocal.givenIn:
            assert(pss.isEmpty)
            assert(body.isEmpty)
            val d =
              given Ctx = newCtx
              semantics.TypeDef(alsSym, sym, tps, rhs.map(term(_)), N, annotations)
            alsSym.defn = S(d)
            d
        case Pat =>
          val patSym = td.symbol.asInstanceOf[PatternSymbol] // TODO improve `asInstanceOf`
          newCtx.givenIn:
            if pss.length > 1 then raise:
                ErrorReport:
                  msg"Multiple parameter lists are not supported for this definition." ->
                    td.toLoc :: Nil
            // Pattern definition should not have a body like class definition.
            assert(body.isEmpty)
            val ps = pss.headOption
            val allParams = ps.fold(Nil):
              _.params.flatMap:
                // Only `pat` flag is `true`.
                case p @ Param(flags = FldFlags(false, false, true, false)) => S(p)
                // All flags are `false`.
                case p @ Param(flags = FldFlags(false, false, false, false)) => S(p)
                case Param(flags, sym, _, _) =>
                  raise(ErrorReport(msg"Unexpected pattern parameter ${sym.name} with modifiers: ${flags.show}" -> sym.toLoc :: Nil))
                  N
            // The following iteration filters out:
            // 1. pattern parameters, e.g., `T` in `pattern Nullable(pattern T) = ...`;
            // 2. extraction bindings, e.g., `value` in `pattern Middle(value) = ...`; and
            // 3. the rest are reported as invalid parameters.
            val (patternParams, extractionParams) = allParams.partition(_.flags.pat)
            log(s"`${patSym.nme}`'s pattern parameters: ${patternParams.mkString("[", ", ", "]")}")
            log(s"`${patSym.nme}`'s extraction parameters: ${extractionParams.mkString("[", ", ", "]")}")
            // Empty pattern body is considered as wildcard patterns.
            val rhs = td.rhs.getOrElse:
              raise(ErrorReport(msg"Pattern definitions must have a body." -> td.toLoc :: Nil))
              Tree.Under()
            // Elaborate the pattern body with the pattern parameters.
            val pat = pattern(rhs)(using ctx ++ patternParams.iterator.map(p => p.sym.name -> p.sym))
            // Report all invalid variables we found in the top-level pattern.
            pat.variables.report
            // Note that the remaining variables have not been bound to any
            // `VarSymbol` yet. Thus, we need to pair them with the extraction
            // parameters. We only report warnings for unbound variables
            // because they are harmless. Variables used in guard conditions
            // (from `where` clauses) are not considered useless.
            val guardedNames = pat.varNamesUsedInGuards
            pat.variables.varMap.foreach: (name, aliases) =>
              extractionParams.find(_.sym.name == name) match
                case S(param) => aliases.foreach(_.symbol = param.sym)
                case N if !guardedNames.contains(name) =>
                  raise(WarningReport(msg"Unused pattern binding: $name." -> aliases.head.toLoc :: Nil))
                case _ => ()
            scoped("ucs:ups")(log(s"elaborated pattern body: ${pat.showDbg}"))
            scoped("ucs:ups:tree")(log(s"elaborated pattern body: ${pat.showAsTree}"))
            // `paramsOpt` is set to `N` because we don't want parameters to
            // appear in the generated class's constructor.
            val pd = PatternDef(owner, patSym, sym, tps, allParams,
              patternParams, extractionParams, pat, annotations)
            patSym.defn = S(pd)
            pd
        case k: (Mod.type | Obj.type) =>
          val modSym = td.symbol.asInstanceOf[ModuleOrObjectSymbol] // TODO: improve `asInstanceOf`
          newCtx.givenIn:
            trace(s"Processing module/object definition $nme"):
              val comp = sym.asCls match
                case comp @ S(_) =>
                  assert(sym.asAls.isEmpty)
                  comp
                case N => sym.asAls
              log(s"Companion: ${comp}")
              val md =
                val (bod, c) = mkBody(Nil)
                ModuleOrObjectDef(owner, modSym, sym,
                  tps, pss.headOption, pss.tailOr(Nil), newOf(td), k, ObjBody(bod), comp, annotations)(outerCtx.scope)
              modSym.defn = S(md)
              md
        case Cls =>
          val clsSym = td.symbol.asInstanceOf[ClassSymbol] // TODO: improve `asInstanceOf`
          // Extract constructor(...) param lists from the class body
          // Handles both single param lists: constructor(x, y)
          // and multi param lists: constructor(x, y)(u, v)
          val auxCtorParamTrees: Ls[Tree] = body match
            case S(blk: Block) => blk.stmts.flatMap:
              case Constructor(ConstructorParamDecl(paramTrees)) =>
                paramTrees
              case _ => Nil
            case _ => Nil
          val auxCtorPss = auxCtorParamTrees.map: ps =>
            val (res, newCtx2) =
              given Ctx = newCtx
              params(ps, isDataClass, false)
            newCtx = newCtx2
            res.restParam.foreach: rp =>
              raise(ErrorReport(
                msg"Spread parameters are not supported in class parameters." -> rp.toLoc :: Nil))
            res.copy(restParam = N)
          newCtx.givenIn:
            trace(s"Processing class definition $nme"):
              val comp = sym.asMod
              log(s"Companion: ${comp}")
              val allCtorPss = pss ::: auxCtorPss
              val tsym = if allCtorPss.nonEmpty then
                val ctsym = ClassCtorSymbol(Fun, S(clsSym), clsSym.id)
                val ctdef =
                  TermDefinition(
                    Fun,
                    sym,
                    ctsym,
                    allCtorPss,
                    S(tps.map(tp => Param(FldFlags.empty, tp.sym, N, Modulefulness.none))),
                    S(clsSym.ref()),
                    N,
                    TermDefFlags.empty,
                    Modulefulness.none,
                    annotations.collect: 
                      case a @ Annot.Modifier(Keyword.`declare`) => a
                    ,
                    S(clsSym),
                  )
                ctsym.defn = S(ctdef)
                if pss.nonEmpty then sym.tsym = S(ctsym)
                // Note: do NOT set sym.tsym for constructor(...) classes; they are not callable as functions.
                S(ctsym)
              else N
              val cd =
                val (bod, c) = mkBody(auxCtorPss)
                ClassDef(owner, Cls, clsSym, sym, tsym, tps, pss, newOf(td), ObjBody(bod), annotations, comp, auxCtorParams = auxCtorPss)
              clsSym.defn = S(cd)
              cd
        go(sts, Nil, defn :: acc)
      case Annotated(annotation, target) :: sts =>
        go(target :: sts, annotations ++ annot(annotation), acc)
      // * With tight right precedence, `#config(args)` is parsed as `App(Directive(config, Tup()), Tup(args))`.
      // * Reconstruct as `Directive(config, Tup(args))` and re-process.
      case App(Directive(prefix, _), args) :: sts =>
        go(Directive(prefix, args) :: sts, annotations, acc)
      case Directive(Ident("config"), Tup(args)) :: sts =>
        reportUnusedAnnotations
        val modify = ConfigParser.parseOverrides(args)
        go(sts, Nil, SetConfig(modify) :: acc)
      case Directive(Ident(name), _) :: sts =>
        raise(ErrorReport(
          msg"Unknown directive '#${name}'" -> sts.headOption.flatMap(_.toLoc) :: Nil,
          source = Diagnostic.Source.Compilation))
        go(sts, annotations, acc)
      case (dir @ Directive(prefix, _)) :: sts =>
        raise(ErrorReport(
          msg"Expected a directive name after '#', but found ${prefix.describe}" -> prefix.toLoc :: Nil,
          source = Diagnostic.Source.Compilation))
        go(sts, annotations, acc)
      case (st: Tree) :: sts =>
        // TODO reject plain term statements? Currently, `(1, 2)` is allowed to elaborate (tho it should be rejected in type checking later)
        val res = annotations.foldLeft(term(st)):
          case (acc, ann) => Term.Annotated(ann, acc)
        sts match
        case Nil => (mkBlk(acc, S(res), hasResult), ctx)
        case _ => go(sts, Nil, res :: acc)
    end go
    
    ctx.withMembers(members).givenIn:
      go(blk.desugStmts, Nil, Nil)
  
  
  def mkBlk(acc: Ls[Statement], res: Opt[Term], hasResult: Bool): Blk | Rcd =
    // TODO forbid certain kinds of terms in records
    val isRcd = acc.exists:
      case _: (RcdField | RcdSpread) => true
      case _ => false
    if isRcd then Term.Rcd(mut = false, (res.toList ::: acc).reverse)
    else Blk(acc.reverse, res.getOrElse:
      if hasResult
        then unit
        else Term.Lit(UnitLit(false))
    )
  
  def newOf(td: TypeDef): Ctxl[Opt[Term.New]] =
    td.extension
    match
    case S(ext) => S(term(ProperNew(S(ext), N)))
    case N => N
    match
    case S(n: Term.New) => S(n)
    case S(trm) =>
      raise:
        ErrorReport:
          msg"Unexpected shape of extension clause: ${trm.describe}" -> trm.toLoc :: Nil
      N
    case N => N
  
  def fieldOrVarSym(k: TermDefKind, id: Ident)(using Ctx): TermSymbol | VarSymbol =
    if ctx.outer.inner.isDefined then TermSymbol(k, ctx.outer.inner, id)
    else VarSymbol(id)
  
  def param(t: Tree, inUsing: Bool, inDataClass: Bool): Ctxl[Diagnostic \/ (Param, Opt[SpreadKind])] =
    t.desugared.asParam(inUsing).map:
      case pt @ ParamTree(flags, id, sign, spd, modifiers) =>
        log(s"Elaborating ParamTree: ${pt}")
        val flg = flags.copy(isVal = flags.isVal || inDataClass)
        val sym = VarSymbol(id)
        val sig = sign.map(term(_))
        val p = Param(flg, sym, sig, Modulefulness.ofSign(sig)(Mod in modifiers))
        sym.decl = S(p)
        (p, spd)
  
  def funParams(t: Tree): Ctxl[(ParamList, Ctx)] =
    val ps_ctx = params(t, inDataClass = false, inPattern = false)
    def checkFlags(p: Param): Unit =
      if p.flags.isVal || p.flags.mut then
        raise(ErrorReport(msg"Illegal function parameter modifiers: ${p.flags.show}" -> p.sym.toLoc :: Nil))
    ps_ctx._1.params.foreach(checkFlags)
    ps_ctx._1.restParam.foreach(checkFlags)
    ps_ctx
  
  /** Elaborate a subtyping constraint. */
  def constraint(lhs: Tree, op: "<:<" | ">:>", rhs: Tree): Ctxl[SubConstraint] =
    val l = term(lhs)
    val r = term(rhs)
    val dir = op match
      case "<:<" => SubDir.Sub
      case ">:>" => SubDir.Sup
    SubConstraint(l, r, dir)
 
  /** Elaborate a subtyping constraint that may be malformed. */
  def maybeConstraint(t: Tree): Ctxl[Option[SubConstraint]] =
    t match
    case OpApp(lhs, Ident(op : ("<:<" | ">:>")), rhs :: Nil) =>
      S(constraint(lhs, op, rhs))
    case _ =>
      raise(ErrorReport(msg"Illegal constraint syntax." -> t.toLoc :: Nil))
      N

  /** Elaborate a parameter list of a term or a definition.
   * @param inDataClass Whether the parameter list belongs to a data class.
   * @param inPattern Whether the parameter list belongs to a pattern definition.
   *                  If `inPattern` is `true`, only parameters with `pat` flag
   *                  will be added to the context.
   */
  def params(t: Tree, inDataClass: Bool, inPattern: Bool): Ctxl[(ParamList, Ctx)] = t match
    case Tup(ps) =>
      def go(ps: Ls[Tree], acc: Ls[Param], ctx: Ctx, flags: ParamListFlags): (ParamList, Ctx) =
        ps match
        case Nil => (ParamList(flags, acc.reverse, N).withLocOf(t), ctx)
        case hd :: tl =>
          val isCtxParam = hd.isModified(Ins)
          val inUsing = flags.ctx || isCtxParam
          param(hd, inUsing, inDataClass)(using ctx) match
          case R((p, spd)) =>
            if isCtxParam && acc.nonEmpty then
              raise(ErrorReport(msg"Keyword `using` must occur before all parameters." -> hd.toLoc :: Nil))
            val newCtx = if !inPattern || p.flags.pat then ctx + (p.sym.name -> p.sym) else ctx
            val newFlags = flags.copy(ctx = inUsing)
            spd match
            case S(spd) =>
              if spd is SpreadKind.Lazy then
                raise(ErrorReport(msg"Lazy spread parameters not allowed." -> hd.toLoc :: Nil))
              if tl.isEmpty then 
                (ParamList(flags, acc.reverse, S(p)).withLocOf(t), newCtx)
              else
                raise(ErrorReport(msg"Spread parameters must be the last in the parameter list." -> hd.toLoc :: Nil))
                go(tl, p :: acc, newCtx, newFlags)
            case N => go(tl, p :: acc, newCtx, newFlags)
          case L(d) => raise(d); go(tl, acc, ctx, flags)
      go(ps, Nil, ctx, ParamListFlags.empty)
  
  def ident(id: Ident)(using Ctx): Ctxl[Opt[Term]] = ctx.get(id.name) match
    case S(elem) => S(elem.ref(id))
    case N =>
      state.builtinOpsMap.get(id.name) match
      case S(bi) => S(bi.ref(id))
      case N => N
  
  def pattern(t: Tree): Ctxl[Pattern] =
    import ucs.{Ctor, unapply, error}, ucs.extractors.*, Keyword.*, Pattern.*, InvalidReason.*
    given TraceLogger = tl
    /** String range bounds must be single characters. */
    def isInvalidStringBounds(lo: StrLit, hi: StrLit)(using Raise): Bool =
      val ds = collection.mutable.Buffer.empty[(Message, Option[Loc])]
      if lo.value.length =/= 1 then
        ds += msg"The lower bound of character ranges must be a single character." -> lo.toLoc
      if hi.value.length =/= 1 then
        ds += msg"The upper bound of character ranges must be a single character." -> hi.toLoc
      if ds.nonEmpty then error(ds.toSeq*)
      ds.nonEmpty
    /** Resolve an identifier. We need to perform a very preliminary check to
     *  determine whether this identifier refers to a pattern, a class, an
     *  object, or creates a new binding.
     * 
     *  FIXME: This routine is insufficient to look up definitions defined
     *  later in the program. */
    def ident(id: Ident)(using Ctx): Ctxl[Opt[Term]] = scoped("ucs:pattern:resolution"):
      log(s"resolve ${id}")
      ctx.get(id.name) match
      case S(elem) =>
        log("has elem!")
        elem.symbol.flatMap:
          case vs: VarSymbol => vs.decl match
            case S(d) if d.isPatternConstructor => S(elem.ref(id))
            case S(_) | N => N
          case sym: Symbol => sym.asCls.orElse(sym.asObj).orElse(sym.asPat) match
            case S(_) => S(elem.ref(id))
            case N => N
      case N =>
        state.builtinOpsMap.get(id.name) match
        case S(bi) => S(bi.ref(id))
        case N => N
    /** Elaborate arrow patterns like `p => t`. Meanwhile, report all invalid
     *  variables we found in `p`. */
    def arrow(lhs: Tree, rhs: Tree): Ctxl[Pattern] =
      val pattern = go(lhs)
      // The symbol allocated here will be bound in `split` to the values
      // destructed from the scrutinee.
      val variables = pattern.variables.allocate
      // The `VarSymbol` created here is used as the parameters of the
      // lambda expression generated by extraction (such as `p => t`).
      // To avoid duplicating `t`, we generate a lambda function before the
      // branch starts, which will be called if the `split` succeeds.
      // - `contextEntries` will be added to the context
      // - `correspondence` is mapping from symbols representing variables
      //   in the pattern to symbols for parameters to be used in the `term`.
      val (contextEntries, correspondence) = variables.iterator.map:
        case (name, symbol) =>
          // We create a symbol specifically for `Param` for each variable to
          // avoid redundantly redeclaring symbols in `Scope` during code
          // generation, which triggers the assertion in `Scope.addToBindings`.
          val parameterSymbol = VarSymbol(new Ident(symbol.name))
          (name -> parameterSymbol, symbol -> parameterSymbol)
      .toList.unzip
      pattern.variables.report // Report all invalid variables we found in `pattern`.
      Transform(pattern, correspondence, term(rhs)(using ctx ++ contextEntries))
    /** Elaborate tuple patterns like `[p1, p2, ...ps, pn]`. */
    def tuple(ts: Ls[Tree]): Ctxl[Pattern.Tuple] =
      // We are accumulating two components: the leading patterns, the spread
      // part including the trailing patterns.
      val z = (Ls[Pattern](), N: Opt[(SpreadKind, Pattern, Ls[Pattern])])
      val (leading, spread) = ts.foldLeft(z):
        case (acc @ (_, S(_)), t: Spread) =>
          // Found two `...p`s in the same tuple pattern. Report an error.
          raise(ErrorReport(msg"Multiple spread patterns are not supported." -> t.toLoc :: Nil))
          acc // Do not modify the accumulator and skip this `Spread`.
        case ((leading, N), Spread(ellipsis, S(t))) =>
          // Found `...p`, elaborate `p` and assign it to the spread pattern.
          (leading, S(SpreadKind.fromKw(ellipsis), go(t), Nil))
        case ((leading, N), Spread(ellipsis, N)) =>
          // Found `...` (no following patterns), which means the spread part
          // will not be further matched. Set the spread pattern to `Wildcard`.
          (leading, S(SpreadKind.fromKw(ellipsis), Wildcard(), Nil))
        case ((leading, N), t) => 
          // Found a tuple field while the spread pattern is not set. Add the
          // elaborated pattern to the leading patterns.
          (go(t) :: leading, N)
        case ((leading, S((spreadKind, spread, trailing))), t) => 
          // Found a tuple field while the spread pattern has been set. Add the
          // elaborated pattern to the trailing patterns.
          (leading, S((spreadKind, spread, go(t) :: trailing)))
      Tuple(leading.reverse, spread)
    /** Elaborate record patterns like `(a: p1, b: p2, ...pn)`. */
    def record(ps: Ls[Tree]): Ctxl[Pattern.Record] =
      val entries = ps.iterator.map(_.desugared).foldLeft(List[(Ident, Pattern)]()):
        case (acc, InfixApp(id: Ident, Keywrd(Keyword.`:`), p)) => (id, go(p)) :: acc
        case (acc, InfixApp(key: StrLit, Keywrd(Keyword.`:`), p)) =>
          ((Ident(key.value): Ident).withLocOf(key), go(p)) :: acc
        case (acc, Pun(false, p)) => (p, Variable(p)) :: acc
        case (acc, t) =>
          raise(ErrorReport(msg"Unexpected record property pattern." -> t.toLoc :: Nil))
          acc
      Record(entries.reverse)
    /** Elaborate a pattern argument. */
    def arg(t: Tree): Ctxl[Pattern \/ Pattern] = t match
      case TypeDef(syntax.Pat, body, N) => L(go(body))
      case _ => R(go(t))
    def go(t: Tree): Ctxl[Pattern] = trace[Pattern](s"Elab pattern ${t.showDbg}", r => s"~> $r"):
      t match
      // Annotated patterns like `@compile P`.
      case Tree.Annotated(annotation, target) =>
        go(target).annotate(term(annotation), t.toLoc)
      // Brackets.
      case Bra(BracketKind.Round | BracketKind.Curly, t) => go(t)
      // Tuple patterns like `[p1, p2, ...ps, pn]`.
      case TyTup(ps) => tuple(ps)
      case Tup(ps) => tuple(ps)
      case t: syntax.Literal => Literal(t)
      // Negation patterns: `~p`
      case App(Ident("~"), Tup(p :: Nil)) => Negation(go(p))
      // Negative integer and decimal literals.
      case app @ App(Ident("-"), Tup(IntLit(n) :: Nil)) =>
        Literal(IntLit(-n).withLocOf(app))
      case app @ App(Ident("-"), Tup(DecLit(n) :: Nil)) =>
        Literal(DecLit(-n).withLocOf(app))
      // Union and intersection patterns: `p | q` and `p & q`
      case App(Ident(op @ ("|" | "&")), Tup(rhs :: Nil)) =>
        go(rhs) // unary uses of `|` and `&` are no-ops
      case OpApp(lhs, Ident(op @ ("|" | "&")), rhs :: Nil) =>
        Composition(op === "|", go(lhs), go(rhs))
      // Constructor patterns with pattern arguments and arguments.
      case App(ctor: Ctor, Tup(argTrees)) =>
        Constructor(term(ctor), S(argTrees.map(go(_))))
      // `[p1, p2, ...ps, pn] => term`: All patterns are in the `TyTup`.
      case (lhs: TyTup) `=>` rhs => arrow(lhs, rhs)
      // `pattern => term`: Note that `pattern` is wrapped in a `Tup`.
      case Tup(lhs) `=>` rhs => lhs match
        case p @ Pun(false, _) :: Nil => record(p)
        case p @ InfixApp(_: Ident, Keywrd(Keyword.`:`), _) :: Nil => record(p)
        case lhs :: Nil => arrow(lhs, rhs)
        case _ :: _ | Nil => ??? // TODO: this case reached by, eg, `pattern p = () => Unit`
      case p as q => q match
        // `p as id` is elaborated into alias if `id` is not a constructor.
        case id: Ident => ident(id) match
          case S(target) if target.symbol.exists(_.isInstanceOf[VarSymbol]) =>
            // If the target is a variable, we should shadow it. This check is
            // probably insufficient as there are more cases.
            go(p) binds id
          case S(target) => Chain(go(p), Constructor(target, N))
          case N => go(p) binds id // Fallback to alias.
        // `p as q` where `q` is not an identifier is elaborated into chain.
        case _: Tree => Chain(go(p), go(q))
      case p where t =>
        val q = go(p)
        Guarded(q, term(t)(using ctx ++ q.variables.allocate))
      case Under() => Pattern.Wildcard().withLocOf(t)
      // Singleton blocks like `{1}`.
      case Block(p :: Nil) => go(p)
      // Record patterns like `(a: p1, b: p2, ...pn)`.
      case Block(ps) => record(ps)
      // A single pun pattern is a record pattern.
      case p @ Pun(false, _) => record(p :: Nil)
      // A single record field is a record pattern.
      case p @ InfixApp(_, Keywrd(Keyword.`:`), _) => record(p :: Nil)
      // Range patterns. We can also desugar them into disjunctions of all the
      // literals in the range.
      case (lower: StrLit) to (incl, upper: StrLit) =>
        if isInvalidStringBounds(lower, upper) then Pattern.Wildcard()
        else Pattern.Range(lower, upper, incl)
      case (lower: IntLit) to (incl, upper: IntLit) => Pattern.Range(lower, upper, incl)
      case (lower: DecLit) to (incl, upper: DecLit) => Pattern.Range(lower, upper, incl)
      case (lower: syntax.Literal) to (_, upper: syntax.Literal) =>
        raise(ErrorReport(msg"The upper and lower bounds of range patterns should be literals of the same type." -> t.toLoc :: Nil))
        Pattern.Wildcard()
      // String concatenation patterns: `p ~ q`. Currently, not supported by the
      // pattern compilation. We elaborate them to keep the consistency with the
      // pattern translation.
      case OpApp(lhs, Ident("~"), rhs :: Nil) => Pattern.Concatenation(go(lhs), go(rhs))
      // Constructor patterns can be written in the infix form.
      case OpApp(lhs, op, rhs :: Nil) => Pattern.Constructor(term(op), S(Ls(go(lhs), go(rhs))))
      // Constructor patterns without arguments
      case id @ Ident(name) if name.isUncapitalized => Variable(id)
      case id @ Ident(name) => ident(id) match
        case S(target) => Constructor(target, N)
        case N =>
          raise:
            ErrorReport(msg"Pattern name not found: ${id.name}." -> id.toLoc :: Nil)
          Pattern.Wildcard()
      case sel: (SynthSel | Sel) => Constructor(term(sel), N)
      case _: Tree =>
        raise(ErrorReport(msg"Unrecognized pattern (${t.describe})." -> t.toLoc :: Nil))
        Pattern.Wildcard()
    go(t)
  
  def typeParams(t: Tree): Ctxl[(Ls[Param], Ctx)] = t match
    case TyTup(ps) =>
      val vs = ps.flatMap:
        case id: Ident =>
          val sym = VarSymbol(id)
          sym.decl = S(TyParam(FldFlags.empty, N, sym))
          Param(FldFlags.empty, sym, N, Modulefulness.none) :: Nil
        case t =>
          raise(ErrorReport(msg"Unsupported type parameter ${t.describe}" -> t.toLoc :: Nil))
          Nil
      (vs, ctx ++ vs.map(p => p.sym.name -> p.sym))
  
  def importFrom(sts: Block): Ctxl[(Blk, Ctx)] =
    given UnderCtx = new UnderCtx(N)
    val (res, newCtx) = block(sts, hasResult = false)
    // TODO handle name clashes
    (res, newCtx)

  def topLevel(sts: Block): Ctxl[(Blk, Ctx)] =
    given UnderCtx = new UnderCtx(N)
    val (res, ctx) = block(sts, hasResult = false)
    computeVariances(res)
    (res, ctx)
  
  def computeVariances(s: Statement): Unit =
    val trav = VarianceTraverser()
    def go(s: Statement): Unit = s match
      case TermDefinition(k, sym, tsym, pss, _, sign, body, r, _, _, _) =>
        pss.foreach(ps => ps.params.foreach(trav.traverseType(S(false))))
        sign.foreach(trav.traverseType(S(true)))
        body match
          case S(b) =>
            go(b)
          case N =>
      case ClassDef(sym, tps, pso, body) =>
        pso.foreach: ps =>
          ps.foreach: p =>
            p.sign.foreach(trav.traverseType(S(true)))
        body.blk.stats.foreach(go)
        // s.subStatements.foreach(go)
      case _ =>
        s.subStatements.foreach(go)
    while trav.changed do
      trav.changed = false
      go(s)
  
  class VarianceTraverser(var changed: Bool = true) extends Traverser:
    override def traverseType(pol: Pol)(trm: Term): Unit = trm match
      case Term.TyApp(lhs, targs) =>
        lhs.symbol.flatMap(sym => sym.asTpe) match
          case S(sym: ClassSymbol) =>
            sym.defn match
            case S(td: ClassDef) =>
              td.tparams.zip(targs).foreach:
                case (tp, targ) =>
                  if !tp.isContravariant then traverseType(pol)(targ)
                  if !tp.isCovariant then traverseType(pol.!)(targ)
            case N =>
              // TODO(sym->sym.uid)
          case S(sym: ModuleOrObjectSymbol) =>
            sym.defn match
            case S(td: ModuleOrObjectDef) =>
              td.tparams.zip(targs).foreach:
                case (tp, targ) =>
                  if !tp.isContravariant then traverseType(pol)(targ)
                  if !tp.isCovariant then traverseType(pol.!)(targ)
            case N =>
              // TODO(sym->sym.uid)
          case S(sym: TypeAliasSymbol) =>
            // TODO dedup with above...
            sym.defn match
            case S(td: semantics.TypeDef) =>
              td.tparams.zip(targs).foreach:
                case (tp, targ) =>
                  if !tp.isContravariant then traverseType(pol)(targ)
                  if !tp.isCovariant then traverseType(pol.!)(targ)
            case N =>
              TODO(sym->sym.uid)
          // case S(sym) => ???
          case N =>
            log(s"No symbol found $lhs ${lhs.symbol}")
            // ???
            () // TODO
      case Term.Ref(sym: VarSymbol) =>
        sym.decl match
          case S(ty: TyParam) =>
            if pol =/= S(true) && ty.isCovariant then
              changed = true
              ty.isCovariant = false
            if pol =/= S(false) && ty.isContravariant then
              changed = true
              ty.isContravariant = false
          // case _ => ???
          case N =>
            lastWords(s"VarSymbol ${sym.name} has no declaration")
      case _ => super.traverseType(pol)(trm)
  abstract class Traverser:
    def traverseType(pol: Pol)(trm: Term): Unit = trm match
      case Term.Lit(_) | Term.UnitVal() | Term.Error =>
      case Term.TyApp(lhs, targs) =>
        // lhs.resolveSymbol
        // targs.foreach(traverseType(pol))
        ???
      case r: Term.Ref =>
      case Term.FunTy(l, r, e) =>
        traverseType(pol.!)(l)
        traverseType(pol)(r)
        e.foreach(e => traverseType(pol)(e))
      case Term.Forall(_, _, body) =>
        traverseType(pol)(body)
      case Term.WildcardTy(in, out) =>
        in.foreach(t => traverseType(pol.!)(t))
        out.foreach(t => traverseType(pol)(t))
      case Term.CompType(lhs, rhs, _) => () // TODO:
      case Term.SynthSel(bse, nme) =>
        traverseType(pol)(bse) // FIXME: probably wrong for what we want to do
      case Term.Tup(fields) =>
        // fields.foreach(f => traverseType(pol)(f.value))
        fields.foreach(traverseType(pol))
      // case _ => ???
      case Term.Neg(ty) => 
        traverseType(pol.!)(ty)
      case _ =>
        // TODO
    def traverseType(pol: Pol)(f: Elem): Unit = f match
      case f: Fld =>
        traverseType(pol)(f.term)
        f.asc.foreach(traverseType(pol))
    def traverseType(pol: Pol)(f: Param): Unit =
      f.sign.foreach(traverseType(pol))
end Elaborator

type Pol = Opt[Bool]
extension (p: Pol) def ! : Pol = p.map(!_)
