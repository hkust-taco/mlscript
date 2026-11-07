package hkmc2
package codegen
package wasm
package text

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*

import document.*
import document.Document
import js.CodeBuilder
import semantics.*, Elaborator.State
import syntax.Tree.{BoolLit, DecLit, IntLit, StrLit, UnitLit, Ident}
import text.{Import as WasmImport, SlotSymbol as WasmSlotSymbol, Param as WasmParam}
import Message.MessageContext

import scala.collection.mutable.{ArrayBuffer as ArrayBuf, LinkedHashMap, Queue}
import scala.util.boundary, boundary.break
import sourcecode.Line

extension (instr: FoldedInstr)
  /** Returns the mneomic prefix of this instruction.
    *
    * For example, for `local.get` it returns `Some("local")`, and for `nop` it returns `None`.
    */
  private def mnemonicPrefix: Opt[Str] =
    instr.mnemonic.split('.').optionUnless(_.size == 1).map(_.head)

/** Whether `sym` is one of the builtin classes boxed as `i31ref`, i.e. `Int`, `Int31`, and `Bool`. */
private def isBoxedAsI31(sym: Symbol, ctx: Ctx): Bool =
  val builtins = ctx.elabCtx.builtins
  (sym eq builtins.Int) || (sym eq builtins.Int31) || (sym eq builtins.Bool)

extension (prim: PrimitiveType)
  /** The Wasm numeric type this unboxed primitive is represented as. */
  private[text] def wasmType: NumType = prim match
    case PrimitiveType.Int32 => I32Type
    case PrimitiveType.Int64 => I64Type
    case PrimitiveType.Float32 => F32Type
    case PrimitiveType.Float64 => F64Type

extension (ty: ValType)
  /** The neutral value of this Wasm value type, used to initialize a slot that has no explicit initializer, or `N` if
    * it has none (a non-nullable reference) or the backend cannot build one yet (`v128`).
    */
  private[text] def zeroValue: Opt[Expr] = ty match
    case refTy: RefType => Option.when(refTy.nullable)(Instructions.ref.`null`(refTy.heapType))
    case I32Type => S(Instructions.i32.const(0))
    case I64Type => S(Instructions.i64.const(0))
    case F32Type => S(Instructions.f32.const(0))
    case F64Type => S(Instructions.f64.const(0))
    case V128Type => N

extension (et: ErasedValueType)
  /** Returns the corresponding Wasm type for this [[ErasedValueType]]. */
  private[text] def wasmType(using Ctx, State): Opt[ValType] =
    import Ctx.ctx
    val elabCtx = ctx.elabCtx
    elabCtx.givenIn:
      et.canonicalize match
        case ErasedType.AnyRef(_, tpeSym) =>
          if tpeSym eq elabCtx.builtins.Object then
            S(RefType.anyref)
          else if isBoxedAsI31(tpeSym, ctx) then
            S(RefType.i31ref)
          else tpeSym match
            // Source slots also admit undefined, represented by a null reference.
            // Known receivers and newly allocated instances can still use non-null references.
            case cls: BaseTypeSymbol => ctx.getType(cls).map(RefType(_, nullable = true))
            case _: TypeAliasSymbol => N
        case ErasedType.Primitive(prim) => S(prim.wasmType)
        case _ => N
end extension

extension (sym: WasmSlotSymbol)
  /** The Wasm value type a *local* slot for `sym` should be declared with.
    *
    * Use [[FunctionCtx.slotType]] for parameter slots, which handles `anyref` widening due to virtual dispatch calling
    * conventions.
    */
  private[text] def localType(using Ctx, State): ValType =
    import Ctx.ctx
    sym match
      case cls: BaseTypeSymbol => ctx.getType(cls).fold(RefType.anyref)(RefType(_, nullable = false))
      case _: InnerSymbol => RefType.anyref
      case bms: BlockMemberSymbol =>
        // A BMS's erased type lives in its associated TermSymbol
        bms.tsym.flatMap(_.erasedType).flatMap(_.wasmType).getOrElse(RefType.anyref)
      case s: LocalVarSymbol =>
        s.erasedType.flatMap(_.wasmType).getOrElse(RefType.anyref)

extension (sym: WasmSlotSymbol)
  /** The Wasm value type a parameter slot for `sym` should be declared with. */
  private[text] def paramType(using Ctx, State): ValType =
    summon[Ctx].elabCtx.givenIn:
      sym match
        case l: LocalVarSymbol => l.erasedType.flatMap(_.wasmType).getOrElse(RefType.anyref)
        case cls: ClassSymbol => CanonicalErasedValueType(rsc = S(false), cls).wasmType.getOrElse(RefType.anyref)
        case mod: ModuleOrObjectSymbol => mod.erasedType.flatMap(_.wasmType).getOrElse(RefType.anyref)
        case _: (PatternSymbol | TopLevelSymbol | BlockMemberSymbol) => RefType.anyref

/** The declared Wasm value type of the parameter slot for `sym` at position `idx`, honoring an optional per-position
  * override (index 0 = `this`). Falls back to `sym.paramType` if no override is given.
  */
private[text] def resolveParamType(
    sym: WasmSlotSymbol,
    idx: Int,
    overrides: Opt[Seq[ValType]],
)(using Ctx, State): ValType =
  overrides.flatMap(_.lift(idx)).getOrElse(sym.paramType)

extension (param: WasmSlotSymbol -> SymIdx)
  /** Resolves the parameter slot to the declared Wasm type from its own symbol's `paramType` (no override).
    *
    * For [[FuncInfo]]s built without a [[FunctionCtx]]; those built from one should pass its `resolvedParams`, which
    * additionally honors the slot overrides.
    */
  private[text] def resolvedParam(using Ctx, State): WasmSlotSymbol -> WasmParam =
    param._1 -> WasmParam(param._2, param._1.paramType)

extension (exprs: Seq[Expr])
  /** Merges a sequence of expressions to a single `block` expression if needed. */
  def mergeAsBlock: Opt[Expr] =
    exprs match
      case Seq() => N
      case Seq(e) => S(e)
      case exprs => S(Instructions.block(
          label = N,
          children = exprs,
          resultTypes = exprs
            .flatMap(_.resultTypes)
            .optionUnless(_.exists(_ is UnreachableType))
            .fold(Seq.empty)(_.map(ty => Result(ty.asValType_!))),
        ))

  /** Similar to [[`mergeAsBlock`]], but throws an exception if `exprs` is empty. */
  def mergeAsBlock_! : Expr =
    exprs.mergeAsBlock.getOrElse:
      lastWords("Merging zero expressions into a block should not occur")
end extension

object WatBuilder:
  /** The maximum number of characters taken to be part of the identifier asscoiated with string constants. */
  val StringConstantIdentMaxLength = 16

  private val binaryIntrinsicNames: Map[Str, Str] = Map(
    "+" -> "plus_impl",
    "-" -> "minus_impl",
    "*" -> "times_impl",
    "/" -> "div_impl",
    "%" -> "mod_impl",
    "===" -> "eq_impl",
    "!==" -> "neq_impl",
    "<" -> "lt_impl",
    "<=" -> "le_impl",
    ">" -> "gt_impl",
    ">=" -> "ge_impl",
  )
  private val unaryIntrinsicNames: Map[Str, Str] = Map(
    "-" -> "neg_impl",
    "+" -> "pos_impl",
    "!" -> "not_impl",
  )

  object ExternIntrinsics:
    val SystemModule = "system"
    val SystemMemoryImportName = "mem"
    val StringFromUtf16ImportName = "mlx_str_from_utf16"
    val WasmPageSizeBytes = 65536

  def fresh(linking: FileCompilation)(using Elaborator.Ctx, TraceLogger, State): WatBuilder =
    new WatBuilder(Ctx.empty, linking)

  /** Compiles the runtime module, which every file module and worksheet imports as [[ExternIntrinsics.SystemModule]].
    * See [[WatBuilder.runtimeModule]].
    */
  def runtimeModule(using Elaborator.Ctx, TraceLogger, State, Raise): CompiledWasmFile =
    new WatBuilder(Ctx.empty, FileCompilation(Vector.empty, Set.empty)).runtimeModule()

  /** Creates the intrinsic definition for `name`.
    */
  private def createIntrinsic(name: Str)(using Ctx, Raise, State): FuncIdx =
    if Ctx.binaryOps.contains(name) then createBinaryInt31Func(name, Ctx.binaryOps(name))
    else if Ctx.unaryOps.contains(name) then createUnaryInt31Func(name, Ctx.unaryOps(name))
    else lastWords(s"Unsupported wasm intrinsic '$name'")

  private def intrinsicParamSuffixes(name: Str): Ls[Str] =
    if Ctx.binaryOps.contains(name) then Ls("lhs", "rhs") else Ls("arg")

  private def declareIntrinsicType(name: Str)(using Ctx, Raise, State): TypeIdx =
    summon[Ctx].addType(TypeInfo(
      sym = TempSymbol(N, initErasedType = N, name),
      compType = FunctionType(
        params = intrinsicParamSuffixes(name).map(nme => WasmParam(SymIdx(nme), RefType.anyref)),
        results = Seq(Result(RefType.anyref)),
      ),
      objectTag = N,
    ))

  /** Creates parameters for an intrinsic.
    */
  private def mkIntrinsicParams(suffixes: Ls[Str])(using State): Ls[TempSymbol -> SymIdx] =
    suffixes.map: suffix =>
      val sym = TempSymbol(N, initErasedType = N, suffix)
      sym -> SymIdx(suffix)

  /** Allocates the Wasm type and function definition for an intrinsic with the given signature.
    */
  private def createIntrinsicFunc(
      name: Str,
      params: Ls[TempSymbol -> SymIdx],
      body: Expr,
  )(using Ctx, Raise, State): FuncIdx =
    val funcTy = WatBuilder.declareIntrinsicType(name)
    val funcInfo = FuncInfo(
      sym = TempSymbol(N, initErasedType = N, name),
      typeUse = TypeUse(funcTy),
      params = params.map(_.resolvedParam),
      locals = Seq.empty,
      body = Seq(body),
      resultTypes = Seq(Result(RefType.anyref)),
      optionalParams = Set.empty,
    )
    summon[Ctx].addFunc(funcInfo)

  /** Builds the body for an Int31 binary operator.
    */
  private def binaryInt31Body(
      lhsIdx: LocalIdx,
      rhsIdx: LocalIdx,
      op: (Expr, Expr) => Expr,
  )(using Ctx): Expr =
    import Instructions.*
    val cond = i32.and(
      ref.test(local.get(lhsIdx, RefType.anyref), RefType.i31ref),
      ref.test(local.get(rhsIdx, RefType.anyref), RefType.i31ref),
    )
    val i31Op =
      ref.i31(
        op(
          i31.get_s(ref.cast(local.get(lhsIdx, RefType.anyref), RefType.i31ref)),
          i31.get_s(ref.cast(local.get(rhsIdx, RefType.anyref), RefType.i31ref)),
        ),
      )
    `if`(
      condition = cond,
      ifTrue = i31Op,
      ifFalse = S(unreachable),
      resultTypes = Seq(Result(RefType.anyref)),
    )
  end binaryInt31Body

  /** Creates a binary Int31 intrinsic with two parameters and body built from `op`.
    */
  private def createBinaryInt31Func(
      name: Str,
      op: (Expr, Expr) => Expr,
  )(using Ctx, Raise, State): FuncIdx =
    val params = mkIntrinsicParams(Ls("lhs", "rhs"))
    val lhsName = params.head._2
    val rhsName = params(1)._2
    val body = binaryInt31Body(LocalIdx(lhsName), LocalIdx(rhsName), op)
    createIntrinsicFunc(name, params, body)

  /** Builds the body for an Int31 unary operator.
    */
  private def unaryInt31Body(paramIdx: LocalIdx, op: Expr => Expr)(using Ctx): Expr =
    import Instructions.*
    val cond = ref.test(local.get(paramIdx, RefType.anyref), RefType.i31ref)
    val i31Op =
      ref.i31(
        op(
          i31.get_s(ref.cast(local.get(paramIdx, RefType.anyref), RefType.i31ref)),
        ),
      )
    `if`(
      condition = cond,
      ifTrue = i31Op,
      ifFalse = S(unreachable),
      resultTypes = Seq(Result(RefType.anyref)),
    )

  /** Creates a unary Int31 intrinsic with a single parameter and body built from `op`.
    */
  private def createUnaryInt31Func(
      name: Str,
      op: Expr => Expr,
  )(using Ctx, Raise, State): FuncIdx =
    val params = mkIntrinsicParams(Ls("arg"))
    val argName = params.head._2
    val body = unaryInt31Body(LocalIdx(argName), op)
    createIntrinsicFunc(name, params, body)
end WatBuilder

/** Compiles one program, with `linking` describing the files it imports. */
class WatBuilder(private val ctx: Ctx, linking: FileCompilation)(using TraceLogger, State) extends CodeBuilder:
  import Ctx.{SingletonInfo, wasmIntrinsicArities, wasmIntrinsicNameSet}
  import FunctionCtx.funcCtx
  import Instructions.{block as blockInstr, loop as loopInstr, *}
  import WatBuilder.ExternIntrinsics

  type Context = Ctx

  given Ctx = ctx
  given elabCtx: Elaborator.Ctx = ctx.elabCtx

  // These tables carry per-file linkage metadata without adding it to cached MIR symbols.
  private val fileSingletonActions = LinkedHashMap.empty[ModuleOrObjectSymbol, Expr]
  private val namespaces = LinkedHashMap.empty[ModuleOrObjectSymbol, AbiNamespace]
  private val localNamespaces = scala.collection.mutable.Set.empty[ModuleOrObjectSymbol]
  private val staticBindings = LinkedHashMap.empty[TermSymbol, ScopedSymbol]

  def fileModule(p: Program, exprt: Opt[BlockMemberSymbol], wd: io.Path)(using Raise): CompiledWasmFile =
    val preserved: Set[ScopedSymbol] = p.main match
      case Scoped(syms, _) => syms.toSet
      case _ => Set.empty
    checkImports(p, wd)
    program(p, exprt, preserved)

  def worksheetModule(p: Program, wd: io.Path, preserved: Set[ScopedSymbol])(using Raise): CompiledWasmFile =
    checkImports(p, wd)
    program(p, N, preserved)

  /** Compiles the module that defines the bindings every other module imports from [[ExternIntrinsics.SystemModule]]:
    * the intrinsics and the exception tag, which importers import by name, and the `Unit` object. The entry function
    * initializes Unit before the loader instantiates any importer. Unit's source symbol identifies its Wasm layout
    * and storage in backend tables; its MIR definition continues to belong to the cached JavaScript runtime.
    */
  def runtimeModule()(using Raise): CompiledWasmFile =
    wasmIntrinsicNameSet.toVector.sorted.foreach(name => WatBuilder.createIntrinsic(name))
    exnTag((ty, sym) => ctx.addTag(TagInfo(ty, sym)))
    initializeObjectTypes()

    val unit = State.unitSymbol
    val binding = unit.bms.getOrElse(lastWords("Runtime Unit has no source binding"))
    val params = LoweredParamList.plain(Nil)(N)
    ctx.registerVirtualTable(unit, Ctx.VirtualTable(Nil, Map.empty))
    predeclareClassType(unit, N, Iterator.empty)
    predeclareClassTypeInfoType(unit, binding.nme, N)
    predeclareClassInit(unit, binding.nme, params)
    predeclareClassConstructor(unit, binding.nme, params)
    predeclareClassTypeInfoGlobal(unit, binding, N)
    registerSingletonInit(unit, binding.nme, ctx.getType_!(unit))

    // Unit has no Wasm fields to initialize. Building MIR here would republish class metadata on the shared symbol.
    val unitType = RefType(ctx.getType_!(unit), nullable = false)
    val (initBody, initFrame) = genFuncBody(params :: Nil, thisSym = S(unit), resultType = S(unitType), loc = N,
      paramTypes = S(Vector(unitType))):
      Vector(`return`(S(local.get(funcCtx.lookupLocal_!(unit, N), unitType))))
    definePredeclaredFunction(initFuncSym(unit), initBody, initFrame)
    defineClassConstructor(unit, params, N)

    val (entryBody, entryFrame) = genFuncBody(Nil, thisSym = N, resultType = S(RefType.anyref), loc = N):
      Vector(fileSingletonActions(unit), singletonGlobalGet(ctx.getSingletonInfo(unit).get))
    val entry = entryFunction(entryBody, entryFrame, RefType.anyref)
    ctx.addFunc(entry)
    compiledModule(entry.exportName, N)

  /** The module namespace that `path` denotes, if any. */
  private def namespace(path: Path): Opt[AbiNamespace] = path match
    case Value.MemberRef(disamb = mod: ModuleOrObjectSymbol) => namespaces.get(mod)
    case Value.This(mod: ModuleOrObjectSymbol) => namespaces.get(mod)
    case _ => N

  /** The global or function that holds the static module member selected by `sel`, if any. */
  private def staticSelection(sel: Select): Opt[ScopedSymbol] =
    namespace(sel.qual).flatMap(ns => sel.symbol.flatMap(staticMember(ns, _)))

  /** The global or function that holds `member` of the module namespace `ns`, if it is one. */
  private def staticMember(ns: AbiNamespace, member: Symbol): Opt[ScopedSymbol] = member match
    case member: TermSymbol => ns.storage.get(member).orElse(ns.methods.get(member))
    case _ => N

  private def registerNamespace(ns: AbiNamespace): Unit =
    namespaces(ns.module) = ns
    staticBindings ++= ns.storage

  /** Whether `body` belongs to a standalone module, which the backend compiles as a static namespace.
    *
    * Lowering represents a standalone module by a class without members whose companion holds the module's body, the
    * same shape as a class with a companion module. Only the module's definition records whether a source class is its
    * companion; when none is, Lowering creates the class (see `Lowering`). The backend does not support classes with
    * companion modules, and compiling one as a namespace would drop the class.
    */
  private def isStandaloneModule(body: ClsLikeBody): Bool =
    body.isym.defn.exists(mod => (mod.kind is syntax.Mod) && mod.classCompanion.isEmpty)

  private def predeclareFileMembers(b: Block)(using Ctx, Raise): Unit =
    new BlockTraverserShallow:
      override def applyDefn(d: Defn): Unit = d match
        case cls @ ClsLikeDefn(companion = S(body)) if isStandaloneModule(body) =>
          // The host facade follows source visibility; internal calls still need every method in the Wasm ABI.
          val members = body.publicFields.iterator.map((bms, ts) => ts.nme -> bms) ++
            body.methods.iterator.filterNot(_.dSym.isPrivate).map(m => m.sym.nme -> m.sym)
          // Private fields have no scoped binding in typed IR. Allocate backend-owned slots
          // carrying their erased types; public fields retain their originating block members.
          val storage = body.publicFields.map((bms, ts) => ts -> (bms: ScopedSymbol)) ++
            body.privateFields.map(ts => ts -> (TempSymbol(N, ts.erasedType, ts.nme): ScopedSymbol))
          val methods = body.methods.map(m => m.dSym -> m.sym)
          registerNamespace(AbiNamespace(cls.sym, body.isym, members.toMap, storage.toMap, methods.toMap))
          localNamespaces += body.isym
          applyBlock(body.ctor)
        case _ => ()
    .applyBlock(b)

  private def fileClasses(using Ctx, Raise): Vector[AbiClass] =
    localClassSymbols.iterator.map: sym =>
      val singleton = ctx.getSingletonInfo(sym).map: info =>
        (GlobalIdx(SymIdx(info.globalName)), info.globalTy)
      AbiClass(sym, typeInfoTypeIdxs(sym)(), typeInfoGlobals(sym)(), initFuncSym(sym),
        ctx.getVirtualTable(sym).getOrElse(Ctx.VirtualTable(Nil, Map.empty)), singleton)
    .toVector

  /** Synthetic base struct symbol for shared runtime type information objects. */
  private val typeInfoBaseSym: BlockMemberSymbol = BlockMemberSymbol("TypeInfoBase", Nil)

  /** Synthetic base struct symbol for all heap-allocated class instances. */
  private val baseObjectSym: BlockMemberSymbol = BlockMemberSymbol("Object", Nil)

  /** Synthetic field symbol for the object-header pointer to a class's shared RTTI object. */
  private val typeInfoFieldSym: TermSymbol = TermSymbol(syntax.MutVal, owner = N, Ident("$typeinfo"), erasure = N)

  /** Synthetic field symbol for the runtime class tag stored in RTTI. */
  private val tagFieldSym: TermSymbol =
    TermSymbol(syntax.MutVal, owner = N, Ident("$tag"), erasure = S(ErasedType.Int))

  /** Synthetic field symbol for the direct-parent RTTI reference used by runtime subtype checks. */
  private val parentFieldSym: TermSymbol = TermSymbol(syntax.MutVal, owner = N, Ident("$parent"), erasure = N)

  private case class StringLitInfo(offset: Int, byteLen: Int, watBytes: Str)
  private val stringLits: LinkedHashMap[Str, StringLitInfo] = LinkedHashMap.empty
  private val initFuncSyms: LinkedHashMap[BaseTypeSymbol, BlockMemberSymbol] = LinkedHashMap.empty
  // Import metadata is available before lowering, but resolving an RTTI index emits
  // its import/type closure. Capturing this file's ABI must visit only local classes.
  private val typeInfoTypeIdxs: LinkedHashMap[BaseTypeSymbol, () => TypeIdx] = LinkedHashMap.empty
  private val typeInfoGlobals: LinkedHashMap[BaseTypeSymbol, () => GlobalIdx] = LinkedHashMap.empty
  private val localClassSymbols = scala.collection.mutable.LinkedHashSet.empty[BaseTypeSymbol]
  private var nextStringDataOffset: Int = 0

  /** Returns the Wasm type index of the synthetic base object header struct. */
  private def baseObjectTypeIdx: TypeIdx =
    ctx.getType_!(baseObjectSym)

  /** Returns the Wasm type index of the synthetic base RTTI struct. */
  private def typeInfoBaseTypeIdx: TypeIdx =
    ctx.getType_!(typeInfoBaseSym)

  /** Resolves the field index for a field inside a previously registered struct type. */
  private def structFieldIdx(typeSym: TypeKey, fieldSym: TermSymbol)(using Ctx): FieldIdx =
    fieldSelect(typeSym, fieldSym)

  /** Loads this module's RTTI singleton for `sym`, if one has been registered. */
  private def getClassTypeInfoGlobal(sym: BaseTypeSymbol)(using Raise): Opt[Expr] =
    typeInfoGlobals.get(sym).map: load =>
      val globalIdx = load()
      val globalTy = ctx.getGlobalType_!(globalIdx).globalType.valType
      global.get(globalIdx, globalTy)

  /** Reads the RTTI pointer stored in an object's common header. */
  private def readObjectTypeInfo(objRef: Expr): Expr =
    struct.get(
      structFieldIdx(baseObjectSym, typeInfoFieldSym),
      ref.cast(objRef, baseObjectRefType(nullable = false)),
      RefType(typeInfoBaseTypeIdx, nullable = false),
    )

  /** Follows one direct-parent RTTI reference from a shared class `typeinfo` object. */
  private def readTypeInfoParent(typeInfoRef: Expr): Expr =
    struct.get(
      structFieldIdx(typeInfoBaseSym, parentFieldSym),
      ref.cast(typeInfoRef, RefType(typeInfoBaseTypeIdx, nullable = false)),
      RefType(typeInfoBaseTypeIdx, nullable = true),
    )

  /** Builds the reference type for the synthetic base object header struct. */
  private def baseObjectRefType(nullable: Bool): RefType =
    RefType(baseObjectTypeIdx, nullable = nullable)

  /** Casts an expression to `target` type, unless its result type is already a subtype of `target`.
    *
    * Emits an error if the two types have incompatible type hierarchies.
    */
  private def castConserve(expr: Expr, target: ValType, loc: Opt[Loc])(using Raise): Expr =
    require(expr.resultTypes.size == 1, "expected single-result expression for cast")
    expr.resultType -> target match
      case (S(ty), _) if ty.isSubtypeOf(target) => expr
      case (S(ty: RefType), target: RefType) if ty.heapType.topType === target.heapType.topType =>
        ref.cast(expr, target)
      case (ty, _) =>
        errExpr(
          Ls(msg"Cannot cast a Wasm value of type `${
              ty.fold("(none)")(_.toWat.mkString())
            }` to `${target.toWat.mkString()}` in a different type hierarchy" -> loc),
          extraInfo = S(expr.toWat.mkString()),
        )

  private def isBottom(r: codegen.Result): Bool =
    ctx.elabCtx.givenIn(r.erasedType_!.canonicalize == ErasedType.Nothing)

  /** Compiles `r` and narrows it to `target`, the declared type of the slot it flows into. A failed cast is reported at
    * `r`'s location, or at `loc` (such as the enclosing call) when lowering left `r` without one, as it does for
    * temporaries.
    */
  private def castToValType(
    r: codegen.Result,
    target: ValType,
    loc: Opt[Loc],
  )(using FunctionCtx, Raise): Expr =
    // Nothing supplies no representation to convert. Evaluate non-literal operands for their effects,
    // then materialize an unspecified value in the destination slot, including for DPE placeholders.
    if isBottom(r) then
      val unspecified = target.zeroValue.getOrElse(lastWords("Undefined requires a defaultable value type"))
      if r.isUndefined then unspecified
      else Seq(asStatement(result(r)), unspecified).mergeAsBlock_!
    else castConserve(result(r), target, r.toLoc.orElse(loc))

  /** Compile arguments in their physical parameter representations, including undefined placeholders, and supply null
    * for omitted optional arguments. A method's already-evaluated receiver occupies the first parameter. Source arity
    * checking happens before parameter flags are erased; a missing slot must still have a representation that can carry
    * null.
    */
  private def adaptCallArgs(
    args: Seq[Arg],
    funcTypeInfo: TypeInfo,
    receiver: Opt[Expr],
    loc: Opt[Loc],
  )(using FunctionCtx, Raise): Seq[Expr] =
    val declParams = funcTypeInfo.asFunctionType_!.sigType.params
    val prefix = receiver.map(castConserve(_, declParams.head.valtype, loc)).toSeq
    val suppliedParams = declParams.drop(prefix.size)
    if args.size > suppliedParams.size then raise:
      ErrorReport(
        msg"More arguments were supplied than the WebAssembly call supports." -> loc :: Nil,
        source = Diagnostic.Source.Compilation,
      )
    prefix ++ suppliedParams.zipWithIndex.map: (p, index) =>
      args.lift(index) match
        case S(arg) => argument(arg, S(p.valtype), loc)
        case N => p.valtype match
          case rt: RefType if rt.nullable => ref.`null`(rt.heapType)
          case _ => errExpr(Ls(msg"Missing argument cannot be represented as null by the WebAssembly backend." -> loc))

  /** Returns the default Wasm value for one struct field when eagerly constructing an object instance. */
  private def defaultStructFieldValue(field: Field)(using Raise): Expr = field.ty.zeroValue.getOrElse:
    field.ty match
      case _: RefType =>
        lastWords(s"non-null ref field `${field.id}` requires an explicit initializer")
      case other =>
        lastWords(s"unsupported default field type `${other.toWat.mkString()}` for eager object construction")

  /** Returns `1` when `scrutTypeInfo` is equal to or descends from `targetTypeInfo`, else `0`. */
  private def isSubtypeByTypeInfo(
      scrutTypeInfo: Expr,
      targetTypeInfo: Expr,
  )(using FunctionCtx, Raise): Expr =
    val currentTmp = mkTempLocal("currentTypeInfo", erasedType = N)
    val targetTmp = mkTempLocal("targetTypeInfo", erasedType = N)
    val resultTmp = mkTempLocal("typeInfoMatch", erasedType = S(ErasedType.Bool))
    funcCtx.withLabel(LabelSymbol(N, "typeInfo"), hasContinueLabel = true):
      case LabelTarget(breakLabel, S(continueLabel)) =>
        Seq(
          local.set(currentTmp, scrutTypeInfo),
          local.set(targetTmp, targetTypeInfo),
          local.set(resultTmp, ref.i31(i32.const(0))),
          blockInstr(
            label = S(breakLabel),
            children = Seq(
              loopInstr(
                label = S(continueLabel),
                children = Seq(
                  `if`(
                    condition = ref.is_null(getLocalAnyref(currentTmp)),
                    ifTrue = br(breakLabel),
                    ifFalse = N,
                    resultTypes = Seq.empty,
                  ),
                  `if`(
                    condition = ref.eq(
                      ref.cast(getLocalAnyref(currentTmp), RefType(HeapType.Eq, nullable = true)),
                      ref.cast(getLocalAnyref(targetTmp), RefType(HeapType.Eq, nullable = true)),
                    ),
                    ifTrue = Seq(
                      local.set(resultTmp, ref.i31(i32.const(1))),
                      br(breakLabel),
                    ).mergeAsBlock_!,
                    ifFalse = N,
                    resultTypes = Seq.empty,
                  ),
                  local.set(currentTmp, readTypeInfoParent(getLocalAnyref(currentTmp))),
                  br(continueLabel),
                ),
                resultTypes = Seq.empty,
              ),
            ),
            resultTypes = Seq.empty,
          ),
          i31.get(ref.cast(getLocalAnyref(resultTmp), RefType.i31ref), signed = true),
        ).mergeAsBlock_!
      case LabelTarget(_, N) =>
        lastWords("unreachable: loop-based RTTI traversal expects a continue label")
  end isSubtypeByTypeInfo

  /** Static module members have no enclosing instance to capture, so their classes
    * use the same representation as top-level classes. Instance-owned classes do not. */
  private def hasStaticOwner(defn: ClsLikeDefn): Bool = defn.owner.forall:
    case mod: ModuleOrObjectSymbol => namespaces.contains(mod)
    case _ => false

  /** True if this statically owned class can be declared as a Wasm struct type. */
  private def isSupportedTopLevelClass(defn: ClsLikeDefn): Bool =
    hasStaticOwner(defn)
      && ((defn.k is syntax.Cls) || (defn.k is syntax.Obj))
      && (!(defn.k is syntax.Obj) || defn.parentPath.isEmpty)
      && (!(defn.k is syntax.Obj) || defn.methods.isEmpty)
      && defn.companion.isEmpty

  /** Returns singleton metadata when `sym` denotes a registered singleton object. */
  private def singletonInfoFor(sym: InnerSymbol): Opt[SingletonInfo] =
    ctx.getSingletonInfo(sym)

  /** Loads the singleton object reference from its backing mutable global. */
  private def singletonGlobalGet(info: SingletonInfo): Expr =
    global.get(GlobalIdx(SymIdx(info.globalName)), info.globalTy)

  /** The object symbol that identifies the singleton defined by `clsLikeDefn`. */
  private def singletonSym(clsLikeDefn: ClsLikeDefn): ModuleOrObjectSymbol = clsLikeDefn.isym match
    case obj: ModuleOrObjectSymbol => obj
    case other => lastWords(s"Singleton `${clsLikeDefn.sym.nme}` is not defined by an object symbol: $other")

  /** Registers eager singleton runtime state by creating its global and entry-function initialization action. */
  private def registerSingletonInit(
      obj: ModuleOrObjectSymbol,
      name: Str,
      typeref: TypeIdx,
  )(using Raise): Unit =
    if ctx.containsSingleton(obj) then return
    
    val globalSym = BlockMemberSymbol(s"$name$$inst", Nil, nameIsMeaningful = false)
    val globalTy = RefType(typeref, nullable = true)

    val globalInfo = GlobalInfo(
      globalType = GlobalType(globalTy, mutable = true),
      init = ref.`null`(typeref),
      sym = globalSym,
    )
    val globalIdx = ctx.addGlobal(globalInfo)

    val info = SingletonInfo(globalInfo.id.id, globalTy)
    ctx.registerSingleton(obj, info)

    val ctorCall = call(
      funcidx = ctx.getFunc_!(obj),
      operands = Seq.empty,
      returnTypes = Seq(Result(globalTy)),
    )
    fileSingletonActions(obj) = global.set(globalIdx, ctorCall)
  end registerSingletonInit

  /** Whether `defn` is a top-level function that may be predeclared.
    *
    * Mirrors what the [[FunDefn]] arm of [[returningTerm]] accepts; a function it refuses must not be predeclared,
    * since its placeholder would then never be overwritten.
    */
  private def isPredeclarableTopLevelFun(defn: FunDefn): Bool =
    defn.owner.isEmpty
      && defn.sym.nameIsMeaningful
      && defn.params.nonEmpty

  /** Collects all top-level class and function definitions in `block`. */
  private def collectTopLevelDefns(block: Block): (List[ClsLikeDefn], List[FunDefn]) =
    val clsAcc = ArrayBuf.empty[ClsLikeDefn]
    val funAcc = ArrayBuf.empty[FunDefn]
    new BlockTraverserShallow:
      applyBlock(block)
      override def applyBlock(b: Block): Unit = b match
        case Match(_, _, _, rst) => applySubBlock(rst)
        case Label(_, _, _, rst) => applySubBlock(rst)
        case TryBlock(_, _, rst) => applySubBlock(rst)
        case _ => super.applyBlock(b)
      override def applyDefn(defn: Defn): Unit = defn match
        case ClsLikeDefn(companion = S(body)) if localNamespaces(body.isym) =>
          funAcc ++= body.methods
          applyBlock(body.ctor)
        case clsLikeDefn: ClsLikeDefn =>
          clsLikeDefn.optionIf(isSupportedTopLevelClass).foreach(clsAcc += _)
        case funDefn: FunDefn =>
          funDefn.optionIf(isPredeclarableTopLevelFun).foreach(funAcc += _)
        case _ => ()
    (clsAcc.toList, funAcc.toList)

  /** Resolves the parent class of a top-level class definition, if present. */
  private def resolveParentSym(defn: ClsLikeDefn)(using Raise): Opt[ClassSymbol] =
    def unsupportedParent(): Opt[ClassSymbol] =
      raise(ErrorReport(
        msg"Wasm inheritance ordering only supports direct resolved parent class references." ->
          defn.parentPath.flatMap(_.toLoc) :: Nil,
        extraInfo = S(defn.showAsTree),
        source = Diagnostic.Source.Compilation,
      ))
      N

    defn.parentPath match
      case N => N
      // Lowering keeps a parent path only when it denotes a class (see `Lowering.withClassParent`).
      case S(Value.MemberRef(disamb = cls: ClassSymbol)) => S(cls)
      case S(sel: Select) => sel.symbol match
        case S(cls: ClassSymbol) => S(cls)
        case _ => unsupportedParent()
      case S(_) =>
        unsupportedParent()

  /** Orders top-level classes using a Kahn topological sort. */
  private def sortTopLevelClasses(defns: List[ClsLikeDefn])(using Ctx, Raise): List[ClsLikeDefn] =
    val defnsBySym = defns.iterator.map(defn => classSym(defn) -> defn).toMap
    val childrenBySym = LinkedHashMap.empty[BaseTypeSymbol, ArrayBuf[BaseTypeSymbol]]
    val indegrees = LinkedHashMap.empty[BaseTypeSymbol, Int]

    defns.foreach: defn =>
      childrenBySym(classSym(defn)) = ArrayBuf.empty
      indegrees(classSym(defn)) = 0

    defns.foreach: defn =>
      if defn.parentPath.nonEmpty then
        val parentSym = resolveParentSym(defn).getOrElse(lastWords("unreachable"))
        if defnsBySym.contains(parentSym) then
          childrenBySym(parentSym) += classSym(defn)
          indegrees(classSym(defn)) += 1
        else if ctx.getType(parentSym).isEmpty then
          raise(ErrorReport(
            msg"Wasm inheritance ordering requires parent classes to be supported top-level classes." ->
              defn.parentPath.flatMap(_.toLoc) :: Nil,
            extraInfo = S(s"${defn.sym.nme} extends ${parentSym.nme}"),
            source = Diagnostic.Source.Compilation,
          ))

    val zeroIndegree = Queue.from:
      defns.iterator.map(classSym).filter(indegrees(_) == 0)

    val ordered = ArrayBuf.empty[ClsLikeDefn]
    while zeroIndegree.nonEmpty do
      val sym = zeroIndegree.dequeue()
      ordered += defnsBySym(sym)
      childrenBySym(sym).foreach: childSym =>
        indegrees(childSym) -= 1
        if indegrees(childSym) == 0 then
          zeroIndegree.enqueue(childSym)

    if ordered.size != defns.size then
      raise(ErrorReport(
        msg"Inheritance cycles are not supported." ->
          defns.flatMap(_.sym.toLoc).headOption :: Nil,
        extraInfo = S(
          defns.iterator
            .filter(defn => indegrees(classSym(defn)) > 0)
            .map(_.sym.nme)
            .mkString(", "),
        ),
        source = Diagnostic.Source.Compilation,
      ))

    ordered.toList
  end sortTopLevelClasses

  /** The class or object symbol that keys the Wasm type, RTTI, initializer, and virtual table of `defn`. */
  private def classSym(defn: ClsLikeDefn): BaseTypeSymbol = defn.isym match
    case cls: BaseTypeSymbol => cls
    case other => lastWords(s"Wasm class `${defn.sym.nme}` is not defined by a class or object symbol: $other")

  /** Returns the elaborated semantic class definition for this lowered class. */
  private def semanticClassDef(defn: ClsLikeDefn)(using Raise): hkmc2.semantics.ClassLikeDef =
    defn.isym.defn match
      case S(clsDef: hkmc2.semantics.ClassLikeDef) => clsDef
      case _ =>
        lastWords(s"Expected definition of class `${defn.sym}` to be present")

  /** Returns the elaborated source methods for this class. */
  private def semanticMethodDefs(defn: ClsLikeDefn)(using Raise): List[TermDefinition] =
    semanticClassDef(defn).body.methods

  /** Resolves the exact overridden parent method symbol for `methodDef`, if any. */
  private def overriddenParentMethodSym(
      defn: ClsLikeDefn,
      methodDef: TermDefinition,
  )(using Raise): Opt[TermSymbol] =
    def lookup(parent: ClassLikeSymbol, seen: Set[ClassLikeSymbol]): Opt[TermSymbol] =
      if seen(parent) then N
      else
        parent.defn.flatMap(parentDefn => parentDefn.body.members.get(methodDef.sym.nme).map(parentDefn -> _)) match
          // The nearest ancestor declaring the name determines the overridden member, which may not be a method.
          case S((parentDefn, member)) => parentDefn.body.methods.find(_.sym is member).map(_.tsym)
          case N =>
            parent.irClassHeader.flatMap(_.parent.knownSymbol).flatMap:
              case cls: BaseTypeSymbol => lookup(cls, seen + parent)
              case _: TypeAliasSymbol => N
    resolveParentSym(defn).flatMap(lookup(_, Set.empty))

  /** True when a method introduces a new virtual slot at its declaring class if not already inherited. */
  private def declaresVirtualSlot(methodDef: TermDefinition): Bool =
    methodDef.body.isEmpty || methodDef.annotations.exists:
      case Annot.Modifier(syntax.Keyword.`virtual` | syntax.Keyword.`open`) => true
      case _ => false

  /** The declared Wasm parameter types of `methodDef`, excluding `this`. */
  private def declaredParamTypes(methodDef: TermDefinition): Seq[ValType] =
    methodDef.params.headOption.fold(Nil)(_.params).map(_.sym.paramType)

  /** Whether a method declaring `actual` may occupy a virtual slot declared as `expected`.
    *
    * All overrides of a method share the slot's Wasm function type. Reference types are bridged by casts at the call
    * site, but primitives have no conversion, so they must match exactly.
    */
  private def conformsToSlotType(actual: ValType, expected: ValType): Bool = (actual, expected) match
    case (_: RefType, _: RefType) => true
    case _ => actual === expected

  /** Reports an overriding method whose primitive parameter or result types differ from the slot it occupies. */
  private def checkOverrideSignature(
      methodDef: TermDefinition,
      slotInfo: Ctx.VirtualMethodInfo,
  )(using Raise): Unit =
    def report(what: Str, actual: ValType, expected: ValType): Unit =
      raise(ErrorReport(
        Ls(msg"Overriding method `${methodDef.sym.nme}` declares $what as `${
            actual.toWat.mkString()
          }`, but the method it overrides declares `${expected.toWat.mkString()}`" -> methodDef.sym.toLoc),
        source = Diagnostic.Source.Compilation,
      ))
    if declaredParamTypes(methodDef).size != slotInfo.paramTypes.size then raise:
      ErrorReport(
        msg"Overriding method '${methodDef.sym.nme}' must preserve the number of parameters" ->
          methodDef.sym.toLoc :: Nil,
        source = Diagnostic.Source.Compilation,
      )
    declaredParamTypes(methodDef).zip(slotInfo.paramTypes).zipWithIndex.foreach:
      case ((actual, expected), idx) =>
        if !conformsToSlotType(actual, expected) then report(s"parameter ${idx + 1}", actual, expected)
    val actualResult = declaredResultType(methodDef.tsym)
    // A bottom result places no constraint on the inherited slot; its body materializes undefined in that slot.
    if !hasBottomResult(methodDef.tsym) && !conformsToSlotType(actualResult, slotInfo.resultType) then
      report("result", actualResult, slotInfo.resultType)
  end checkOverrideSignature

  /** Computes one derived virtual-table layout for one top-level class. */
  private def predeclareClassVirtualTable(defn: ClsLikeDefn)(using Raise): Unit =
    val parentVirtualTable = resolveParentSym(defn).flatMap(ctx.getVirtualTable)
      .getOrElse(Ctx.VirtualTable(Nil, Map.empty))
    val slots = ArrayBuf.from(parentVirtualTable.slots)
    val slotOf = LinkedHashMap.from(parentVirtualTable.slotOf)

    // FIXME: LP: why do we need to access elaborated Term methods, here?! We should just be able to look at the IR definitions, and if that's not enough, we should put the required info there...
    semanticMethodDefs(defn).foreach: methodDef =>
      val slotIdx = overriddenParentMethodSym(defn, methodDef).flatMap(parentVirtualTable.slotOf.get)
      slotIdx match
        case S(slot) =>
          checkOverrideSignature(methodDef, slots(slot))
          slots(slot) = slots(slot).copy(sym = methodDef.tsym)
          slotOf(methodDef.tsym) = slot
        case N if declaresVirtualSlot(methodDef) =>
          val slot = slots.size
          slots += Ctx.VirtualMethodInfo(
            sym = methodDef.tsym,
            owner = classSym(defn),
            paramTypes = declaredParamTypes(methodDef),
            resultType = declaredResultType(methodDef.tsym),
          )
          slotOf(methodDef.tsym) = slot
        case N => ()

    ctx.registerVirtualTable(
      classSym(defn),
      Ctx.VirtualTable(
        slots = slots.toList,
        slotOf = slotOf.toMap,
      ),
    )
  end predeclareClassVirtualTable

  /** Declares an instance layout from its source identity and fields, without constructing a MIR definition. */
  private def predeclareClassType(
      sym: BaseTypeSymbol,
      parent: Opt[ClassSymbol],
      fields: Iterator[TermSymbol],
  )(using Raise): Unit =
    val parentTypeIdx = parent.fold(baseObjectTypeIdx)(ctx.getType_!(_))
    val inheritedFields = ctx.getTypeInfo_!(parentTypeIdx).compType match
      case struct: StructType => struct.fields
      case other => lastWords(s"Parent type must be a struct, found ${other.toWat.mkString()}")

    val classFields = ctx.elabCtx.givenIn:
      fields.flatMap: f =>
        // Reference fields need to be nullable so that `struct.new_default` has a valid value to write
        val fieldType: ValType = f.erasedType.flatMap(_.wasmType) match
          case S(ty: RefType) => ty.copy(nullable = true)
          case S(ty) => ty
          case N => RefType.anyref
        inheritedFields.collectFirst:
          case (sym: TermSymbol, field) if !sym.isPrivate && !f.isPrivate && sym.nme == f.nme => field
        match
          case S(field) =>
            // Overrides denote the same public property, including abstract fields. Reuse its
            // storage so a selection through the base symbol sees the overriding initializer.
            if !conformsToSlotType(fieldType, field.ty) then raise:
              ErrorReport(
                msg"Overriding field '${f.nme}' must preserve its inherited storage type" -> f.toLoc :: Nil,
                source = Diagnostic.Source.Compilation,
              )
            Nil
          case N => (f -> Field(fieldType, mutable = true, id = f.nme)) :: Nil

    val allFields = inheritedFields ++ classFields
    val runtimeTag = ctx.getFreshObjectTag()

    ctx.addType(TypeInfo(
      sym = sym,
      compType = StructType(fields = allFields, parents = Seq(parentTypeIdx)),
      objectTag = S(runtimeTag),
    ))
  end predeclareClassType
  
  /** Declares the shared Wasm function type used by a class-associated function placeholder.
    *
    * @param thisType
    *   When set, overrides the type of param index 0 (`this`) instead of `anyref`.
    */
  private def declareClassFuncType(
      className: Str,
      suffix: Str,
      params: Seq[WasmSlotSymbol -> SymIdx],
      results: Seq[Result],
      thisType: Opt[ValType],
  )(using Raise): TypeIdx =
    ctx.addType(TypeInfo(
      sym = TempSymbol(N, initErasedType = N, className),
      FunctionType(
        params = params.zipWithIndex.map: (p, idx) =>
          WasmParam(p._2, resolveParamType(p._1, idx, thisType.map(Seq(_)))),
        results = results,
      ),
      objectTag = N,
      wrapId = N -> S(suffix),
    ))

  /** Returns the declared Wasm result type of the function or method `sym`, defaulting to `anyref` when the return type
    * is not annotated.
    */
  private def declaredResultType(sym: TermSymbol)(using Raise): ValType =
    sym.declaredResultType.flatMap(_.wasmType).getOrElse(RefType.anyref)

  /** Bottom has no physical result type of its own; an override can use any inherited result slot. */
  private def hasBottomResult(sym: TermSymbol): Bool =
    ctx.elabCtx.givenIn(sym.declaredResultType.exists(_.canonicalize == ErasedType.Nothing))

  /** The physical result slot of the function or method `sym`, whose predeclared signature has the results `declared`.
    * Each `return` is checked against this slot, and falling off the body materializes `undefined` in it.
    */
  private def singleResultType(sym: ExternSymbol, declared: Seq[Result])(using Raise): Opt[ValType] =
    softAssert(declared.sizeIs == 1, s"Wasm function `${sym.nme}` with multiple declared results not supported yet")
    declared.headOption.map(_.valtype)

  /** Returns the shared erased Wasm function signature for a virtual method slot introduced by `baseSym`, with the
    * given non-`this` param types, including a concretely-typed `this`.
    */
  private def virtualMethodSignature(
      baseSym: BaseTypeSymbol,
      paramTypes: Seq[ValType],
      resultType: ValType,
  )(using Raise): FunctionType =
    val thisTy = RefType(ctx.getType_!(baseSym), nullable = false)
    FunctionType(
      params = WasmParam(SymIdx("this"), thisTy) +: paramTypes.zipWithIndex.map: (ty, idx) =>
        WasmParam(SymIdx(s"arg${idx + 1}"), ty),
      results = Seq(Result(resultType)),
    )

  /** Declares (and caches) the shared Wasm function type for a virtual method slot introduced by `baseSym` with the
    * given non-`this` param types and result type.
    */
  private def virtualMethodFuncType(
      baseSym: BaseTypeSymbol,
      paramTypes: Seq[ValType],
      resultType: ValType,
  )(using Raise): TypeIdx =
    ctx.getOrCreateWasmIntrinsicType(WasmIntrinsicType.VirtualMethod(baseSym, paramTypes.toList, resultType)):
      ctx.addType(TypeInfo(
        sym = TempSymbol(N, initErasedType = N, s"virtual${paramTypes.size + 1}"),
        compType = virtualMethodSignature(baseSym, paramTypes, resultType),
        objectTag = N,
      ))
  end virtualMethodFuncType

  /** Returns the symbol used to predeclare and later overwrite a class init function. */
  private def initFuncSym(sym: BaseTypeSymbol): BlockMemberSymbol =
    initFuncSyms.getOrElseUpdate(sym, BlockMemberSymbol("init", Nil, nameIsMeaningful = false))

  private def optionalParamIndices(params: Ls[semantics.Param], offset: Int): Set[Int] =
    params.zipWithIndex.collect { case (p, i) if p.flags.opt => i + offset }.toSet

  /** Registers a placeholder class-associated function so later lowering can overwrite it. */
  private def predeclareClassFunc(
      className: Str,
      suffix: Str,
      params: Seq[WasmSlotSymbol -> SymIdx],
      results: Seq[Result],
      sym: ExternSymbol,
      thisType: Opt[ValType],
      optionalParams: Set[Int],
  )(using Raise): Unit =
    val funcTy = declareClassFuncType(className, suffix, params, results, thisType)
    predeclareClassFuncWithType(className, params, results, sym, funcTy, optionalParams)

  /** Registers a class-associated function's signature and placeholder body before generating its implementation.
    * `params` supplies symbols and names in the order of `funcTy`'s physical slots; slot types come from `funcTy`, and
    * `resultTypes` must agree with it. This lets an overriding method retain its own parameter identities while using
    * its inherited virtual signature.
    */
  private def predeclareClassFuncWithType(
      className: Str,
      params: Seq[WasmSlotSymbol -> SymIdx],
      resultTypes: Seq[Result],
      sym: ExternSymbol,
      funcTy: TypeIdx,
      optionalParams: Set[Int],
  )(using Raise): Unit =
    val signature = ctx.getTypeInfo_!(funcTy).asFunctionType_!.sigType
    assert(params.size == signature.params.size, "Class function parameters must match its signature")
    ctx.addFunc(FuncInfo(
      sym,
      wrapId = sym match
        case _: BaseTypeSymbol => N -> S("ctor")
        case _ => S(className) -> N,
      typeUse = TypeUse(funcTy),
      params = params.lazyZip(signature.params).map:
        case ((symbol, id), param) =>
          symbol -> WasmParam(id, param.valtype),
      resultTypes = resultTypes,
      locals = Seq.empty,
      body = Vector(unreachable),
      optionalParams = optionalParams,
    ))
  end predeclareClassFuncWithType

  /** Returns the single flattened constructor parameter list. After ClassParamFlattener, all classes have paramsOpt = N
    * and exactly one auxParams entry.
    */
  private def classCtorParamList(defn: ClsLikeDefn): LoweredParamList =
    assert(
      defn.paramsOpt.isEmpty,
      s"WatBuilder: expected paramsOpt to be None after flattening for class ${defn.sym.nme}",
    )
    assert(
      defn.auxParams.sizeCompare(1) == 0,
      s"WatBuilder: expected exactly one auxParams entry after flattening for class ${defn.sym.nme}",
    )
    defn.auxParams.head

  /** Declares one top-level class init function. */
  private def predeclareClassInit(sym: BaseTypeSymbol, name: Str, pl: LoweredParamList)(using Raise): Unit =
    val typeIdx = ctx.getType_!(sym)
    val initParams = (sym -> SymIdx("this")) +:
      pl.params.map: p =>
        p.sym -> SymIdx(p.sym.nme)
    predeclareClassFunc(
      name,
      "init",
      initParams,
      Seq(Result(RefType(typeIdx, nullable = false))),
      initFuncSym(sym),
      thisType = S(RefType(typeIdx, nullable = false)),
      optionalParams = optionalParamIndices(pl.params, 1),
    )

  /** Declares a constructor under the class definition's identity. Its overloaded block member may also bind an
    * explicit function companion, which needs a separate Wasm function. */
  private def predeclareClassConstructor(sym: BaseTypeSymbol, name: Str, pl: LoweredParamList)(using Raise): Unit =
    val typeIdx = ctx.getType_!(sym)
    val ctorParams = pl.params.map: p =>
      p.sym -> SymIdx(p.sym.nme)
    predeclareClassFunc(
      name,
      "ctor",
      ctorParams,
      Seq(Result(RefType(typeIdx, nullable = false))),
      sym,
      thisType = N,
      optionalParams = optionalParamIndices(pl.params, 0),
    )
  end predeclareClassConstructor

  /** Registers a class's type identity into `Ctx`.
    *
    * This method is intended to be called before any layout or signature resolution for the class, since it is used to
    * allocate a placeholder type identity so that forward- and self-references to the class are resolved correctly.
    *
    * The layout registered here is a placeholder: [[predeclareClassType]] overwrites it with the real one under the
    * same name.
    */
  private def allocateClassTypeIdentity(defn: ClsLikeDefn)(using Raise): Unit =
    ctx.addType(TypeInfo(
      sym = classSym(defn),
      compType = StructType(fields = Nil),
      objectTag = N,
    ))
    ()

  /** Registers all Wasm pre-declarations needed for one top-level class, in dependency order. */
  private def predeclareClass(defn: ClsLikeDefn)(using Raise): Unit =
    val sym = classSym(defn)
    val parent = resolveParentSym(defn)
    val params = classCtorParamList(defn)
    predeclareClassVirtualTable(defn)
    // Note: `predeclareClassType` must run before `predeclareClassTypeInfoType`, since virtual slots in `typeinfo`
    // need to type `this` as the class's own type.
    predeclareClassType(sym, parent, defn.publicFields.iterator.map(_._2) ++ defn.privateFields.iterator)
    predeclareClassTypeInfoType(sym, defn.sym.nme, parent)
    predeclareClassInit(sym, defn.sym.nme, params)
    predeclareClassConstructor(sym, defn.sym.nme, params)
    predeclareClassMethods(defn)
    predeclareClassTypeInfoGlobal(sym, defn.sym, parent)
    if defn.k is syntax.Obj then
      registerSingletonInit(singletonSym(defn), defn.sym.nme, ctx.getType_!(sym))

  /** Registers a placeholder for a top-level function.
    *
    * `ps` is the function's first parameter list. It is the only one the [[FunDefn]] arm compiles into the Wasm
    * function itself - the rest become lambdas in its body - so it alone determines the declared type.
    *
    * The result type of the function is derived from the type annotations present on the function, falling back to
    * `anyref` when there is none.
    *
    * Note that only top-level functions that will be lowered by the [[FunDefn]] arm of [[returningTerm]] can be
    * pre-declared with this function - see [[isPredeclarableTopLevelFun]].
    */
  private def predeclareTopLevelFun(sym: BlockMemberSymbol, dSym: TermSymbol, ps: LoweredParamList)(using Raise): Unit =
    val params = ps.paramSyms.map(p => p -> SymIdx(p.nme))
    val resultTypes = Seq(Result(declaredResultType(dSym)))
    val funcTy = ctx.addType(TypeInfo(
      sym = TempSymbol(N, initErasedType = N, sym.nme),
      compType = FunctionType(
        params = params.map((p, idx) => WasmParam(idx, p.paramType)),
        results = resultTypes,
      ),
      objectTag = N,
    ))
    ctx.addFunc(FuncInfo(
      sym,
      typeUse = TypeUse(funcTy),
      params = params.map(_.resolvedParam),
      resultTypes = resultTypes,
      locals = Seq.empty,
      // Use `unreachable` as the placeholder body so that the module always remains well-formed.
      body = Seq(unreachable),
      optionalParams = optionalParamIndices(ps.params, 0),
    ))
  end predeclareTopLevelFun

  /** Collects the bindings in `preserved` that `b` defines at its top level. They live in mutable globals, which the
    * module exports, so that importing modules and later worksheet blocks can access them.
    *
    * TODO: replace this structural scan with an explicit "session-visible bindings" set from lowering once that
    * information is available directly in the IR.
    */
  private def collectPreservedBindings(
      b: Block,
      preserved: Set[ScopedSymbol],
  ): Set[ScopedSymbol] =
    def restOf(block: Block): Opt[Block] = block match
      case Define(_, rst) => S(rst)
      case Assign(_, _, rst) => S(rst)
      case AssignField(_, _, _, rst) => S(rst)
      case AssignDynField(_, _, _, _, rst) => S(rst)
      case Match(_, _, _, rst) => S(rst)
      case TryBlock(_, _, rst) => S(rst)
      case Label(_, _, _, rst) => S(rst)
      case _ => N

    def recur(block: Block): Set[ScopedSymbol] = block match
      case Scoped(_, body) =>
        recur(body)
      case Begin(sub, rst) =>
        recur(sub) ++ recur(rst)
      case Define(defn: ValDefn, rst) if preserved(defn.sym) =>
        recur(rst) + defn.sym
      case Define(_, rst) =>
        recur(rst)
      case Assign(sym: LocalVarSymbol, _, rst) if preserved(sym) =>
        recur(rst) + sym
      case _: BlockTail =>
        Set.empty
      case block =>
        restOf(block).fold(Set.empty)(recur)

    recur(b)
  end collectPreservedBindings

  /** Declares the mutable global that stores `sym`, a top-level binding or a module field. */
  private def registerGlobal(sym: ScopedSymbol)(using Raise): Unit =
    if ctx.containsGlobal(sym) then return
    // Reference globals need to be nullable so that they have a valid initializer
    val valType: ValType = sym.localType match
      case ty: RefType => ty.copy(nullable = true)
      case ty => ty
    val init = valType.zeroValue.getOrElse:
      lastWords(s"unsupported global type `${valType.toWat.mkString()}` for `${sym.nme}`")
    ctx.addGlobal(GlobalInfo(GlobalType(valType, mutable = true), init, sym))
  end registerGlobal

  /** Predeclares the per-class `typeinfo` struct type for one supported top-level class. */
  private def predeclareClassTypeInfoType(sym: BaseTypeSymbol, name: Str, parent: Opt[ClassSymbol])(using Raise): Unit =
    val parentTypeInfoIdx = parent.fold(typeInfoBaseTypeIdx)(typeInfoTypeIdxs(_)())

    val inheritedFields = ctx.getTypeInfo_!(parentTypeInfoIdx).compType match
      case struct: StructType => struct.fields
      case other =>
        lastWords(
          s"expected struct RTTI parent type for $sym, found ${other.toWat.mkString()}",
        )

    val parentVirtualMethodCount = parent.flatMap(ctx.getVirtualTable)
      .fold(0)(_.slots.size)
    val vt = ctx.getVirtualTable(sym)
    val vtSlots = vt.fold(Nil)(_.slots)
    val newSlotFields = vtSlots.zipWithIndex.drop(parentVirtualMethodCount).map: (slotInfo, slot) =>
      val fieldSym = TermSymbol(syntax.MutVal, owner = N, Ident(s"slot$slot"), erasure = N)
      fieldSym -> Field(
        RefType(virtualMethodFuncType(sym, slotInfo.paramTypes, slotInfo.resultType), nullable = true),
        mutable = true,
        id = s"slot$slot",
      )

    val typeInfoType = ctx.addType(TypeInfo(
      sym = TempSymbol(N, initErasedType = N, name),
      compType = StructType(fields = inheritedFields ++ newSlotFields, parents = Seq(parentTypeInfoIdx)),
      objectTag = N,
      wrapId = N -> S("typeinfo"),
    ))
    typeInfoTypeIdxs(sym) = () => typeInfoType
  end predeclareClassTypeInfoType

  /** Predeclares the shared runtime `typeinfo` global for one supported top-level class. */
  private def predeclareClassTypeInfoGlobal(
      sym: BaseTypeSymbol,
      binding: BlockMemberSymbol,
      parent: Opt[ClassSymbol],
  )(using Ctx, Raise): Unit =
    val typeInfoTypeIdx = typeInfoTypeIdxs(sym)()
    val tagValue = ctx.getTypeInfo_!(sym).objectTag.get
    val parentTypeInfo = parent.fold(ref.`null`(typeInfoBaseTypeIdx))(getClassTypeInfoGlobal(_).get)
    val vtSlots = ctx.getVirtualTable(sym).fold(Nil)(_.slots)
    val initFields = Seq[Expr](
      i32.const(tagValue),
      parentTypeInfo,
    ) ++ vtSlots.map: method =>
      // Abstract classes retain the slot and its calling convention without an implementation.
      // Erasure rejects constructing them; each concrete subclass must fill every such slot.
      ctx.getFunc(method.sym) match
        case S(func) => ref.func(func, RefType(ctx.getFuncTypeUse_!(method.sym).typeIdx, nullable = false))
        case N => ref.`null`(virtualMethodFuncType(method.owner, method.paramTypes, method.resultType))
    val globalInfo = GlobalInfo(
      globalType = GlobalType(RefType(typeInfoTypeIdx, nullable = false), mutable = false),
      init = struct.`new`(typeInfoTypeIdx, initFields),
      sym = binding,
      wrapId = N -> S("typeinfo"),
    )
    val globalIdx = ctx.addGlobal(globalInfo)
    typeInfoGlobals(sym) = () => globalIdx
    localClassSymbols += sym
  end predeclareClassTypeInfoGlobal

  /** Declares one top-level class method. */
  private def predeclareMethod(methodDefn: FunDefn, ownerCls: ClsLikeDefn)(using Raise): Unit =
    val methodParams = (ownerCls.isym -> SymIdx("this")) +:
      methodDefn.params.headOption.fold(Nil): ps =>
        ps.params.map: p =>
          p.sym -> SymIdx(p.sym.nme)
    ctx.getVirtualTable(classSym(ownerCls)).flatMap(vt =>
      vt.slotOf.get(methodDefn.dSym).map(slot => vt.slots(slot)),
    ) match
      case S(slotInfo) =>
        // Overrides adopt the slot's result type, not their own: all overrides share one Wasm function type.
        predeclareClassFuncWithType(
          ownerCls.sym.nme,
          methodParams,
          Seq(Result(slotInfo.resultType)),
          methodDefn.dSym,
          virtualMethodFuncType(slotInfo.owner, slotInfo.paramTypes, slotInfo.resultType),
          optionalParamIndices(methodDefn.params.flatMap(_.params), 1),
        )
      case N =>
        predeclareClassFunc(
          ownerCls.sym.nme,
          methodDefn.sym.nme,
          methodParams,
          Seq(Result(declaredResultType(methodDefn.dSym))),
          methodDefn.dSym,
          thisType = S(RefType(ctx.getType_!(classSym(ownerCls)), nullable = false)),
          optionalParams = optionalParamIndices(methodDefn.params.flatMap(_.params), 1),
        )
    end match
  end predeclareMethod

  /** Declares placeholders for all methods on one top-level class. */
  private def predeclareClassMethods(defn: ClsLikeDefn)(using Raise): Unit =
    defn.methods.foreach:
      case methodDefn @ FunDefn(params = Nil | _ :: Nil) =>
        predeclareMethod(methodDefn, defn)
      case FunDefn(sym = sym, params = _ :: _ :: _) =>
        raise(ErrorReport(
          msg"WatBuilder::predeclareClassMethods for ClsLikeDefn(...) with `multi-parameter-list method` not implemented yet" ->
            sym.toLoc :: Nil,
          source = Diagnostic.Source.Compilation,
        ))
      case _ => ()

  /** Gets (and caches) the exception tag used for MLX `throw`, creating it with `create` from its type and symbol. */
  private def exnTag(create: (TypeUse, TempSymbol) => TagIdx)(using Raise): TagIdx =
    val sym = TempSymbol(N, initErasedType = N, "mlx_exn")
    ctx.getOrCreateWasmIntrinsicTag("mlx_exn", {
      val ty = TypeUse(ctx.addType(TypeInfo(sym,
        FunctionType(params = Seq(WasmParam(SymIdx("ex"), RefType.anyref)), results = Seq.empty), N)))
      create(ty, sym)
    })

  /** The exception tag used for MLX `throw`, which the runtime module defines (see [[runtimeModule]]). */
  private def exnTagIdx(using Ctx, Raise): TagIdx =
    exnTag((ty, sym) => ctx.addTagImport(WasmImport("system", "mlx_exn", ExternType.Tag(ty, sym))))

  /** Returns (and caches) string literal data metadata, allocating data-segment space on first use.
    */
  private def internStringLiteral(value: Str): StringLitInfo =
    stringLits.getOrElseUpdate(
      value,
      if value.isEmpty then
        StringLitInfo(offset = 0, byteLen = 0, watBytes = "")
      else
        val sb = new StringBuilder(value.length * 6)
        value.foreach: ch =>
          val codeUnit = ch.toInt
          sb.append(f"\\${codeUnit & 0xff}%02x")
          sb.append(f"\\${(codeUnit >>> 8) & 0xff}%02x")
        val watBytes = sb.toString
        val offset = (nextStringDataOffset + 1) & ~1
        val byteLen = value.length * 2
        nextStringDataOffset = offset + byteLen
        StringLitInfo(offset = offset, byteLen = byteLen, watBytes = watBytes),
    )

  /** Ensures imports required for string materialization exist and returns the constructor function.
    */
  private def getOrLoadStrCtorFunction(using Raise): FuncIdx =
    val minBytes = nextStringDataOffset
    val pageSize = ExternIntrinsics.WasmPageSizeBytes
    val minPages =
      if minBytes <= 0 then 0
      else (minBytes + pageSize - 1) / pageSize
    ctx.ensureMemoryImport(
      ExternIntrinsics.SystemModule,
      ExternIntrinsics.SystemMemoryImportName,
      minPages,
    )
    ctx.getOrCreateFunctionImport(
      module = ExternIntrinsics.SystemModule,
      name = ExternIntrinsics.StringFromUtf16ImportName,
    ):
      val importTySym = TempSymbol(N, initErasedType = N, ExternIntrinsics.StringFromUtf16ImportName)
      val importTy = ctx.addType(TypeInfo(
        sym = importTySym,
        compType = FunctionType(
          params = Seq(WasmParam(SymIdx("glob_offset"), RefType.anyref), WasmParam(SymIdx("len"), RefType.anyref)),
          results = Seq(Result(RefType.anyref)),
        ),
        objectTag = N,
      ))
      WasmImport(
        module = ExternIntrinsics.SystemModule,
        name = ExternIntrinsics.StringFromUtf16ImportName,
        externType = ExternType.Func(
          typeUse = TypeUse(importTy),
          sym = importTySym,
          wrapId = N -> N,
        ),
      )
  end getOrLoadStrCtorFunction

  /** Gets (and caches) the Wasm GC array type used for tuples (`mut` selects mutability).
    */
  private def tupleArrayType(mut: Bool)(using Raise): TypeIdx =
    ctx.getOrCreateWasmIntrinsicType(WasmIntrinsicType.TupleArray(mutable = mut)):
      val suffix = if mut then "Mut" else ""
      val sym = BlockMemberSymbol(s"TupleArray$suffix", Nil)
      ctx.addType(TypeInfo(
        sym,
        ArrayType(elemType = RefType.anyref, mutable = mut),
        objectTag = N,
      ))

  /** Allocates a fresh temp local (typed `anyref`) and returns its `LocalIdx`.
    */
  private def mkTempLocal(base: Str, erasedType: Opt[ErasedValueType])(using FunctionCtx, Raise): LocalIdx =
    funcCtx.addLocal(TempSymbol(N, erasedType, base))

  /** Binds constructor self (`thisSym`) to the Wasm local name `this` in the current function context.
    */
  private def bindCtorThis(thisSym: InnerSymbol)(using FunctionCtx, Raise): LocalIdx =
    funcCtx.addLocal(thisSym, S("this"))

  /** Replaces a declared function's placeholder while retaining its physical signature and exported identity. */
  private def definePredeclaredFunction(sym: ExternSymbol, body: Seq[Expr], frame: FunctionCtx)(using Raise): Unit =
    val declared = ctx.getFuncInfo_!(sym)
    val compiled = FuncInfo(
      sym = sym,
      wrapId = declared.wrapId,
      typeUse = declared.typeUse,
      params = frame.resolvedParams,
      resultTypes = declared.resultTypes,
      locals = frame.locals,
      body = body,
      optionalParams = declared.optionalParams,
    )
    softAssert(compiled.id == declared.id, s"Function ID changed while defining `${sym.nme}`")
    ctx.addFunc(compiled)
    ()

  /** Allocates the registered instance layout, calls its initializer, and returns the new instance.
    * Source classes and the intrinsic Unit object share this allocation convention. */
  private def defineClassConstructor(sym: BaseTypeSymbol, params: LoweredParamList, loc: Opt[Loc])(using Raise): Unit =
    val typeref = ctx.getType_!(sym)
    val typeinfo = ctx.getTypeInfo_!(typeref)
    assert(typeinfo.objectTag.nonEmpty, s"Expected class $sym to have an object tag")
    val instanceFields = typeinfo.compType match
      case struct: StructType =>
        struct.fields match
          case _ +: rest =>
            getClassTypeInfoGlobal(sym).get +: rest.map((_, field) => defaultStructFieldValue(field))
          case Nil => lastWords(s"Expected instance struct for $sym to include $$typeinfo header")
      case other => lastWords(s"Expected struct type for $sym, found ${other.toWat.mkString()}")
    val (body, frame) = genFuncBody(params :: Nil, thisSym = N, resultType = N, loc = loc):
      val thisVar = bindCtorThis(sym)
      val initCall = call(
        funcidx = ctx.getFunc_!(initFuncSym(sym)),
        operands = local.get(thisVar, RefType(typeref, nullable = false)) +:
          funcCtx.params.map((_, nme) => getLocalAnyref(LocalIdx(nme))),
        returnTypes = Vector(Result(RefType(typeref, nullable = false))),
      )
      Vector(
        local.set(thisVar, struct.`new`(typeref, instanceFields)),
        drop(initCall),
        `return`(S(local.get(thisVar, RefType(typeref, nullable = false)))),
      )
    definePredeclaredFunction(sym, body, frame)

  /** Compiles a class init body under its own Wasm-local frame with explicit `this`. */
  private def setupInitLocals(
      clsLikeDefn: ClsLikeDefn,
  )(using Raise): (Seq[Expr], FunctionCtx) =
    genFuncBody(
      classCtorParamList(clsLikeDefn) :: Nil,
      thisSym = S(clsLikeDefn.isym),
      resultType = N,
      loc = clsLikeDefn.sym.toLoc,
      paramTypes = S(Seq(RefType(ctx.getType_!(classSym(clsLikeDefn)), nullable = false))),
    ):
      val thisVar = funcCtx.lookupLocal_!(clsLikeDefn.isym, N)
      val typeref = ctx.getType_!(classSym(clsLikeDefn))
      val preCtorWat = compilePreCtor(clsLikeDefn, thisVar)
      val ctorWat = block(clsLikeDefn.ctor)
      val retWat = `return`(S(ref.cast(local.get(thisVar, RefType.anyref), RefType(typeref, nullable = false))))
      preCtorWat ++ ctorWat :+ retWat

  /** Lowers an inherited pre-constructor by preserving its setup code and rewriting the final `super(...)` into
    * `Parent_init(this, ...)`.
    */
  private def compilePreCtor(
      clsLikeDefn: ClsLikeDefn,
      thisVar: LocalIdx,
  )(using FunctionCtx, Raise): Vector[Expr] =
    def withRest(block: NonBlockTail, rest: Block): Block = block match
      case Scoped(syms, _) => Scoped(syms, rest)
      case Begin(sub, _) => Begin(sub, rest)
      case TryBlock(sub, finallyDo, _) => TryBlock(sub, finallyDo, rest)
      case Assign(lhs, rhs, _) => Assign(lhs, rhs, rest)
      case af @ AssignField(lhs, nme, rhs, _) => AssignField(lhs, nme, rhs, rest)(af.symbol)
      case AssignDynField(lhs, fld, kind, rhs, _) => AssignDynField(lhs, fld, kind, rhs, rest)
      case Define(defn, _) => Define(defn, rest)
      case Match(scrut, arms, dflt, _) => Match(scrut, arms, dflt, rest)
      case Label(label, loop, body, _) => Label(label, loop, body, rest)

    def splitSuperTail(block: Block): Opt[Block -> Ls[Arg]] = block match
      case End(_) => N
      case Assign(NoSymbol, Call(Value.SimpleRef(State.superSymbol), argss), _: End) =>
        S(End("") -> argss.flatten)
      case b: NonBlockTail =>
        splitSuperTail(b.rest).map: (prefix, args) =>
          withRest(b, prefix) -> args
      case _ => N

    clsLikeDefn.preCtor match
      case End(_) => Vector.empty
      case _ =>
        splitSuperTail(clsLikeDefn.preCtor) match
          case S((prefixBlock, args)) =>
            val prefixWat = block(prefixBlock)
            resolveParentSym(clsLikeDefn) match
              case S(parentSym) =>
                val parentTypeRef = ctx.getType_!(parentSym)
                val parentInitFunc = initFuncSym(parentSym)
                val parentInitType = ctx.getTypeInfo_!(ctx.getFuncTypeUse_!(parentInitFunc).typeIdx)
                val superCall = call(
                  funcidx = ctx.getFunc_!(parentInitFunc),
                  operands = adaptCallArgs(
                    args,
                    parentInitType,
                    S(local.get(thisVar, RefType(parentTypeRef, nullable = false))),
                    clsLikeDefn.sym.toLoc,
                  ),
                  returnTypes = Seq(Result(RefType(parentTypeRef, nullable = false))),
                )
                prefixWat :+ drop(superCall)
              case N => Vector.empty
          case N =>
            raise(ErrorReport(
              msg"Wasm preCtor lowering only supports lowered super(...) shapes." ->
                clsLikeDefn.sym.toLoc :: Nil,
              extraInfo = S(clsLikeDefn.preCtor.showAsTree),
              source = Diagnostic.Source.Compilation,
            ))
            Vector.empty
    end match
  end compilePreCtor

  /** MIR function bodies return explicitly, as specified in Block.scala's design notes. This helper also emits
    * `Program.main`, whose fallthrough supplies an unspecified value in the entry function's result representation.
    * An inner `End` only continues after its enclosing block, so matches and labels must not manufacture their own
    * result values.
    *
    * The instructions form the Wasm function body directly. Wrapping them in a `block` would be redundant, and a block
    * ending in a control transfer would also need the function's result type to be valid under the core spec.
    */
  private def functionBody(body: Block)(using FunctionCtx, Raise): Vector[Expr] =
    val exprs = block(body)
    softAssert(
      exprs.forall(_.resultTypes.forall(_ is UnreachableType)),
      "MIR statements must not leave Wasm values on the stack",
    )
    val tail =
      if exprs.lastOption.exists(_.isControlTransfer) then Vector.empty
      // Wasm cannot infer that every branch of a statement match returns or throws.
      else if body.isAbortive then Vector(unreachable)
      else
        val undefined = Value.Lit(UnitLit(false))(N)
        Vector(summon[FunctionCtx].resultType.fold(result(undefined))(castToValType(undefined, _, N)))
    exprs ++ tail

  /** Validates an IntLit value fits signed 32-bit and delegates codegen to `onValid`.
    */
  private def withValidIntLit(
      value: BigInt,
      loc: Opt[Loc],
  )(onValid: Int => Expr)(using Raise, Line): Expr =
    if value.isValidInt then onValid(value.toInt)
    else
      errExpr(
        Ls(msg"WatBuilder::IntLit lowering with value outside signed 32-bit range not implemented yet" -> loc),
        extraInfo = S(value.toString),
      )

  /** Emits a tuple element load that works for both mutable and immutable tuple arrays.
    */
  private def tupleArrayGet(tupleExpr: Expr, idxBuilder: Expr => Expr)(using FunctionCtx, Raise): Expr =
    val elemType = RefType.anyref
    val mutArrayType = tupleArrayType(true)
    val immArrayType = tupleArrayType(false)
    val tupleTmp = mkTempLocal("tuple", erasedType = N)
    val tupleIsMutable = ref.test(local.tee(tupleTmp, tupleExpr), RefType(mutArrayType, nullable = true))
    val tupleValue = local.get(tupleTmp, RefType.anyref)
    val mutableBranch =
      val tupleRef = ref.cast(tupleValue, RefType(mutArrayType, nullable = false))
      array.get(mutArrayType, tupleRef, idxBuilder(tupleRef), elemType)
    val immutableBranch =
      val tupleRef = ref.cast(tupleValue, RefType(immArrayType, nullable = false))
      array.get(immArrayType, tupleRef, idxBuilder(tupleRef), elemType)
    `if`(
      condition = tupleIsMutable,
      ifTrue = mutableBranch,
      ifFalse = S(immutableBranch),
      resultTypes = Seq(Result(elemType.asValType_!)),
    )

  /** Builds an i32 index for tuple indexing (supports negative indices; caches non-literals).
    */
  private def compileTupleIndex(
      fld: Path,
      loc: Opt[Loc],
      errCtx: Str,
      errExtra: => Str,
  )(using FunctionCtx, Raise): Expr => Expr =
    fld match
      case Value.Lit(IntLit(value)) if value.isValidInt =>
        val idx = value.toInt
        tupleRef =>
          if idx >= 0 then i32.const(idx)
          else i32.add(array.len(tupleRef), i32.const(idx))
      case _ =>
        val rawIdx = result(fld)
        val idxI32 = rawIdx.resultType match
          case S(I32Type) => rawIdx
          case S(RefType(HeapType.I31, _)) => i31.get(rawIdx, signed = true)
          case S(RefType(HeapType.Any, _)) =>
            val casted = ref.cast(rawIdx, RefType.i31ref)
            i31.get(casted, signed = true)
          case ty =>
            return (_: Expr) =>
              errExpr(
                msg"$errCtx expects an integer index but found ${ty.fold("(none)")(_.toWat.mkString())}" -> loc :: Nil,
                extraInfo = S(errExtra),
              )

        val idxTmp = mkTempLocal("idx", erasedType = S(ErasedType.Int31))

        tupleRef =>
          val storeIdx = local.set(idxTmp, ref.i31(idxI32))
          def idxVal: Expr = i31.get(ref.cast(local.get(idxTmp, RefType.anyref), RefType.i31ref), signed = true)

          val normalizedIdx = `if`(
            condition = i32.lt_s(idxVal, i32.const(0)),
            ifTrue = i32.add(idxVal, array.len(tupleRef)),
            ifFalse = S(idxVal),
            resultTypes = Seq(Result(I32Type)),
          )

          Seq(storeIdx, normalizedIdx).mergeAsBlock_!

  /** Raises a [[WarningReport]] with the given `warnMsgs` and `extraInfo`, and emits the `defaultValue` instruction.
    */
  def warnExpr(
      warnMsgs: Ls[Message -> Opt[Loc]],
      extraInfo: Opt[Any] = N,
  )(defaultValue: => FoldedInstr = unreachable)(using Raise)(using Line): Expr =
    raise(WarningReport(warnMsgs, source = Diagnostic.Source.Compilation, extraInfo = extraInfo))
    defaultValue

  /** Raises an [[ErrorReport]] with the given `warnMsgs` and `extraInfo`, and emits an `unreachable` instruction.
    */
  def errExpr(
      errMsgs: Ls[Message -> Opt[Loc]],
      extraInfo: => Opt[Any] = N,
  )(using Raise)(using Line): Expr =
    raise(ErrorReport(errMsgs, source = Diagnostic.Source.Compilation, extraInfo = extraInfo))
    unreachable

  /** The local or global index for `l`, or `N` when it is neither.
    *
    * An [[InnerSymbol]] is a hard failure: it never denotes a variable slot.
    */
  def varIndex(l: WasmSlotSymbol, loc: Opt[Loc])(using FunctionCtx, Raise): Opt[LocalIdx | GlobalIdx] = l match
    case ts: InnerSymbol =>
      lastWords(s"InnerSymbol `$ts` (${ts.getClass.getSimpleName}) cannot be resolved as a variable")
    case l: ScopedSymbol =>
      funcCtx.lookupLocal(l) match
        case S(localIdx) => S(localIdx)
        case _ => ctx.getGlobal(l)

  def getVar(l: WasmSlotSymbol, loc: Opt[Loc])(using FunctionCtx, Raise): Expr = varIndex(l, loc) match
    case S(localIdx: LocalIdx) => local.get(localIdx, funcCtx.slotType(l))
    case S(globalIdx: GlobalIdx) =>
      castConserve(
        global.get(globalIdx, ctx.getGlobalType_!(globalIdx).globalType.valType),
        l.localType,
        loc,
      )
    case N =>
      errExpr(
        Ls(
          msg"Cannot find variable `${l.toString}` (${l.getClass.getSimpleName}) in local or global scope." ->
            l.toLoc,
        ),
        extraInfo = S(
          s"Locals: ${(funcCtx.params ++ funcCtx.locals).toString}\nGlobals: ${ctx.getGlobals.toString}",
        ),
      )

  /** Stores `value` into the local or global slot for `l`, narrowing it to the slot's declared type. The write-side
    * dual of [[getVar]].
    */
  def setVar(
      l: WasmSlotSymbol,
      value: codegen.Result,
      loc: Opt[Loc],
  )(using FunctionCtx, Raise): Expr = varIndex(l, loc) match
    case S(localIdx: LocalIdx) => local.set(localIdx, castToValType(value, funcCtx.slotType(l), loc))
    case S(globalIdx: GlobalIdx) =>
      global.set(globalIdx, castToValType(value, ctx.getGlobalType_!(globalIdx).globalType.valType, loc))
    case N =>
      errExpr(
        Ls(
          msg"Cannot find variable `${l.toString}` (${l.getClass.getSimpleName}) in local or global scope." ->
            l.toLoc,
        ),
        extraInfo = S(
          s"Locals: ${(funcCtx.params ++ funcCtx.locals).toString}\nGlobals: ${ctx.getGlobals.toString}",
        ),
      )

  /** Compiles `a`, narrowing it to `expected` when given. `loc` locates a failed cast if the argument has no location
    * of its own.
    */
  private def argument(
    a: Arg,
    expected: Opt[ValType],
    loc: Opt[Loc],
  )(using FunctionCtx, Raise): Expr =
    if a.spread.nonEmpty then
      errExpr(
        Ls(msg"WatBackend::argument for spread expression not implemented yet" -> a.value.toLoc),
        extraInfo = S(a.showAsTree),
      )
    else expected.fold(result(a.value))(castToValType(a.value, _, loc))

  def operand(a: Arg)(using FunctionCtx, Raise): Expr =
    if a.spread.nonEmpty then die else subexpression(a.value)

  def subexpression(r: codegen.Result)(using FunctionCtx, Raise): Expr = r match
    case r: Lambda =>
      errExpr(
        Ls(msg"WatBuilder::subexpression for Lambda not implemented yet" -> r.toLoc),
        extraInfo = S(r.showAsTree),
      )
    case r => result(r)

  /** Returns the class or object that owns a resolved field or method symbol, when available. */
  private def fieldOwner(sym: DefinitionSymbol[?]): Opt[BaseTypeSymbol] = sym match
    case ts: TermSymbol => ts.owner match
      case S(cls: BaseTypeSymbol) => S(cls)
      case _ => N
    case _ => N

  /** Resolve the layout slot once for both its physical offset and its declared type. */
  private def classField(thisSym: TypeKey | TypeIdx, sym: DefinitionSymbol[?])(using Ctx): (FieldIdx, Field) =
    val structInfo = ctx.getTypeInfo_!(thisSym)
    val fields = structInfo.compType match
      case ty: StructType => ty.fields
      case _ => lastWords(s"Cannot select field from non-struct type: ${structInfo.compType.toWat.mkString()}")
    val exactOffset = fields.indexWhere(_._1 == sym)
    val offset = if exactOffset >= 0 then exactOffset else
      // A subclass symbol can name an inherited public slot. Resolve the alias from the
      // immutable layout, which also works for class layouts imported from an earlier session.
      sym match
        case target: TermSymbol if !target.isPrivate =>
          fields.indexWhere:
            case (base: TermSymbol, _) => !base.isPrivate && base.nme == target.nme
            case _ => false
        case _ => -1
    assert(offset >= 0, s"Missing field $sym in struct $thisSym")
    val field = fields(offset)._2
    (field.index(offset), field)
  end classField

  def fieldSelect(thisSym: TypeKey | TypeIdx, sym: DefinitionSymbol[?])(using Ctx): FieldIdx =
    classField(thisSym, sym)._1
  end fieldSelect

  /** Returns `sym` when it denotes a class method with a predeclared function or a virtual slot. */
  private def predeclaredClassMethodSym(sym: DefinitionSymbol[?]): Opt[TermSymbol] = sym match
    case methodSym: TermSymbol => methodSym.owner match
      case S(_: ClassSymbol) => methodSym.optionIf: methodSym =>
        ctx.getFunc(methodSym).nonEmpty ||
          fieldOwner(methodSym).flatMap(ctx.getVirtualTable).exists(_.slotOf.contains(methodSym))
      case _ => N
    case _ => N

  /** Lowers a class method call, using virtual dispatch only when the selected owner class has a virtual slot. */
  private def lowerClassMethodCall(
      qual: Path,
      methodSym: TermSymbol,
      args: Seq[Arg],
      virtual: Bool,
  )(using FunctionCtx, Raise): Ls[Expr] =
    val ownerCls = fieldOwner(methodSym).get
    ctx.getVirtualTable(ownerCls).filter(_ => virtual).flatMap(vt =>
      vt.slotOf.get(methodSym).map(slot => (vt, slot)),
    ) match
      case S((vt, slot)) =>
        val baseSym = vt.slots(slot).owner
        val paramTypes = vt.slots(slot).paramTypes
        val resultType = vt.slots(slot).resultType
        val ownerTypeInfoIdx = typeInfoTypeIdxs(ownerCls)()
        val receiverTmp = mkTempLocal("receiver", erasedType = N)
        val receiverExpr = local.set(receiverTmp, result(qual))
        val receiverRef = local.get(receiverTmp, RefType.anyref)
        val ownerTypeInfoRef = ref.cast(
          readObjectTypeInfo(receiverRef),
          RefType(ownerTypeInfoIdx, nullable = false),
        )
        val virtualMethodTypeIdx = virtualMethodFuncType(baseSym, paramTypes, resultType)
        val slotSym = ctx.getTypeInfo_!(ownerTypeInfoIdx).compType match
          case ty: StructType => ty.fields.find(_._2.id == s"slot$slot").map(_._1)
            .getOrElse(lastWords(s"Missing virtual slot $slot in $ownerCls"))
          case _ => lastWords(s"RTTI for $ownerCls must be a struct")
        val methodRef = struct.get(
          fieldSelect(ownerTypeInfoIdx, slotSym),
          ownerTypeInfoRef,
          RefType(virtualMethodTypeIdx, nullable = true),
        )
        val operands = adaptCallArgs(args, ctx.getTypeInfo_!(virtualMethodTypeIdx), S(receiverRef), qual.toLoc)
        val virtualCall = call_ref(
          target = methodRef,
          operands = operands,
          typeIdx = virtualMethodTypeIdx,
          funcType = virtualMethodSignature(baseSym, paramTypes, resultType),
        )
        // The slot carries the *base* declaration's result type, but the resolved method's declared result may be
        // overridden to be narrower. Restore the slot's result value to the resolved method's declared type here -
        // the checked cast ensures that a value that doesn't conform will trap at runtime.
        // Nothing has no representation to restore: consumers evaluate the call and supply their own value.
        val adaptedCall = if hasBottomResult(methodSym) then virtualCall
        else castConserve(virtualCall, declaredResultType(methodSym), qual.toLoc)
        Ls(receiverExpr, adaptedCall)
      case N =>
        val funcTypeInfo = ctx.getTypeInfo_!(ctx.getFuncTypeUse_!(methodSym).typeIdx)
        val operands = adaptCallArgs(args, funcTypeInfo, S(result(qual)), qual.toLoc)
        Ls(call(
          funcidx = ctx.getFunc_!(methodSym),
          operands = operands,
          returnTypes = funcTypeInfo.asFunctionType_!.sigType.results,
        ))
    end match
  end lowerClassMethodCall

  def result(r: codegen.Result)(using FunctionCtx, Raise): Expr = r match
    case Value.Lit(BoolLit(value)) =>
      ref.i31(i32.const(if value then 1 else 0))
    case Value.Lit(IntLit(value)) =>
      withValidIntLit(value, r.toLoc)(intVal => ref.i31(i32.const(intVal)))
    case Value.Lit(StrLit(value)) =>
      val lit = internStringLiteral(value)
      val stringCtor = getOrLoadStrCtorFunction
      call(
        funcidx = stringCtor,
        operands = Seq(ref.i31(i32.const(lit.offset)), ref.i31(i32.const(lit.byteLen))),
        returnTypes = Seq(Result(RefType.anyref)),
      )
    case sel: Select if staticSelection(sel).nonEmpty =>
      val sym = staticSelection(sel).get
      ctx.getFunc(sym) match
        case S(idx) => ref.func(idx, RefType(ctx.getFuncTypeUse_!(sym).typeIdx, nullable = false))
        case N => getVar(sym, sel.toLoc)
    case Value.Lit(UnitLit(true)) => ref.`null`(HeapType.Any)
    case Value.Lit(UnitLit(false)) =>
      // Without a destination representation, use the Unit singleton for an unspecified value.
      singletonGlobalGet(ctx.getSingletonInfo(State.unitSymbol).getOrElse:
        lastWords("Missing runtime Unit singleton"))
    case Value.SimpleRef(sym) if sym is State.runtimeSymbol =>
      errExpr(Ls(msg"This runtime operation is not supported by the WebAssembly backend" -> r.toLoc))
    case Value.SimpleRef(l) => l match
      case l: LocalVarSymbol => getVar(l, r.toLoc)
      case bs: BuiltinSymbol => errExpr(
          Ls(msg"Unexpected reference to a builtin symbol '${bs.nme}' in result position" -> r.toLoc),
          extraInfo = S(r.toString),
        )
    case r: Path if namespace(r).nonEmpty =>
      errExpr(Ls(msg"First-class module values are not supported by the WASM backend" -> r.toLoc))
    case Value.MemberRef(bms, disamb) =>
      val singleton = disamb match
        case obj: ModuleOrObjectSymbol => singletonInfoFor(obj)
        case _ => N
      singleton match
        case S(info) => singletonGlobalGet(info)
        case N =>
          if disamb.isInstanceOf[ClassSymbol] then
            errExpr:
              Ls(msg"Plain class references are not supported in Wasm; instantiate the class instead." -> r.toLoc)
          else
            ctx.getFunc(ExternSymbol.forReference(bms, disamb)) match
              case S(funcIdx) => ref.func(funcIdx, RefType(ctx.getFuncTypeUse_!(funcIdx).typeIdx, nullable = false))
              case N => getVar(bms, r.toLoc)
    case Value.This(_: TopLevelSymbol) =>
      errExpr:
        Ls(msg"The global object is not supported in Wasm." -> r.toLoc)
    case Value.This(sym: InnerSymbol) =>
      // In a singleton constructor, `this` is the new instance, not the backing global
      // (which is still null until construction finishes).
      singletonInfoFor(sym).filter(_ => funcCtx.lookupLocal(sym).isEmpty) match
        case S(info) => singletonGlobalGet(info)
        case N =>
          val thisTypeIdx = sym match
            case cls: BaseTypeSymbol => ctx.getType_!(cls)
            case _ => baseObjectTypeIdx
          castConserve(
            local.get(funcCtx.lookupLocal_!(sym, sym.toLoc), funcCtx.slotType(sym)),
            RefType(thisTypeIdx, nullable = false),
            r.toLoc,
          )

    case Call(sel @ Select(qual, _), argss) if sel.symbol.flatMap(predeclaredClassMethodSym).nonEmpty =>
      if argss.length > 1 then
        return errExpr(
          Ls(msg"WatBuilder::result for Call(...) with multiple argument lists is not supported yet" -> r.toLoc),
          extraInfo = S(r.toString),
        )
      val args = argss.flatten
      val methodSym = sel.symbol.flatMap(predeclaredClassMethodSym).get
      lowerClassMethodCall(qual, methodSym, args, virtual = true).mergeAsBlock_!

    case c @ Call(sel: SuperSelect, argss) =>
      if argss.length != 1 then
        errExpr(Ls(msg"Super calls with multiple parameter lists are not supported by WASM" -> c.toLoc))
      else lowerClassMethodCall(sel.qual, sel.symbol, argss.head, virtual = false).mergeAsBlock_!

    case sel: SuperSelect =>
      if sel.symbol.defn.exists(_.params.isEmpty) then
        lowerClassMethodCall(sel.qual, sel.symbol, Nil, virtual = false).mergeAsBlock_!
      else errExpr(Ls(msg"Super method values are not supported by WASM" -> sel.toLoc))

    case c @ Call(fun, argss) =>
      if argss.length > 1 then
        return errExpr(
          Ls(msg"WatBuilder::result for Call(...) with multiple argument lists is not supported yet" -> c.toLoc),
          extraInfo = S(c.toString),
        )
      val args = argss.flatten
      wasmIntrinsicName(fun) match
        case S(intrName) =>
          Ctx.wasmInstrIntrinsics.get(intrName) match
            case S(body) =>
              val declaredParams = fun.targetSymbol match
                case S(ts: TermSymbol) =>
                  ts.erasedSignature.map(_.paramLists)
                case _ => N
              val ps = declaredParams match
                case S(pl :: Nil) => pl
                // * The prelude declares every `wasm.` intrinsic with exactly one parameter list; a curried (or
                // * parameterless) one has no meaning as an instruction.
                case S(_) =>
                  lastWords(s"wasm intrinsic '$intrName' must be declared with exactly one parameter list")
                // * `Lowering` attaches the intrinsic's `TermSymbol` to the path it builds, so an implemented
                // * intrinsic always has a declared signature here.
                case N =>
                  lastWords(s"wasm intrinsic '$intrName' is implemented but has no declared signature")
              if ps.length =/= args.length then
                return errExpr(
                  Ls(msg"Wasm intrinsic '$intrName' called with incorrect arity (${args.length})" -> c.toLoc),
                  extraInfo = S(c.toString),
                )
              body(ps.zip(args).zipWithIndex.map:
                case ((declared, arg), idx) => resolveIntrinsicArg(intrName, idx, declared, arg))
            // * `Lowering` marks every function the prelude declares under `wasm` as an intrinsic, so a name that is
            // * neither implemented as an instruction above nor generated as an operator function here is one the
            // * prelude declares and the backend does not implement.
            case N => wasmIntrinsicArities.get(intrName) match
              case N =>
                errExpr(
                  Ls(msg"Wasm intrinsic '$intrName' is declared but not implemented" -> c.toLoc),
                  extraInfo = S(c.toString),
                )
              case S(expectedArity) if expectedArity =/= args.length =>
                errExpr(
                  Ls(msg"Wasm intrinsic '$intrName' called with incorrect arity (${args.length})" -> c.toLoc),
                  extraInfo = S(c.toString),
                )
              case S(_) =>
                call(
                  funcidx = getIntrinsic(intrName),
                  operands = args.map(argument(_, N, N)),
                  returnTypes = Seq(Result(RefType.anyref)),
                )
        case N =>
          fun match
            case Value.MemberRef(l, disamb) =>
              val base = ctx.getFunc(ExternSymbol.forReference(l, disamb))
              val baseFuncIdx = base match
                case S(idx) => idx
                case N => return errExpr(
                    Ls(msg"Expected static function reference in Call(...) expression" -> fun.toLoc),
                    extraInfo = S(fun.toString),
                  )
              val baseTypeInfo = ctx.getTypeInfo_!(ctx.getFuncTypeUse_!(baseFuncIdx).typeIdx)
              val wasmArgs = adaptCallArgs(args, baseTypeInfo, N, c.toLoc)

              call(
                funcidx = baseFuncIdx,
                operands = wasmArgs,
                returnTypes = baseTypeInfo.asFunctionType_!.sigType.results,
              )
            case _ =>
              val base = subexpression(fun)
              if base.resultTypes.exists(_ is UnreachableType) then return base

              val baseTypeIdx = base.resultType match
                case S(RefType(idx: TypeIdx, _)) => idx
                case ty =>
                  return errExpr(
                    Ls(msg"Expected WAT of `fun` expression in Call(...) to have a `(ref <typeidx>)` type" -> r.toLoc),
                    extraInfo = S(
                      s"Block IR: `${
                          fun.toString
                        }`\nCompiled WAT: `${
                          base.toWat.mkString()
                        }`\n... which has type `${
                          ty.fold("(none)")(_.toWat.mkString())
                        }`",
                    ),
                  )
              val baseTypeInfo = ctx.getTypeInfo_!(baseTypeIdx)
              val wasmArgs = adaptCallArgs(args, baseTypeInfo, N, c.toLoc)

              call_ref(
                target = base,
                operands = wasmArgs,
                typeIdx = baseTypeIdx,
                funcType = baseTypeInfo.asFunctionType_!,
              )
      end match

    case sel @ Select(qual, id) =>
      sel.symbol match
        case S(selObj: ModuleOrObjectSymbol) =>
          singletonInfoFor(selObj) match
            case S(info) => singletonGlobalGet(info)
            case N =>
              errExpr(
                Ls(msg"WatBuilder::result for object selection `${id.name}` not implemented yet" -> sel.toLoc),
                extraInfo = S(sel),
              )

        case S(selSym) if predeclaredClassMethodSym(selSym).nonEmpty =>
          val methodSym = predeclaredClassMethodSym(selSym).get
          methodSym.defn match
            case S(defn: TermDefinition) if defn.params.isEmpty =>
              lowerClassMethodCall(qual, methodSym, Nil, virtual = true).mergeAsBlock_!
            case _ =>
              errExpr(
                Ls(
                  msg"`${methodSym.nme}` is neither a field access nor a callable method" ->
                    sel.toLoc,
                ),
                extraInfo = S(sel),
              )

        case S(selSym: MemberSymbol) =>
          val qualRes = result(qual)
          if qualRes.resultType.contains(UnreachableType) then return qualRes
          val selCls = fieldOwner(selSym) match
            case S(owner) => owner
            case N => return errExpr:
              Ls(
                msg"Selecting member '${id.name}' is not supported by the WebAssembly backend" -> sel.toLoc,
              )
          if ctx.getTypeInfo(selCls).isEmpty then return errExpr:
            Ls(
              msg"Selecting member '${id.name}' of '${selCls.nme}' is not supported by the WebAssembly backend" ->
                sel.toLoc,
            )
          val (fieldidx, field) = classField(selCls, selSym)
          val fieldTy = field.ty
          // `struct.get` traps on a null reference, so narrowing the object to the nullable class type is
          // enough, and an object already stored in a slot of the class's type needs no cast.
          val getExpr = struct.get(
            fieldidx,
            ref = castConserve(qualRes, RefType(ctx.getType_!(selCls), nullable = true), sel.toLoc),
            ty = fieldTy,
          )
          val declaredType = selSym match
            case field: TermSymbol => field.erasedType.flatMap(_.wasmType)
            case _ => N
          declaredType match
            case S(declared) => castConserve(getExpr, declared, sel.toLoc)
            case N => fieldTy match
              case rt: RefType if rt.nullable && rt.heapType != HeapType.Any =>
                castConserve(getExpr, rt.copy(nullable = false), sel.toLoc)
              case _ => getExpr
        case N =>
          errExpr(
            Ls(
              msg"WatBuilder::result for field selection without a resolved symbol is not implemented (field `${
                  id.name
                }`). Use `_.[_]` for index-based accesses." ->
                sel.toLoc,
            ),
            extraInfo = S(sel),
          )

    case dyn @ DynSelect(qual, fld, kind) =>
      val qualRes = result(qual)
      if kind.isArrayIdx then
        val idxBuilder = compileTupleIndex(
          fld = fld,
          loc = fld.toLoc,
          errCtx = "WatBuilder::result for array-style dynamic selections",
          errExtra = dyn.toString,
        )
        tupleArrayGet(qualRes, idxBuilder)
      else
        errExpr(
          Ls(msg"WatBuilder::result for dynamic field selections is not implemented yet" -> dyn.toLoc),
          extraInfo = S(dyn),
        )

    case Instantiate(_, cls, argss) =>
      if argss.length > 1 then
        return errExpr(
          Ls(msg"WatBuilder::result for Instantiate(...) with multiple argument lists is not supported yet" -> r.toLoc),
          extraInfo = S(r.toString),
        )
      val as = argss.flatten
      cls match
        // TODO: Implement proper lowering for Errors with unit payloads.
        case Select(Value.This(sym), id) if (sym eq State.globalThisSymbol) && id.name == "Error" =>
          return as.headOption match
            case S(arg) => arg.value match
                case Value.Lit(BoolLit(value)) => ref.i31(i32.const(if value then 1 else 0))
                case Value.Lit(IntLit(value)) =>
                  withValidIntLit(value, arg.value.toLoc)(intVal => ref.i31(i32.const(intVal)))
                case Value.Lit(StrLit(_)) => result(arg.value)
                case unsupported =>
                  warnExpr(
                    msg"WatBuilder::result for Instantiate(...) of `globalThis.Error(...)` with payload `${
                        unsupported.toString
                      }` not implemented yet" ->
                      unsupported.toLoc :: Nil,
                    extraInfo = S(unsupported.toString),
                  ):
                    ref.i31(i32.const(0))
            case N => ref.i31(i32.const(0))
        case _ => ()
      end match
      // The constructed class, which identifies both its constructor function and its struct type.
      def instantiated(sym: Symbol): Opt[ClassSymbol] = sym match
        case cls: ClassSymbol => S(cls)
        case ctor: ClassCtorSymbol => S(ctor.associatedCls)
        case _ => N
      val ctorClsSymOpt = cls match
        case ref: Value.MemberRef => instantiated(ref.disamb)
        case sel: Select => sel.symbol.flatMap(instantiated)
        case cls => return errExpr(
            Ls(
              msg"WatBuilder::result for Instantiate(...) where `cls` is not a Ref(...) or Select(...) path not implemented yet " ->
                cls.toLoc,
            ),
            extraInfo = S(s"Block IR of `cls` expression: ${cls.toString}"),
          )
      val ctorClsSym = ctorClsSymOpt match
        case S(sym) => sym
        case N => return errExpr(
            Ls(msg"Class path for an Instantiate(...) expression must be resolved" -> cls.toLoc),
            extraInfo = S(s"Block IR of `cls` expression: ${cls.toString}"),
          )
      // A class has a constructor only when the backend compiled its definition. The definition of an
      // unsupported class reports why it was not compiled; builtin classes have no definition here.
      val ctorFuncIdx = ctx.getFunc(ctorClsSym) match
        case S(idx) => idx
        case N => return errExpr(Ls(
          msg"Instantiating class `${ctorClsSym.nme}` is not supported by the WebAssembly backend" -> r.toLoc))
      val ctorTypeIdx = ctx.getTypeInfo(ctx.getFuncTypeUse_!(ctorFuncIdx).typeIdx).getOrElse:
        lastWords(s"Missing type definition for class constructor ${ctorClsSym.toString}")
      val ctorClsTypeIdx = ctx.getType(ctorClsSym).getOrElse:
        lastWords(s"Missing class definition for class ${ctorClsSym.toString}")
      val ctorArgs = adaptCallArgs(as, ctorTypeIdx, N, r.toLoc)
      call(funcidx = ctorFuncIdx, operands = ctorArgs, Seq(Result(RefType(ctorClsTypeIdx, nullable = false))))

    case Tuple(mut, elems) =>
      val tupleValues = elems.map(argument(_, N, N))
      array.new_fixed(tupleArrayType(mut), tupleValues)

    case cast @ Cast(value, target, _) =>
      target.wasmType match
        // Substitution can expose a bottom operand whose effects must run before filling the nullable slot.
        // Ordinary nominal casts still reject null.
        case S(ty @ RefType(_: TypeIdx, _)) if !isBottom(value) =>
          castToValType(value, ty.copy(nullable = false), cast.toLoc)
        case S(ty) => castToValType(value, ty, cast.toLoc)
        case N =>
          target.canonicalize match
            case ErasedType.AnyRef(_, tpeSym: BaseTypeSymbol) if tpeSym.irClsLikeDefn.isDefined =>
              // A concrete class with no Wasm representation means the class definition is missing from the IR.
              softAssert(false, s"no Wasm type is available for cast target `${target.describe}`")
            case _ =>
          result(value)

    case r =>
      errExpr(
        Ls(msg"WatBackend::result for ${r.getClass.getSimpleName} expression not implemented yet" -> r.toLoc),
        extraInfo = S(s"Block IR: `${r.toString}`"),
      )
  end result

  /** Selects a Wasm implementation for a shared MIR operator or an explicit `wasm` intrinsic. Operator calls retain
    * their builtin symbols through lowering and optimization on every target.
    */
  private def wasmIntrinsicName(path: Path): Opt[Str] =
    def loop(p: Path, acc: Ls[Str]): Opt[Str] = p match
      case Select(Value.SimpleRef(sym), ident) if sym eq sym.getState.wasmSymbol =>
        S((ident.name :: acc).mkString("."))
      case Select(qual, ident) =>
        loop(qual, ident.name :: acc)
      case _ => N
    path match
      case Value.SimpleRef(sym: BuiltinSymbol) => sym.arity match
        case BuiltinSymbol.Arity.Unary => WatBuilder.unaryIntrinsicNames.get(sym.nme)
        case BuiltinSymbol.Arity.Binary => WatBuilder.binaryIntrinsicNames.get(sym.nme)
        case BuiltinSymbol.Arity.Variadic => N
      case _ => loop(path, Nil)

  /** Resolves the argument at position `idx` as an [[IntrinsicArg]], recovering the numeric literal it was written as,
    * if it was written as one.
    *
    * `declared` is the type the prelude declares for the parameter. The argument is only compiled as an operand - and
    * its conformance to `declared` only reported - if the intrinsic's body actually reads it as one.
    */
  private def resolveIntrinsicArg(
      intrName: Str,
      idx: Int,
      declared: Opt[ErasedValueType],
      arg: Arg,
  )(using Ctx, FunctionCtx, Raise): IntrinsicArg =
    def compileOperand: (Expr, Opt[Str]) =
      val operand =
        if isBottom(arg.value) then argument(arg, declared.flatMap(_.wasmType), N)
        else argument(arg, N, N)
      operand ->
        declared
          .filter(_.wasmType.exists(expected => !operand.resultType.exists(_.isSubtypeOf(expected))))
          .map(_.describe)
    IntrinsicArg(
      intrName,
      idx,
      compileOperand,
      arg.value.litThroughUncheckedCasts match
        case S(Value.Lit(IntLit(value))) if arg.spread.isEmpty => S(value)
        case S(Value.Lit(DecLit(value))) if arg.spread.isEmpty => S(value)
        case _ => N,
      arg.value.toLoc,
      arg.value.toString,
    )
  end resolveIntrinsicArg

  /** Gets (or creates) the intrinsic function implementing the wasm operator `name`.
    */
  private def getIntrinsic(name: Str)(using Raise): FuncIdx =
    ctx.getOrCreateWasmIntrinsic(name, importIntrinsic(name))

  private def importIntrinsic(name: Str)(using Raise): FuncIdx =
    val typeIdx = WatBuilder.declareIntrinsicType(name)
    ctx.addFunctionImport(WasmImport(
      ExternIntrinsics.SystemModule,
      name,
      ExternType.Func(
        TypeUse(typeIdx),
        TempSymbol(N, initErasedType = N, name),
        wrapId = N -> N,
      ),
    ))

  /** Loads the local `name` as an `anyref`.
    */
  private def getLocalAnyref(idx: LocalIdx): Expr =
    local.get(idx, RefType.anyref)

  extension (expr: Expr)
    private def isControlTransfer: Bool =
      expr.resultType.contains(UnreachableType)

  private def asStatement(expr: Expr): Expr =
    if expr.isControlTransfer then expr
    else
      (1 to expr.resultTypes.size).foldRight(expr): (_, acc) =>
        drop(acc)

  private def asStatement(exprs: Seq[Expr]): Opt[Expr] =
    exprs.mergeAsBlock.map(asStatement(_))

  def returningTerm(t: Block)(using FunctionCtx, Raise): Vector[Expr] =
    t match
      case Assign(NoSymbol, r, rst) =>
        val rExpr = result(r)
        val evalExpr = rExpr.resultType match
          case S(_) => drop(rExpr)
          case N => rExpr
        val rstBlk = returningTerm(rst)
        evalExpr +: rstBlk

      case Assign(l: LocalVarSymbol, r, rst) =>
        val assignExpr = setVar(l, r, l.toLoc)
        val rstBlk = returningTerm(rst)
        assignExpr +: rstBlk

      case assign @ AssignField(lhs, nme, rhs, rst) if namespace(lhs).nonEmpty =>
        val storage = namespace(lhs).flatMap(ns => assign.symbol.flatMap(staticMember(ns, _)))
        val expr = storage match
          case S(sym) => setVar(sym, rhs, rhs.toLoc)
          case N => errExpr(Ls(msg"Unknown WASM module field '${nme.name}'" -> nme.toLoc))
        expr +: returningTerm(rst)

      case assign @ AssignField(lhs, nme, rhs, rst) =>
        val lhsExpr = result(lhs)
        val assignInstr = assign.symbol match
          case S(selSym) =>
            selSym match
              case fieldSym: TermSymbol =>
                val selCls = fieldOwner(fieldSym) getOrElse
                  lastWords(s"Expected resolved AssignField(...) expression `$fieldSym` to have a class owner")
                val (fieldidx, field) = classField(selCls, fieldSym)
                // Like `struct.get`, `struct.set` traps on a null reference.
                val objRef = castConserve(lhsExpr, RefType(ctx.getType_!(selCls), nullable = true), lhs.toLoc)
                val rhsCasted = castToValType(rhs, field.ty, nme.toLoc)
                struct.set(fieldidx, objRef, rhsCasted)
              case _ =>
                lastWords(
                  s"Expected resolved AssignField(...) expression to be a TermSymbol, but got $selSym (${
                      selSym.getClass.getName
                    })",
                )
          case N =>
            errExpr(
              Ls(
                msg"WatBuilder::returningTerm for AssignField(...) without a resolved symbol is not implemented (field `${
                    nme.name
                  }`). Use `_.[_]` for index-based accesses." ->
                  nme.toLoc,
              ),
              extraInfo = S(assign),
            )

        val rstBlk = returningTerm(rst)
        assignInstr +: rstBlk

      case assign @ AssignDynField(lhs, fld, kind, rhs, rst) =>
        val lhsExpr = result(lhs)
        val rhsExpr = result(rhs)
        val assignInstr =
          if kind.isArrayIdx then
            val tupleArrayType = this.tupleArrayType(mut = true)
            val tupleRef = ref.cast(lhsExpr, RefType(tupleArrayType, nullable = false))
            val idxBuilder = compileTupleIndex(
              fld = fld,
              loc = fld.toLoc,
              errCtx = "WatBuilder::returningTerm for AssignDynField(...)",
              errExtra = assign.toString,
            )
            val idxExpr = idxBuilder(tupleRef)
            array.set(tupleArrayType, tupleRef, idxExpr, rhsExpr)
          else
            errExpr(
              Ls(msg"WatBuilder::returningTerm for AssignDynField(...) with a non-index key is not implemented yet" ->
                lhs.toLoc),
              extraInfo = S(assign),
            )

        val rstBlk = returningTerm(rst)
        assignInstr +: rstBlk

      case Define(defn, rst) =>
        def mkThis(sym: InnerSymbol): Expr = result(sym.asThis)
        defn match
          case ValDefn(tsym, sym, p) if staticBindings.contains(tsym) =>
            setVar(staticBindings(tsym), p, p.toLoc) +: returningTerm(rst)
          case ValDefn(tsym, sym, p) =>
            // * Currently we allow `val` outside of object/module scopes,
            // * in which case it has no owner and is just a glorified local variable rather than a field
            tsym.owner match
              case N =>
                val localStorageSym = defn.sym
                val defineExpr = setVar(localStorageSym, p, localStorageSym.toLoc)
                val rstWat = returningTerm(rst)
                defineExpr +: rstWat
              case S(owner) =>
                val ownerCls = fieldOwner(tsym) getOrElse
                  lastWords(s"Field `${tsym.nme}` is owned by `${owner.nme}`, which is not a class or object")
                val (fieldIdx, field) = classField(ownerCls, tsym)
                val pCasted = castToValType(p, field.ty, defn.sym.toLoc)
                val assignInstr = struct.set(
                  index = fieldIdx,
                  ref = mkThis(owner),
                  value = pCasted,
                )
                val rstWat = returningTerm(rst)
                assignInstr +: rstWat

          case ClsLikeDefn(companion = S(body)) if localNamespaces(body.isym) =>
            body.methods.foreach: fd =>
              val ps = fd.params.headOption.getOrElse(LoweredParamList.plain(Nil)(fd.sym.toLoc))
              val declared = ctx.getFuncInfo_!(fd.sym)
              val (wat, fc) = setupFunction(
                N,
                ps,
                fd.body,
                resultType = singleResultType(fd.sym, declared.resultTypes),
                loc = fd.sym.toLoc,
              )
              ctx.addFunc(FuncInfo(fd.sym, declared.typeUse, fc.resolvedParams, declared.resultTypes, fc.locals,
                wat, declared.optionalParams))
            returningTerm(body.ctor) ++ returningTerm(rst)
          case defn: (FunDefn | ClsLikeDefn) =>
            val res: Opt[Expr] = boundary:
              defn match
                case FunDefn(params = Nil) =>
                  lastWords("cannot generate function with no parameter list")
                case fd @ FunDefn(own, sym, dSym, ps :: pss, bod) =>
                  if own.nonEmpty then
                    break(S(errExpr(
                      Ls(
                        msg"WatBuilder::returningTerm for Define(...) with `owner.nonEmpty` not implemented yet" ->
                          defn.sym.toLoc,
                      ),
                      extraInfo = S(defn.showAsTree),
                    )))

                  // Checked before predeclaring, since a function this lowering refuses must not leave a placeholder
                  // behind in the module.
                  if !sym.nameIsMeaningful then
                    break(S(errExpr(
                      Ls(
                        msg"WatBuilder::returningTerm for FunDefn(...) where `!sym.nameIsMeaningful` not implemented yet" ->
                          defn.sym.toLoc,
                      ),
                      extraInfo = S(defn.showAsTree),
                    )))

                  val result = pss.foldRight(bod):
                    case (ps, block) =>
                      Return(Lambda(ps, block)(Nil, N))
                  // Nested functions are not predeclared in `program` - declare them now.
                  // Note that predeclaring functions twice causes an orphaned type to be duplicated in the module.
                  if ctx.getFunc(sym).isEmpty then predeclareTopLevelFun(sym, dSym, ps)
                  val predeclared = ctx.getFuncInfo_!(sym)
                  val (bodyWat, fnCtx) = setupFunction(
                    N,
                    ps,
                    result,
                    resultType = singleResultType(sym, predeclared.resultTypes),
                    loc = sym.toLoc,
                  )

                  val funcInfo = FuncInfo(
                    sym,
                    typeUse = predeclared.typeUse,
                    params = fnCtx.resolvedParams,
                    resultTypes = predeclared.resultTypes,
                    locals = fnCtx.locals,
                    body = bodyWat,
                    optionalParams = predeclared.optionalParams,
                  )
                  softAssert(
                    funcInfo.id == predeclared.id,
                    s"Function ID mismatch while overwriting body for `${sym.nme}`: Predeclared: ${predeclared.id}; Overwriting: ${funcInfo.id}",
                  )
                  ctx.addFunc(funcInfo)

                  N
                case clsLikeDefn: ClsLikeDefn =>
                  // Guard against unsupported features
                  def errUnimplExpr(cond: Str): Nothing = break(S(errExpr(
                    Ls(
                      msg"WatBuilder::returningTerm for ClsLikeDefn(...) where `$cond` not implemented yet" ->
                        clsLikeDefn.sym.toLoc,
                    ),
                    extraInfo = S(defn.showAsTree),
                  )))
                  val isSingletonObj = clsLikeDefn.k is syntax.Obj
                  if !hasStaticOwner(clsLikeDefn) then
                    break(errUnimplExpr("owner.nonEmpty"))
                  if !(clsLikeDefn.k is syntax.Cls) && !isSingletonObj then
                    break(errUnimplExpr("unsupported ClsLikeDefn kind"))
                  val ctorParamList = classCtorParamList(clsLikeDefn)
                  if isSingletonObj && ctorParamList.params.nonEmpty then
                    break(errUnimplExpr("constructor parameters for object"))
                  if isSingletonObj && clsLikeDefn.parentPath.nonEmpty then
                    break(errUnimplExpr("parentPath.nonEmpty for object"))
                  if isSingletonObj && clsLikeDefn.methods.nonEmpty then
                    break(errUnimplExpr("methods.nonEmpty for object"))
                  if clsLikeDefn.companion.isDefined then
                    break(errUnimplExpr("companion.isDefined"))

                  // Use the symbolic type reference (e.g. `$Foo`) in emitted WAT for readability.
                  // Numeric indices are only needed for `$tag` values.
                  val typeref = ctx.getType_!(classSym(clsLikeDefn))

                  val (initWat, initFnCtx) = setupInitLocals(clsLikeDefn)
                  definePredeclaredFunction(initFuncSym(classSym(clsLikeDefn)), initWat, initFnCtx)
                  defineClassConstructor(classSym(clsLikeDefn), ctorParamList, clsLikeDefn.sym.toLoc)

                  def overwriteMethod(
                      method: FunDefn,
                      ps: LoweredParamList,
                  ): Unit =
                    val sym = method.dSym
                    val predeclaredMethod = ctx.getFuncInfo_!(sym)
                    // Reuse the physical signature, including a non-null receiver and any inherited virtual slot.
                    val paramTypes = S(predeclaredMethod.getSignatureType.params.map(_.valtype))
                    val (bodyWat, fnCtx) = setupFunction(
                      S(clsLikeDefn.isym),
                      ps,
                      method.body,
                      resultType = singleResultType(sym, predeclaredMethod.resultTypes),
                      loc = method.sym.toLoc,
                      paramTypes = paramTypes,
                    )
                    definePredeclaredFunction(sym, bodyWat, fnCtx)
                  end overwriteMethod

                  clsLikeDefn.methods.foreach:
                    case method @ FunDefn(params = Nil) =>
                      overwriteMethod(method, LoweredParamList.plain(Nil)(N))
                    case method @ FunDefn(params = ps :: Nil) =>
                      overwriteMethod(method, ps)
                    case methodDefn =>
                      lastWords(
                        s"Class method `$methodDefn` with multiple parameter lists should be rejected in predeclaration pass",
                      )
                  if isSingletonObj then
                    registerSingletonInit(singletonSym(clsLikeDefn), clsLikeDefn.sym.nme, typeref)
                    S(fileSingletonActions(singletonSym(clsLikeDefn)))
                  else N

                case defn =>
                  S(errExpr(
                    Ls(msg"WatBuilder::returningTerm for Define(...) not implemented yet" -> defn.sym.toLoc),
                    extraInfo = S(defn.showAsTree),
                  ))
              end match

            val rstBlk = returningTerm(rst)
            res.toVector ++ rstBlk
        end match

      case Return(res) =>
        // Storage and calling conventions may widen a reference (e.g. a singleton's nullable global).
        // Restore the IR value's type at the return boundary so Block.returnType also describes the emitted value.
        // Nothing leaves the representation to the physical result slot and must preserve operand effects.
        val resWat =
          if isBottom(res) then funcCtx.resultType.fold(result(res))(castToValType(res, _, funcCtx.loc))
          else res.erasedType.flatMap(_.wasmType).fold(result(res))(castToValType(res, _, funcCtx.loc))
        val returned = resWat.resultType match
          case S(refTy: RefType) =>
            refTy.heapType match
              case HeapType.Func =>
                errExpr(Ls(msg"Returning function instances is not supported" -> res.toLoc))
              case typeidx: TypeIdx if ctx.getTypeInfo_!(typeidx).compType.isInstanceOf[FunctionType] =>
                errExpr(Ls(msg"Returning function instances is not supported" -> res.toLoc))
              case _ => resWat
          case _ => resWat

        // Check each return against the physical signature. A return makes the surrounding expression
        // stack-polymorphic, so checking only the complete body's type misses incompatible operands.
        val checked = funcCtx.resultType.fold(returned)(castConserve(returned, _, res.toLoc.orElse(funcCtx.loc)))
        Vector(`return`(S(checked)))

      case Scoped(syms, body) =>
        blockPreamble(syms)
        returningTerm(body)
      case Break(label) =>
        funcCtx.lookupLabel(label) match
          case S(target) => Vector(br(target.breakLabel))
          case N =>
            Vector(errExpr(
              Ls(
                msg"WatBuilder::returningTerm for Break(...) to unknown label `${label.nme}`" -> label.toLoc,
              ),
              extraInfo = S(t.showAsTree),
            ))
      case Continue(label) =>
        funcCtx.lookupLabel(label) match
          case S(target) =>
            target.continueLabel match
              case S(continueLabel) => Vector(br(continueLabel))
              case N =>
                Vector(errExpr(
                  Ls(
                    msg"WatBuilder::returningTerm for Continue(...) to non-loop label `${label.nme}`" -> label.toLoc,
                  ),
                  extraInfo = S(t.showAsTree),
                ))
          case N =>
            Vector(errExpr(
              Ls(
                msg"WatBuilder::returningTerm for Continue(...) to unknown label `${label.nme}`" -> label.toLoc,
              ),
              extraInfo = S(t.showAsTree),
            ))
      case Label(label, loop, body, rst) =>
        val labeledRegion = funcCtx.withLabel(label, hasContinueLabel = loop):
          case LabelTarget(breakLabel, continueLabel) =>
            val bodyExpr = returningTerm(body)
            val bodyStmt = asStatement(bodyExpr)

            if loop then
              blockInstr(
                label = S(breakLabel),
                children = Seq(
                  loopInstr(
                    label = continueLabel,
                    children = bodyStmt.toList,
                    resultTypes = Seq.empty,
                  ),
                ),
                resultTypes = Seq.empty,
              )
            else
              blockInstr(
                label = S(breakLabel),
                children = bodyStmt.toList,
                resultTypes = Seq.empty,
              )

        val rstExpr = returningTerm(rst)
        labeledRegion +: rstExpr
      case Match(scrut, arms, dflt, rst) =>
        val scrutLocalResult = scrut match
          case _: (Value.RefLike | Value.Lit) => N
          case _ => S(mkTempLocal("scrut", erasedType = N))

        val scrutInitExpr = scrutLocalResult.map: scrutLocal =>
          local.set(scrutLocal, result(scrut))

        def getScrutExpr: Expr =
          scrutLocalResult.fold(result(scrut))(getLocalAnyref)

        // Compile each match arm
        val matchBlock = funcCtx.withLabel(LabelSymbol(N, "match"), hasContinueLabel = false):
          case LabelTarget(matchLabel, _) =>
            boundary:
              val armExprs = arms.zipWithIndex.flatMap: (caseAndBody, armIdx) =>
                val (cse, body) = caseAndBody
                lazy val ifTrue =
                  funcCtx.withLabel(LabelSymbol(N, "arm"), hasContinueLabel = false):
                    case LabelTarget(armLabel, _) =>
                      val bodyExpr = returningTerm(body)
                      val armBodyExpr = asStatement(bodyExpr).toVector
                      blockInstr(
                        label = S(armLabel),
                        children = armBodyExpr ++ br(matchLabel).optionUnless(body.isAbortive).toVector,
                        resultTypes = Seq.empty,
                      )
                
                cse match
                  case Case.Lit(lit) =>
                    val testExpr: FoldedInstr = lit match
                      case BoolLit(value) =>
                        val scrutAsI31 = ref.cast(getScrutExpr, RefType.i31ref)
                        val scrutValue = i31.get(scrutAsI31, signed = true)
                        i32.eq(scrutValue, i32.const(if value then 1 else 0))
                      case IntLit(value) =>
                        val scrutAsI31 = ref.cast(getScrutExpr, RefType.i31ref)
                        val scrutValue = i31.get(scrutAsI31, signed = true)
                        i32.eq(scrutValue, withValidIntLit(value, lit.toLoc)(i32.const))
                      case UnitLit(true) => ref.is_null(getScrutExpr)
                      case _ =>
                        break(errExpr(Ls(msg"Pattern matching for unit literals not implemented yet" -> lit.toLoc)))

                    S(`if`(
                      condition = testExpr,
                      ifTrue = ifTrue,
                      ifFalse = N,
                      resultTypes = Seq.empty,
                    ))

                  case Case.Cls(cls, _) =>
                    val isStructCompatible = ref.test(getScrutExpr, baseObjectRefType(nullable = false))
                    def isArrayCompatible = ref.test(getScrutExpr, RefType(HeapType.Array, nullable = false))

                    if cls eq ctx.elabCtx.builtins.Object then
                      // All `Object`s are emitted as a struct that extends `$Object` - A simple `ref.test` against
                      // `$Object` struct is enough. `Tuple` is a special case - it is emitted as a `(ref array)`, so we
                      // also check against that.
                      S(`if`(
                        condition = i32.or(isStructCompatible, isArrayCompatible),
                        ifTrue = ifTrue,
                        ifFalse = N,
                        resultTypes = Seq.empty,
                      ))
                    else if cls eq ctx.elabCtx.builtins.Array then
                      // Arrays are just `(ref array)`.
                      S(`if`(
                        condition = isArrayCompatible,
                        ifTrue = ifTrue,
                        ifFalse = N,
                        resultTypes = Seq.empty,
                      ))
                    else if isBoxedAsI31(cls, ctx) then
                      // `Int`, `Int31`, and `Bool` are all boxed `i31ref`s.
                      //
                      // TODO(Derppening): Ideally we should be able to tell `Int` and `Bool` apart at runtime, but
                      //                   could we do so without introducing another (struct) type?
                      S(`if`(
                        condition = ref.test(getScrutExpr, RefType.i31ref),
                        ifTrue = ifTrue,
                        ifFalse = N,
                        resultTypes = Seq.empty,
                      ))
                    else
                      val scrutRtti = readObjectTypeInfo(getScrutExpr)
                      // Every other class is matched by walking the scrutinee's RTTI chain, which needs the
                      // target's `typeinfo` global - registered only for classes with a Wasm struct
                      // representation.
                      val targetRtti = getClassTypeInfoGlobal(baseTypeSymbol(cls)) getOrElse:
                        break(errExpr(
                          Ls(msg"Pattern matching against class `${cls.nme}`, which has no Wasm " +
                            msg"runtime type information, is not implemented yet" -> scrut.toLoc),
                          extraInfo = S(s"no `typeinfo` global is registered for `${cls}`"),
                        ))
                      val classMatchExpr = isSubtypeByTypeInfo(scrutRtti, targetRtti)

                      S(`if`(
                        condition = isStructCompatible,
                        ifTrue = `if`(
                          condition = classMatchExpr,
                          ifTrue = ifTrue,
                          ifFalse = N,
                          resultTypes = Seq.empty,
                        ),
                        ifFalse = N,
                        resultTypes = Seq.empty,
                      ))
                    end if
                  case Case.Tup(len, inf) =>
                    val arrayRefType = RefType(HeapType.Array, nullable = true)
                    val isArrayTest = ref.test(getScrutExpr, arrayRefType)

                    // Length check
                    val scrutArray = ref.cast(getScrutExpr, arrayRefType)
                    val arrayLength = array.len(scrutArray)
                    val lengthTest = if inf then
                      i32.ge_u(arrayLength, i32.const(len))
                    else
                      i32.eq(arrayLength, i32.const(len))

                    val testExpr = i32.and(isArrayTest, lengthTest)
                    S(`if`(
                      condition = testExpr,
                      ifTrue = ifTrue,
                      ifFalse = N,
                      resultTypes = Seq.empty,
                    ))
                  case _ =>
                    break(errExpr(
                      Ls(
                        msg"WatBuilder::returningTerm for Match(...) with case `${cse.toString}` not implemented yet" ->
                          N,
                      ),
                      extraInfo = S(cse.toString),
                    ))
                end match

              val defaultExpr = asStatement(dflt.toVector.flatMap(returningTerm)).toVector

              // Generate the match block
              blockInstr(
                label = S(matchLabel),
                children = scrutInitExpr.toVector ++ armExprs ++ defaultExpr,
                resultTypes = Seq.empty,
              )

        matchBlock +: returningTerm(rst)

      // * Try/finally lowering is intentionally rejected for now: the previous implementation required `exnref` support
      // * which can only be enabled with the `--experimental-wasm-exnref` flag.
      // * Later, it will be implemented using intrinsic function.
      case TryBlock(sub, _, _) =>
        Vector(errExpr(
          Ls(msg"WatBuilder::returningTerm for TryBlock(...) not implemented yet" -> N),
          extraInfo = S(sub.showAsTree),
        ))

      case Throw(res, _) =>
        val excWat = result(res)
        Vector(`throw`(exnTagIdx, Seq(excWat)))

      case End(_) => Vector.empty
      case Unreachable(_) => Vector(unreachable)

      case t =>
        Vector(errExpr(
          Ls(msg"WatBuilder::returningTerm for ${t.getClass.getSimpleName} block not implemented yet" -> N),
          extraInfo = S(t.showAsTree),
        ))
    end match
  end returningTerm

  /** Reports the imports of `p` that are not source imports, which the Wasm backend does not support. */
  private def checkImports(p: Program, wd: io.Path)(using Raise): Unit =
    for imprt <- p.imports if !linking.sourceImports.contains(imprt._1) do
      val displayPath = if imprt._2.startsWith("/") then
        io.Path(imprt._2).relativeTo(wd).fold(imprt._2)(_.toString)
      else imprt._2
      raise(
        ErrorReport(
          msg"Import of symbol `$displayPath` not implemented yet" -> imprt._1.toLoc :: Nil,
          extraInfo = S(imprt),
          source = Diagnostic.Source.Compilation,
        ),
      )

  private def compiledModule(entryName: Str, exprt: Opt[BlockMemberSymbol])(using Raise): CompiledWasmFile =
    def systemMemMinPages: Int =
      ctx.getMemoryImport(
        ExternIntrinsics.SystemModule,
        ExternIntrinsics.SystemMemoryImportName,
      ).fold(0)(_.memType.lim.min)

    val interface = ctx.fileInterface(fileClasses,
      namespaces.valuesIterator.filter(ns => localNamespaces(ns.module)).toVector, exprt)
    CompiledWasmFile(CompiledWasmModule(ctx.toWat, entryName, systemMemMinPages), interface)

  /** The common headers used by source-class layouts and the runtime's intrinsic Unit layout. */
  private def initializeObjectTypes()(using Raise): Unit =
    ctx.addType(TypeInfo(
      sym = typeInfoBaseSym,
      compType = StructType(Seq(
        tagFieldSym -> Field(I32Type, mutable = false, id = "tag"),
        parentFieldSym -> Field(
          RefType(TypeIdx(SymIdx("TypeInfoBase")), nullable = true),
          mutable = false,
          id = "parent",
        ),
      )),
      objectTag = N,
    ))

    ctx.addType(TypeInfo(
      sym = baseObjectSym,
      compType = StructType(Seq(
        typeInfoFieldSym -> Field(RefType(typeInfoBaseTypeIdx, nullable = false), mutable = true, id = "typeinfo"),
      )),
      objectTag = S(ctx.getFreshObjectTag() ensuring (_ == 0)),
    ))
    ()

  /** File and runtime entries share a zero-argument, single-result calling convention. */
  private def entryFunction(body: Vector[Expr], frame: FunctionCtx, resultType: ValType)(using Raise): FuncInfo =
    val sym = BlockMemberSymbol("entry", Nil)
    val results = Vector(Result(resultType))
    val ty = ctx.addType(TypeInfo(
      sym = TempSymbol(N, initErasedType = N, sym.nme),
      FunctionType(params = Vector.empty, results = results),
      objectTag = N,
    ))
    FuncInfo(
      sym = sym,
      typeUse = TypeUse(ty),
      params = Vector.empty,
      resultTypes = results,
      locals = frame.locals,
      body = body,
      optionalParams = Set.empty,
    )

  private def program(
      p: Program,
      exprt: Opt[BlockMemberSymbol],
      preserved: Set[ScopedSymbol],
  )(using Raise): CompiledWasmFile =
    initializeObjectTypes()

    linking.imports.foreach: dep =>
      val (relocate, globals) = ctx.importFile(dep)
      dep.interface.classes.foreach: cls =>
        typeInfoTypeIdxs(cls.sym) = () => relocate.index(cls.rttiType)
        typeInfoGlobals(cls.sym) = () => globals(cls.rttiGlobal)
        initFuncSyms(cls.sym) = cls.initializer
        ctx.registerVirtualTable(cls.sym, cls.virtualTable.copy(slots = cls.virtualTable.slots.map(slot =>
          slot.copy(paramTypes = slot.paramTypes.map(relocate.value), resultType = relocate.value(slot.resultType)))))
        (cls.sym, cls.singleton) match
          case (obj: ModuleOrObjectSymbol, S((index, ty))) =>
            lazy val info =
              val GlobalIdx(SymIdx(name)) = globals(index).runtimeChecked
              SingletonInfo(name, relocate.reference(ty))
            ctx.registerSingleton(obj, info)
          case (_, S(_)) => lastWords(s"Imported singleton `${cls.sym.nme}` is not an object")
          case (_, N) => ()
      dep.interface.namespaces.foreach(registerNamespace)
    predeclareFileMembers(p.main)

    boundary[CompiledWasmFile]:
      val outerRaise = summon[Raise]

      // Early registration scheme: collect supported top-level classes from main block,
      // order by inheritance, predeclare struct types, init functions, and constructors.
      locally:
        given Raise = diag =>
          outerRaise(diag)
          diag match
            case _: ErrorReport => break(compiledModule("entry", exprt))
            case _ => ()
        val (classes, funs) = collectTopLevelDefns(p.main)
        val sortedClasses = sortTopLevelClasses(classes)
        // Class identities come first, so that layouts and signatures resolve self- and forward references to
        // the class's own type rather than to `anyref`.
        sortedClasses.foreach(allocateClassTypeIdentity)
        sortedClasses.foreach(predeclareClass)
        // Top-level functions are predeclared here too, so that a call can be compiled before the
        // definition it refers to. Functions do not need to be ordered.
        // Note that classes must come first, since the types of parameters and return values may
        // refer to declared class types.
        funs.foreach: fd =>
          if fd.params.size != 1 then
            raise(ErrorReport(Ls(msg"WASM functions require exactly one parameter list" -> fd.sym.toLoc),
              source = Diagnostic.Source.Compilation))
          predeclareTopLevelFun(fd.sym, fd.dSym, fd.params.head)
        // Slot types may mention classes from this module. Resolve them only after all
        // class identities and layouts are available, just like function signatures.
        collectPreservedBindings(p.main, preserved).toVector.sortBy(_.uid).foreach(registerGlobal)
        namespaces.valuesIterator.filter(ns => localNamespaces(ns.module)).foreach: ns =>
          ns.storage.values.foreach(registerGlobal)

      // Compile the entry function under a dedicated local scope so that any temp locals introduced
      // during codegen (e.g., via `local.tee`) are declared in the entry function.
      val entryType = ctx.elabCtx.givenIn(Block.returnType(p.main).map(_.canonicalize))
      // A bottom-typed entry still exports an anyref result. Give returns that slot before lowering their
      // operands, which can have another representation underneath a cast to Nothing.
      val entrySlot = entryType match
        case S(ErasedType.Nothing) => S(RefType.anyref)
        case _ => entryType.flatMap(_.wasmType)
      val (entryBody, entryFnCtx) = genFuncBody(Nil, thisSym = N, resultType = entrySlot, loc = N):
        functionBody(p.main)

      val entryResultType = entryType.flatMap(_.wasmType).getOrElse(RefType.anyref)

      val entryFnExpr = ctx.elabCtx.givenIn:
        entryType match
          case S(ErasedType.Incompatible(lhs, rhs)) =>
            Vector(errExpr(
              Ls(msg"Wasm entry function has incompatible result types `${lhs.describe}` and `${rhs.describe}`" -> N),
              extraInfo = S(entryBody.map(_.toWat.mkString()).mkString("\n")),
            ))
          // A block with no returns places no constraint on the entry function's single-result signature.
          case _ => entryBody
      val entryFnInfo = entryFunction(entryFnExpr, entryFnCtx, entryResultType)

      if stringLits.nonEmpty then
        stringLits.foreach: (s, lit) =>
          if lit.byteLen > 0 then
            ctx.addDataSegment(DataSegment.Active(
              offset = i32.const(lit.offset),
              bytes = Seq(lit.watBytes),
              memuse = N,
              sym = TempSymbol(
                N,
                initErasedType = S(ErasedType.Str),
                s.take(WatBuilder.StringConstantIdentMaxLength),
              ),
            ))

      ctx.addFunc(entryFnInfo)

      compiledModule(entryFnInfo.exportName, exprt)
  end program

  def blockPreamble(ss: Iterable[ScopedSymbol])(using FunctionCtx, Raise): Unit =
    ss.toVector.sortBy(_.uid).filter: sym =>
      !ctx.containsGlobal(sym)
    .foreach: sym =>
      funcCtx.addLocal(sym)

  def nonNestedScoped(
      blk: Block,
  )(k: Block => Vector[Expr])(using FunctionCtx, Raise): Vector[Expr] = blk match
    case Scoped(syms, body) =>
      blockPreamble(syms.view.filter(body.freeVars))
      k(body)
    case _ => k(blk)

  def block(t: Block)(using FunctionCtx, Raise): Vector[Expr] =
    nonNestedScoped(t)(returningTerm)

  /** Compiles a function's IR body to Wasm instructions and returns the context that records its parameters and locals.
    * `paramTypes` describes the registered function signature's parameter slots, including the shared virtual signature
    * for an override; [[FunctionCtx]] defines the fallback when it is absent.
    */
  def setupFunction(
      thisSym: Opt[InnerSymbol],
      params: LoweredParamList,
      body: Block,
      resultType: Opt[ValType],
      loc: Opt[Loc],
      paramTypes: Opt[Seq[ValType]] = N,
  )(using Raise): (Seq[Expr], FunctionCtx) =
    genFuncBody(params :: Nil, thisSym = thisSym, resultType = resultType, loc = loc, paramTypes = paramTypes):
      functionBody(body)

end WatBuilder
