package hkmc2
package codegen
package wasm
package text

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import document.*
import document.Document
import semantics.{
  BlockMemberSymbol, Elaborator, InnerSymbol, LabelSymbol, ModuleOrObjectSymbol, ParamList, Symbol, TempSymbol,
},
  Elaborator.State
import text.Param as WasmParam
import Instructions.*

import scala.collection.immutable.ListMap
import scala.collection.mutable.{ArrayBuffer as ArrayBuf, Map as MutMap}
import scala.reflect.ClassTag

/** Metadata for a REPL binding that can be imported by later Wasm modules. */
sealed trait SessionBinding:
  /** Returns the deduplication key for this binding. */
  def bindingKey: Str

  /** Returns the symbols that should resolve to this binding. */
  def bindingSyms: Seq[Local]

  /** Returns the export name if this binding is re-exported. */
  def exportNameOpt: Opt[Str] = N

object SessionBinding:
  val ReplModuleName: Str = "repl"

/** Metadata for an exported function that later Wasm REPL modules can import.
  *
  * @param sym
  *   The source symbol associated with the exported function.
  * @param moduleName
  *   The Wasm module name used by the import.
  * @param exportName
  *   The exported function name within `moduleName`.
  * @param funcType
  *   The Wasm function type expected by the import.
  */
final case class SessionFunc(
    sym: BlockMemberSymbol,
    wrapId: Opt[Str] -> Opt[Str],
    moduleName: Str,
    exportName: Str,
    funcType: FunctionType,
) extends SessionBinding:
  def bindingKey: Str = s"func:$moduleName:$exportName"
  def bindingSyms: Seq[Local] = sym :: Nil
  override def exportNameOpt: Opt[Str] = S(exportName)

/** Metadata for an exported global that later Wasm REPL modules can import.
  *
  * @param sym
  *   The source symbol associated with the exported global.
  * @param moduleName
  *   The Wasm module name used by the import.
  * @param exportName
  *   The exported global name within `moduleName`.
  * @param globalType
  *   The Wasm global type expected by the import.
  */
final case class SessionGlobal(
    sym: Symbol,
    wrapId: Opt[Str] -> Opt[Str],
    moduleName: Str,
    exportName: Str,
    globalType: GlobalType,
) extends SessionBinding:
  def bindingKey: Str = s"global:$moduleName:$exportName"
  def bindingSyms: Seq[Local] = sym :: Nil
  override def exportNameOpt: Opt[Str] = S(exportName)

/** Metadata for a class type made visible to later Wasm REPL modules.
  *
  * @param sym
  *   The block member symbol of the class.
  * @param wrapId
  *   Identifier wrapping metadata for recreating the class type in importing modules.
  * @param compType
  *   The class composite type that must be recreated in importing modules.
  * @param objectTag
  *   The runtime object tag assigned to the class type.
  * @param rttiTypeInfo
  *   The RTTI struct type information that must be recreated in importing modules.
  * @param rttiGlobalExportName
  *   The export name of the per-class RTTI global to import from prior REPL modules.
  * @param aliasSyms
  *   Additional symbols that should resolve to this class binding.
  */
final case class SessionClass(
    sym: BlockMemberSymbol,
    wrapId: Opt[Str] -> Opt[Str],
    compType: CompType,
    objectTag: Opt[Int],
    rttiTypeInfo: TypeInfo,
    rttiGlobalExportName: Str,
    aliasSyms: Seq[Local] = Nil,
) extends SessionBinding:
  def bindingKey: Str = s"class:${sym.uid}"
  def bindingSyms: Seq[Local] = sym +: aliasSyms
  override def exportNameOpt: Opt[Str] = S(rttiGlobalExportName)

/** Metadata for a singleton object's backing global made visible to later Wasm REPL modules.
  *
  * @param blockSym
  *   The block member symbol of the singleton object.
  * @param objectSym
  *   Optional object/module symbol that should also resolve to this singleton binding.
  * @param moduleName
  *   The Wasm module name used by the import.
  * @param exportName
  *   The exported global name within `moduleName`.
  * @param globalTy
  *   The Wasm reference type of the singleton backing global.
  */
final case class SessionSingleton(
    blockSym: BlockMemberSymbol,
    objectSym: Opt[ModuleOrObjectSymbol],
    wrapId: Opt[Str] -> Opt[Str],
    moduleName: Str,
    exportName: Str,
    globalTy: RefType,
) extends SessionBinding:
  def bindingKey: Str = s"singleton:$moduleName:$exportName"
  def bindingSyms: Seq[Local] = blockSym +: objectSym.toSeq
  override def exportNameOpt: Opt[Str] = S(exportName)

/** The emitted Wasm module together with REPL/session export metadata.
  *
  * @param wat
  *   The generated WAT for the module.
  * @param entryName
  *   The name of the module entry function.
  * @param systemMemMinPages
  *   The minimum number of imported system-memory pages required by the module.
  * @param sessionExports
  *   Session bindings exported by this module for use by later REPL blocks.
  */
final case class CompiledWasmModule(
    wat: Document,
    entryName: Str,
    systemMemMinPages: Int,
    sessionExports: Seq[SessionBinding],
)

/** Context used while collecting REPL/session exports for a single Wasm module.
  *
  * @param symbolsToExport
  *   The symbols from the current module that should be recorded as session exports.
  * @param collectedBindings
  *   The session bindings accumulated while compiling the current module.
  */
final class SessionExportCtx(
    val symbolsToExport: Set[Local],
    val collectedBindings: ArrayBuf[SessionBinding],
):
  def shouldExport(sym: Local): Bool = symbolsToExport(sym)

  def emit(binding: SessionBinding): Unit =
    collectedBindings += binding

  def freshCollector(): SessionExportCtx =
    SessionExportCtx(symbolsToExport, ArrayBuf.empty)

/** A Wasm function and its associated information.
  *
  * Each instance of [[FuncInfo]] represents a single function definition in a WebAssembly module.
  *
  * @param sym
  *   The source [[Symbol]] which this function is generated from.
  * @param wrapId
  *   An pair of optional strings for adding a prefix and suffix to the generated identifier of this function.
  * @param typeUse
  *   [[TypeUse]] of the function's type in the module's type section.
  * @param params
  *   [[Seq]] of parameter local variables and their names.
  * @param resultTypes
  *   The result types of the function.
  * @param locals
  *   [[Seq]] of local variables (excluding parameters) and their names.
  * @param body
  *   The expression of the function body.
  * @param exportName
  *   Optional export name.
  */
class FuncInfo(
    val sym: BlockMemberSymbol | TempSymbol,
    val typeUse: TypeUse,
    val params: Seq[Local -> SymIdx],
    val resultTypes: Seq[Result],
    val locals: Seq[Local -> SymIdx],
    val body: Expr,
    val exportName: Opt[Str],
    val wrapId: Opt[Str] -> Opt[Str] = N -> N,
)(using Ctx, Raise) extends ToWat:

  /** Symbolic identifier for the function. */
  val id = SymIdx(summon[Ctx].funcScp.allocateOrGetNameWrapped(sym, wrapId))

  /** Returns the type of this function as a [[SignatureType]]. */
  def getSignatureType: SignatureType = SignatureType(
    params = params.map((_, paramIdx) => WasmParam(paramIdx, RefType.anyref)),
    results = resultTypes,
  )

  def toWat: Document =
    doc"""(func ${id.toWat}${
        exportName.fold(doc""): e =>
          doc""" (export "$e")"""
      } ${typeUse.toWat}${
        getSignatureType.toWat.surroundUnlessEmpty(doc" ")
      } #{ ${
        locals.map: p =>
          doc"(local ${p._2.toWat} ${RefType.anyref.toWat})"
        .mkDocument(doc" # ").surroundUnlessEmpty(doc" # ")
      } # ${body.toWat} #} )"""
end FuncInfo

/** A Wasm global and its associated information.
  *
  * Each instance of [[GlobalInfo]] represents a single global definition in a WebAssembly module.
  *
  * @param globalType
  *   The type of the global.
  * @param init
  *   The initializer expression for the global.
  * @param exportName
  *   Optional export name.
  * @param sym
  *   The source [[Symbol]] which this global is generated from.
  * @param wrapId
  *   An pair of optional strings for adding a prefix and suffix to the generated identifier of this global.
  */
class GlobalInfo(
    val globalType: GlobalType,
    val init: Expr,
    val exportName: Opt[Str],
    val sym: Symbol,
    val wrapId: Opt[Str] -> Opt[Str] = N -> N,
)(using Ctx, Raise) extends ToWat:

  /** Symbolic identifier for the global. */
  val id: SymIdx = SymIdx(summon[Ctx].globalScp.allocateOrGetNameWrapped(sym, wrapId))

  def toWat: Document =
    doc"""(global ${id.toWat}${
        exportName.fold(doc""): name =>
          doc""" (export "$name")"""
      } ${globalType.toWat} ${init.toWat})"""
end GlobalInfo

/** A WebAssembly memory and its associated information.
  *
  * Each instance of [[MemInfo]] represents a single memory definition in a WebAssembly module.
  *
  * @param sym
  *   The source [[TempSymbol]] which this memory is generated from.
  * @param memType
  *   The type of the memory.
  * @param wrapId
  *   An pair of optional strings for adding a prefix and suffix to the generated identifier of this memory.
  */
class MemInfo(val sym: TempSymbol, val memType: MemType, val wrapId: Opt[Str] -> Opt[Str] = N -> N)(using Ctx, Raise)
    extends ToWat:

  /** Symbolic identifier for the global. */
  val id: SymIdx = SymIdx(summon[Ctx].memoryScp.allocateOrGetNameWrapped(sym, wrapId))

  def toWat: Document = doc"(memory ${id.toWat} ${memType.toWat})"
end MemInfo

/** A Wasm type and its associated information.
  *
  * Each instance of [[TypeInfo]] represents a single type definition in a WebAssembly module.
  *
  * @param sym
  *   The source [[Symbol]] which this type is generated from.
  * @param wrapId
  *   An pair of optional strings for adding a prefix and suffix to the generated identifier of this type.
  * @param compType
  *   The composite type this type definition represents.
  * @param objectTag
  *   An optional object tag number associated with this type.
  */
final class TypeInfo(
    val sym: BlockMemberSymbol | TempSymbol,
    val compType: CompType,
    val objectTag: Opt[Int],
    val wrapId: Opt[Str] -> Opt[Str] = N -> N,
)(using Ctx, Raise) extends ToWat:

  /** Symbolic identifier for the type. */
  val id = SymIdx(summon[Ctx].typeScp.allocateOrGetNameWrapped(sym, wrapId))

  def toWat: Document = doc"(type ${id.toWat} ${compType.toWat})"

/** A WebAssembly exception tag declaration.
  *
  * In Wasm, a `tag` names an exception kind and points to a function type that describes the payload values carried by
  * `throw tag ...` and extracted by matching `catch tag ...`.
  *
  * @param typeUse
  *   The function type referenced by this tag.
  * @param sym
  *   The source [[Symbol]] which this tag is generated from.
  */
class TagInfo(val typeUse: TypeUse, val sym: Symbol, val wrapId: Opt[Str] -> Opt[Str] = N -> N)(using Ctx, Raise)
    extends ToWat:

  /** Symbolic identifier for the tag. */
  val id: SymIdx = SymIdx(summon[Ctx].tagScp.allocateOrGetNameWrapped(sym, wrapId))

  def toWat: Document =
    doc"""(tag ${id.toWat} (export "${id.id}") ${typeUse.toWat})"""
end TagInfo

enum WasmIntrinsicType:
  case TupleArray(mutable: Bool)
  /** Shared erased Wasm function type for virtual methods with the given arity, including `this`. */
  case VirtualMethod(arity: Int)

/** Class containing identifiers of labels to jump to when breaking or continuing from a control flow structure.
  *
  * @param breakLabel
  *   The identifier of the label to jump to for exiting the control flow structure, e.g. for `break` statements.
  * @param continueLabel
  *   The identifier of the label to jump to for continuing the control flow structure, e.g. for `continue` statements
  *   in loops. This is `None` for non-loop control flow structures.
  */
case class LabelTarget(breakLabel: Str, continueLabel: Opt[Str])

object FunctionCtx:

  def funcCtx(using funcCtx: FunctionCtx): FunctionCtx = funcCtx

  /** Context for tracking control flow jump targets.
    *
    * @param scp
    *   [[Scope]] for generating WAT identifiers of labels in this control flow context.
    * @param breakLabel
    *   The label to jump to for exiting this control flow context, e.g. for `break` statements.
    * @param continueLabel
    *   The label to jump to for continuing this control flow context, e.g. for `continue` statements in loops. This is
    *   `None` for non-loop contexts.
    */
  private case class ControlFlowCtx(scp: Scope, breakLabel: LabelSymbol, continueLabel: Opt[LabelSymbol])

/** Context associated with codegen for a Wasm function.
  *
  * @param _params
  *   The parameters of this function.
  * @param thisSym
  *   The implicit `this` parameter symbol if this function is generated from a non-static method, or `N` otherwise.
  */
class FunctionCtx(_params: Ls[ParamList], thisSym: Opt[InnerSymbol])(using Raise, State):

  /** [[Scope]] for generating WAT identifiers of locals. */
  private[text] val localScp = Scope.empty(Scope.Cfg.default)

  /** The parameter of this function, represented by a tuple of the symbol representing the parameter and its symbolic
    * identifier.
    */
  val params: Seq[Local -> SymIdx] =
    if _params.length > 1 then
      lastWords("Multiple parameter lists are not yet supported")
    val thisParam = thisSym.map: dis =>
      dis -> SymIdx(localScp.addToBindings(dis, "this", shadow = false))
    thisParam.toSeq ++ _params.flatMap(_.paramSyms).map(p => p -> SymIdx(localScp.allocateName(p)))
  private val _locals = ArrayBuf.empty[Local]
  private var labels = ListMap.empty[LabelSymbol, FunctionCtx.ControlFlowCtx]

  /** Adds a Wasm local into this context.
    *
    * @param customName
    *   An optional name for the local variable. If provided, the local will be emitted with the given name instead of
    *   an auto-generated one.
    */
  def addLocal(local: Local, customName: Opt[Str] = N): LocalIdx =
    customName match
      case S(name) => localScp.addToBindings(local, name, shadow = false)
      case N => localScp.allocateName(local)
    _locals += local
    LocalIdx(SymIdx(localScp.lookup_!(local, N)))

  /** Looks up the given `sym` in this function context, returning its [[LocalIdx]] if it exists. */
  def lookupLocal(sym: Local): Opt[LocalIdx] =
    localScp.lookup(sym).map(idx => LocalIdx(SymIdx(idx)))

  /** Similar to [[lookupLocal]], but throws an exception if `sym` is not in this context. */
  def lookupLocal_!(sym: Local, loc: Opt[Loc]): LocalIdx =
    LocalIdx(SymIdx(localScp.lookup_!(sym, loc)))

  /** The locals of this function, represented by a tuple of the symbol representing the parameter and its symbolic
    * identifier.
    */
  def locals: Seq[Local -> SymIdx] = _locals.map(l => l -> SymIdx(localScp.lookup_!(l, N))).toSeq

  /** Pushes a label target for the dynamic extent of `body` and pops it afterwards.
    *
    * The `body` function is given a [[LabelTarget]] containing the `break` and `continue` labels corresponding to
    * `label`.
    *
    * @param hasContinueLabel
    *   Indicates whether a `continue` label should be generated for this control flow context, e.g. for loops.
    */
  def withLabel[T](label: LabelSymbol, hasContinueLabel: Bool)(body: LabelTarget => T): T =
    val ctrlFlowCtx = FunctionCtx.ControlFlowCtx(
      scp = labels.lastOption.fold(Scope.empty(Scope.Cfg.default))(_._2.scp.nest),
      breakLabel = label,
      continueLabel = if hasContinueLabel then S(LabelSymbol(N, s"${label.nme}_cont")) else N,
    )
    labels += label -> ctrlFlowCtx
    val res = body:
      LabelTarget(
        breakLabel = ctrlFlowCtx.scp.allocateName(label),
        continueLabel = ctrlFlowCtx.continueLabel.map(cl => ctrlFlowCtx.scp.allocateName(cl)),
      )
    labels = labels.init
    res

  /** Looks up the nearest in-scope target for `label`. */
  def lookupLabel(label: LabelSymbol): Opt[LabelTarget] =
    labels.lastOption.flatMap: (_, ctrlFlowCtx) =>
      ctrlFlowCtx.scp.lookup(label).map: labelId =>
        LabelTarget(
          breakLabel = labelId,
          continueLabel = labels(label).continueLabel.map(cl => labels.last._2.scp.lookup_!(cl, N)),
        )
end FunctionCtx

/** Generates a function body, providing an instance of [[FunctionCtx]] for parameter and locals tracking.
  *
  * Returns the result of the `mkBody` function along with the [[FunctionCtx]].
  */
def genFuncBody[T](
    params: Ls[ParamList],
    thisSym: Opt[InnerSymbol],
)(mkBody: FunctionCtx ?=> T)(using Raise, State): T -> FunctionCtx =
  val funcCtx = FunctionCtx(params, thisSym)
  val result = mkBody(using funcCtx)
  result -> funcCtx

object Ctx:
  case class SingletonInfo(
      globalName: Str,
      globalTy: RefType,
  )

  /** Derived virtual-dispatch layout for one class.
    *
    * @param virtualMethods
    *   Slot-ordered method symbols, used when declaring and initializing RTTI slot fields.
    * @param virtualMethodSlots
    *   Reverse lookup from a resolved method symbol to its virtual slot index.
    */
  case class VirtualTable(
      virtualMethods: List[BlockMemberSymbol],
      virtualMethodSlots: Map[BlockMemberSymbol, Int],
  )

  val binaryOps: Map[Str, (Expr, Expr) => Expr] = Map(
    "plus_impl" -> i32.add,
    "minus_impl" -> i32.sub,
    "times_impl" -> i32.mul,
    "div_impl" -> i32.div_s,
    "mod_impl" -> i32.rem_s,
    "eq_impl" -> i32.eq,
    "neq_impl" -> i32.ne,
    "lt_impl" -> i32.lt_s,
    "le_impl" -> i32.le_s,
    "gt_impl" -> i32.gt_s,
    "ge_impl" -> i32.ge_s,
  )
  val unaryOps: Map[Str, Expr => Expr] = Map(
    "neg_impl" -> (value => i32.sub(i32.const(0), value)),
    "pos_impl" -> identity,
    "not_impl" -> i32.eqz,
  )
  val wasmIntrinsicArities: Map[Str, Int] = (binaryOps.keys.map(_ -> 2) ++ unaryOps.keys.map(_ -> 1)).toMap
  val wasmIntrinsicNameSet: Set[Str] = wasmIntrinsicArities.keySet

  def empty(using State): Ctx = Ctx()

  def ctx(using ctx: Ctx): Ctx = ctx

  extension (ref: CtxIdx | Symbol)
    private def prettyString: Str = ref match
      case idx: CtxIdx => s"type index `${idx.toWat.mkString()}`"
      case sym: Symbol => s"symbol `${sym.toString}`"
end Ctx

/** Context for [[WatBuilder]]. */
class Ctx(using State) extends ToWat:

  import Ctx.prettyString

  /** [[Scope]] for generating WAT identifiers of types. */
  private[text] val typeScp = Scope.empty(Scope.Cfg.default)

  /** [[ListMap]] containing all type definitions in the module mapped by their symbolic identifiers. */
  private var types = ListMap.empty[SymIdx, TypeInfo]

  /** [[MutMap]] containing type symbols mapped to their corresponding [[TypeInfo]] instance. */
  private val namedTypes = MutMap.empty[BlockMemberSymbol, TypeInfo]
  
  /** [[Scope]] for generating WAT identifiers of data segments. */
  private[text] val dataSegmentScp = Scope.empty(Scope.Cfg.default)

  /** [[ListMap]] containing all data segments in the module. */
  private var dataSegments = ListMap.empty[SymIdx, DataSegment]
  
  /** [[Scope]] for generating WAT identifiers of element segments. */
  private[text] val elemSegmentScp = Scope.empty(Scope.Cfg.default)

  /** [[ListMap]] containing all element segments in the module. */
  private var elemSegments = ListMap.empty[SymIdx, ElemSegment]

  /** [[Scope]] for generating WAT identifiers of functions. */
  private[text] val funcScp = Scope.empty(Scope.Cfg.default)

  /** [[ListMap]] containing all function definitions and imports in the module mapped by their symbolic identifiers. */
  private var funcs = ListMap.empty[SymIdx, FuncInfo | Import[ExternType.Func]]

  /** [[MutMap]] containing function symbols mapped to the corresponding [[FuncInfo]] or [[Import]] instance. */
  private val namedFuncs = MutMap.empty[Symbol, FuncInfo | Import[ExternType.Func]]

  /** [[Scope]] for generating WAT identifiers of memories. */
  private[text] val memoryScp = Scope.empty(Scope.Cfg.default)

  /** [[ListMap]] containing all memory definitions and imports in the module mapped by their symbolic identifiers. */
  private var memories = ListMap.empty[SymIdx, MemInfo | Import[ExternType.Mem]]
  
  /** [[Scope]] for generating WAT identifiers of tags. */
  private[text] val tagScp = Scope.empty(Scope.Cfg.default)

  /** [[ListMap]] containing all tag definitions in the module. */
  private var tags = ListMap.empty[SymIdx, TagInfo]

  /** [[Scope]] for generating WAT identifiers of globals. */
  private[text] val globalScp = Scope.empty(Scope.Cfg.default)

  /** [[ListMap]] containing all global definitions and imports in the module. */
  private var globals = ListMap.empty[SymIdx, GlobalInfo | Import[ExternType.Global]]

  /** [[MutMap]] containing global symbols mapped to their corresponding [[GlobalInfo]] or [[Import]] instance. */
  private val namedGlobals = MutMap.empty[Symbol, GlobalInfo | Import[ExternType.Global]]

  private var startFunc = N: Opt[FuncIdx]

  /** Counter for generating object tags. */
  private var objectTagNum = 0

  private val wasmIntrinsicFuncs = MutMap.empty[Str, FuncIdx]
  private val wasmIntrinsicTypes = MutMap.empty[WasmIntrinsicType, TypeIdx]
  private val wasmIntrinsicTags = MutMap.empty[Str, TagIdx]

  private val cachedMemoryImport = MutMap.empty[(Str, Str), SymIdx]
  private val cachedFunctionImports = MutMap.empty[(Str, Str), FuncIdx]
  private val cachedGlobalImports = MutMap.empty[(Str, Str), GlobalIdx]

  private val singletonByBms = MutMap.empty[BlockMemberSymbol, Ctx.SingletonInfo]
  private val singletonByIsym = MutMap.empty[ModuleOrObjectSymbol, Ctx.SingletonInfo]
  private val singletonInitActions = ArrayBuf.empty[Expr]
  private val virtualTables = MutMap.empty[BlockMemberSymbol, Ctx.VirtualTable]
  private def imports: Seq[Import[?]] =
    val importedFuncs = funcs.collect:
      case (_, imp: Import[ExternType.Func]) => imp
    val importedGlobals = globals.collect:
      case (_, imp: Import[ExternType.Global]) => imp
    val importedMems = memories.collect:
      case (_, imp: Import[ExternType.Mem]) => imp
    (importedFuncs ++ importedGlobals ++ importedMems).toSeq

  private def globalExternType(globalEntry: GlobalInfo | Import[ExternType.Global])(using
      Ctx,
      Raise,
  ): ExternType.Global =
    globalEntry match
      case globalInfo: GlobalInfo => ExternType.Global(globalInfo.globalType, globalInfo.sym)
      case globalImport: Import[ExternType.Global] => globalImport.externType

  /** Returns a new number to be used as an object tag. */
  def getFreshObjectTag(): Int =
    val tag = objectTagNum
    objectTagNum += 1
    tag

  /** Adds a type into this context. */
  def addType(typeInfo: TypeInfo): TypeIdx =
    val id = typeInfo.id
    types += (id -> typeInfo)
    typeInfo.sym match
      case bms: BlockMemberSymbol => namedTypes(bms) = typeInfo
      case _ =>
    TypeIdx(id)

  /** Returns the [[TypeIdx]] of the given `typeref`.
    */
  def getType(typeref: TypeIdx | BlockMemberSymbol): Opt[TypeIdx] = typeref match
    case typeidx: TypeIdx => S(typeidx)
    case sym: BlockMemberSymbol => getTypeInfo(typeref).map(ti => TypeIdx(ti.id))

  /** Same as [[getType]] but throws an exception when the `typeref` is not found. */
  def getType_!(typeref: TypeIdx | BlockMemberSymbol): TypeIdx =
    getType(typeref).getOrElse:
      lastWords(s"Missing type definition for ${typeref.prettyString}")

  /** Returns the [[TypeInfo]] instance associated with the given `typeref`. */
  def getTypeInfo(typeref: TypeIdx | BlockMemberSymbol): Opt[TypeInfo] = typeref match
    case TypeIdx(idx @ SymIdx(nme)) => types.get(idx)
    case sym: BlockMemberSymbol => namedTypes.get(sym)

  /** Same as [[getTypeInfo]] but throws an exception when the `typeref` is not found. */
  def getTypeInfo_!(typeref: TypeIdx | BlockMemberSymbol): TypeInfo =
    getTypeInfo(typeref).getOrElse:
      lastWords(s"Missing type definition for ${typeref.prettyString}")

  /** Records the derived virtual-dispatch layout for `sym`. */
  def registerVirtualTable(sym: BlockMemberSymbol, info: Ctx.VirtualTable): Unit =
    virtualTables(sym) = info

  /** Returns the derived virtual-dispatch layout for `sym`. */
  def getVirtualTable(sym: BlockMemberSymbol): Opt[Ctx.VirtualTable] =
    virtualTables.get(sym)

  /** Adds a function import into this context.
    *
    * Returns the function index in the global function index space.
    */
  def addFunctionImport(funcImport: Import[ExternType.Func]): FuncIdx =
    val id = funcImport.externType.id
    funcs = funcs + (id -> funcImport)
    namedFuncs(funcImport.externType.sym) = funcImport
    FuncIdx(id)

  /** Returns the cached function import for (`module`, `name`), creating it with `createImport` if needed.
    */
  def getOrCreateFunctionImport(
      module: Str,
      name: Str,
  )(createImport: => Import[ExternType.Func]): FuncIdx =
    cachedFunctionImports.getOrElseUpdate((module, name), addFunctionImport(createImport))

  /** Adds a global import into this context.
    *
    * Returns the global index in the global index space.
    */
  def addGlobalImport(globalImport: Import[ExternType.Global]): GlobalIdx =
    val id = globalImport.externType.id
    globals = globals + (id -> globalImport)
    namedGlobals(globalImport.externType.sym) = globalImport
    GlobalIdx(id)

  /** Returns the cached global import for (`module`, `name`), creating it with `createImport` if needed.
    */
  def getOrCreateGlobalImport(
      module: Str,
      name: Str,
  )(createImport: => Import[ExternType.Global]): GlobalIdx =
    cachedGlobalImports.getOrElseUpdate((module, name), addGlobalImport(createImport))

  /** Adds or updates a memory import. If the import already exists, its minimum pages are increased to at least
    * `minPages`.
    */
  def ensureMemoryImport(module: Str, name: Str, minPages: Int)(using Ctx, Raise): Unit =
    val key = module -> name
    cachedMemoryImport.get(key) match
      case S(idx) =>
        val existing = memories(idx) match
          case imp: Import[ExternType.Mem] => imp
          case _ => lastWords(
              s"Expected an existing memory import \"$module\".\"$name\" for `${idx.toWat}`, got a definition instead.",
            )
        val newMin = existing.externType.memType.lim.min max minPages
        if newMin > existing.externType.memType.lim.min then
          memories = memories +
            (idx -> Import(
              module,
              name,
              ExternType.Mem(
                MemType(existing.externType.memType.lim.copy(min = minPages)),
                sym = existing.externType.sym,
                wrapId = existing.externType.wrapId,
              ),
            ))
      case N =>
        val id = SymIdx(name)
        memories = memories +
          (id ->
            Import(module, name, ExternType.Mem(MemType(Limits(minPages)), sym = TempSymbol(N, name))))
        cachedMemoryImport(key) = SymIdx(name)
    end match
  end ensureMemoryImport

  /** Returns the memory import information for the given (`module`, `name`) tuple if present. */
  def getMemoryImport(module: Str, name: Str): Opt[ExternType.Mem] =
    memories.collectFirst:
      case (_, imp @ Import(`module`, `name`, mem: ExternType.Mem)) => mem

  /** Adds a data segment into this context. */
  def addDataSegment(seg: DataSegment): Unit =
    dataSegments = dataSegments + (seg.id -> seg)

  /** Adds a tag into this context. */
  def addTag(tagInfo: TagInfo): TagIdx =
    val id = tagInfo.id
    tags = tags + (id -> tagInfo)
    TagIdx(id)

  /** Adds a function into this context. */
  def addFunc(funcInfo: FuncInfo)(using Ctx, Raise): FuncIdx =
    val id = funcInfo.id
    funcs = funcs + (id -> funcInfo)
    funcInfo.sym match
      case bms: BlockMemberSymbol => namedFuncs(bms) = funcInfo
      case _ =>
    val idx = FuncIdx(funcInfo.id)
    val refType = RefType(funcInfo.typeUse.typeIdx, nullable = false)
    elemSegments = elemSegments +
      (id -> ElemSegment.Declare(refType -> Seq(ref.func(idx, refType)), funcInfo.sym, funcInfo.wrapId))
    idx

  /** Returns the [[FuncIdx]] of the given `funcref`.
    */
  def getFunc(funcref: FuncIdx | Symbol): Opt[FuncIdx] = funcref match
    case funcidx: FuncIdx => S(funcidx)
    case sym: Symbol =>
      namedFuncs.get(sym).map: funcInfo =>
        funcInfo match
          case fi: FuncInfo => FuncIdx(fi.id)
          case imp: Import[ExternType.Func] => FuncIdx(imp.externType.id)

  /** Same as [[getFunc]] but throws an exception when the `funcref` is not found. */
  def getFunc_!(funcref: FuncIdx | Symbol): FuncIdx =
    getFunc(funcref).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  private def getFuncEntry(funcref: FuncIdx | Symbol): Opt[FuncInfo | Import[ExternType.Func]] = funcref match
    case FuncIdx(idx @ SymIdx(_)) => funcs.get(idx)
    case funcref: Symbol => namedFuncs.get(funcref)

  /** Returns the [[FuncInfo]] instance associated with the given `funcref`. */
  def getFuncInfo(funcref: FuncIdx | Symbol): Opt[FuncInfo] =
    getFuncEntry(funcref).collect:
      case funcInfo: FuncInfo => funcInfo

  /** Same as [[getFuncInfo]] but throws an exception when the `funcref` is not found. */
  def getFuncInfo_!(funcref: FuncIdx | Symbol): FuncInfo =
    getFuncInfo(funcref).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  /** Returns the type use associated with the given `funcref`, whether it is a definition or an import. */
  def getFuncTypeUse(funcref: FuncIdx | Symbol): Opt[TypeUse] =
    getFuncEntry(funcref).map:
      case funcInfo: FuncInfo => funcInfo.typeUse
      case funcImport: Import[ExternType.Func] => funcImport.externType.typeUse

  /** Same as [[getFuncTypeUse]] but throws an exception when the `funcref` is not found. */
  def getFuncTypeUse_!(funcref: FuncIdx | Symbol): TypeUse =
    getFuncTypeUse(funcref).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  /** Returns the [[GlobalIdx]] of the given `globalref`. */
  def getGlobal(globalref: GlobalIdx | Symbol)(using Ctx, Raise): Opt[GlobalIdx] = globalref match
    case globalidx: GlobalIdx => S(globalidx)
    case sym: Symbol =>
      namedGlobals.get(sym).map: globalEntry =>
        GlobalIdx(globalExternType(globalEntry).id)

  /** Same as [[getGlobal]] but throws an exception when the `globalref` is not found. */
  def getGlobal_!(globalref: GlobalIdx | Symbol)(using Ctx, Raise): GlobalIdx =
    getGlobal(globalref).getOrElse:
      lastWords(s"Missing global definition for ${globalref.prettyString}")

  private def getGlobalEntry(globalref: GlobalIdx | Symbol): Opt[GlobalInfo | Import[ExternType.Global]] =
    globalref match
      case GlobalIdx(idx @ SymIdx(_)) => globals.get(idx)
      case sym: Symbol => namedGlobals.get(sym)

  /** Returns the global extern metadata associated with the given `globalref`. */
  def getGlobalType(globalref: GlobalIdx | Symbol)(using Ctx, Raise): Opt[ExternType.Global] =
    getGlobalEntry(globalref).map(globalExternType)

  /** Same as [[getGlobalType]] but throws an exception when the `globalref` is not found. */
  def getGlobalType_!(globalref: GlobalIdx | Symbol)(using Ctx, Raise): ExternType.Global =
    getGlobalType(globalref).getOrElse:
      lastWords(s"Missing global definition for ${globalref.prettyString}")

  /** Returns the [[GlobalInfo]] instance associated with the given `globalref` when it is a definition. */
  def getGlobalInfo(globalref: GlobalIdx | Symbol): Opt[GlobalInfo] =
    getGlobalEntry(globalref).collect:
      case globalInfo: GlobalInfo => globalInfo

  /** Same as [[getGlobalInfo]] but throws an exception when the `globalref` is not found. */
  def getGlobalInfo_!(globalref: GlobalIdx | Symbol): GlobalInfo =
    getGlobalInfo(globalref).getOrElse:
      lastWords(s"Missing global definition for ${globalref.prettyString}")

  /** Adds a new variable into the global variable scope. */
  def addGlobal(globalInfo: GlobalInfo): GlobalIdx =
    val id = globalInfo.id
    globals = globals + (id -> globalInfo)
    namedGlobals(globalInfo.sym) = globalInfo
    GlobalIdx(id)

  /** Adds a [[Seq]] of variables into the global variable scope. */
  def addGlobals(globalDefs: Seq[GlobalInfo]): Seq[GlobalIdx] =
    globalDefs.map(addGlobal)

  /** Checks whether the global variable scope contains the variable `sym`. */
  def containsGlobal(sym: Symbol): Bool = namedGlobals.contains(sym)
  
  /** Returns all globals in this context. */
  def getGlobals: Seq[Symbol] = namedGlobals.keys.toSeq

  /** Checks whether singleton metadata has been registered for class symbol `sym`. */
  def containsSingleton(sym: BlockMemberSymbol): Bool = singletonByBms.contains(sym)

  /** Returns singleton metadata for `sym` when it resolves to either the block-member symbol or module/object symbol
    * used during singleton registration.
    */
  def getSingletonInfo(sym: Local): Opt[Ctx.SingletonInfo] = sym match
    case bms: BlockMemberSymbol => singletonByBms.get(bms)
    case isym: ModuleOrObjectSymbol => singletonByIsym.get(isym)
    case _ => N

  /** Registers singleton metadata under both its block-member symbol and optional module/object symbol alias.
    */
  def registerSingleton(
      bms: BlockMemberSymbol,
      isym: Opt[ModuleOrObjectSymbol],
      info: Ctx.SingletonInfo,
  ): Unit =
    singletonByBms(bms) = info
    isym.foreach(singletonByIsym(_) = info)

  /** Appends one eager singleton initialization action for synthesized module start code. */
  def addSingletonInitAction(action: Expr): Unit =
    singletonInitActions += action

  /** Returns the singleton initialization actions in deterministic insertion order. */
  def getSingletonInitActions: Seq[Expr] = singletonInitActions.toSeq

  /** Configures the module start function. */
  def setStartFunc(funcIdx: FuncIdx): Unit =
    startFunc = S(funcIdx)

  /** Returns the cached [[FuncIdx]] for the intrinsic named `name`, creating it with `createIntrinsic` if it does not
    * yet exist in this context.
    */
  def getOrCreateWasmIntrinsic(name: Str, createIntrinsic: => FuncIdx): FuncIdx =
    wasmIntrinsicFuncs.getOrElseUpdate(name, createIntrinsic)

  /** Returns the cached [[TypeIdx]] for the intrinsic type `key`, creating it with `createType` if it does not yet
    * exist in this context.
    */
  def getOrCreateWasmIntrinsicType(key: WasmIntrinsicType)(createType: => TypeIdx): TypeIdx =
    wasmIntrinsicTypes.getOrElseUpdate(key, createType)

  /** Returns the cached [[TagIdx]] for the intrinsic tag named `name`, creating it if absent. */
  def getOrCreateWasmIntrinsicTag(name: Str, createTag: => TagIdx): TagIdx =
    wasmIntrinsicTags.getOrElseUpdate(name, createTag)

  def toWat: Document =
    val definedGlobals = globals.valuesIterator.collect:
      case globalInfo: GlobalInfo => globalInfo.toWat
    val memDefns = memories.valuesIterator.collect:
      case memInfo: MemInfo => memInfo.toWat
    val funcDefns = funcs.valuesIterator.collect:
      case funcInfo: FuncInfo => funcInfo.toWat
    doc"(module #{  # ${
        (
          types.valuesIterator.map(_.toWat)
            ++ imports.iterator.map(_.toWat)
            ++ tags.valuesIterator.map(_.toWat)
            ++ definedGlobals
            ++ memDefns
            ++ funcDefns
            ++ dataSegments.valuesIterator.map(_.toWat)
            ++ elemSegments.valuesIterator.map(_.toWat)
            ++ startFunc.iterator.map(funcIdx => doc"(start ${funcIdx.toWat})")
        ).toSeq.mkDocument(doc" # ")
      } #} )"
  end toWat

end Ctx
