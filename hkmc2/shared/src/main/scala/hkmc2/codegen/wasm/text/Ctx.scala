package hkmc2
package codegen
package wasm
package text

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import document.*
import document.Document
import semantics.{BlockMemberSymbol, Elaborator, LabelSymbol, ModuleOrObjectSymbol, Symbol, TempSymbol},
  Elaborator.State
import text.Param as WasmParam
import Instructions.*

import scala.annotation.{nowarn, targetName}
import scala.collection.immutable.ListMap
import scala.collection.mutable.{ArrayBuffer as ArrayBuf, Map as MutMap, LinkedHashSet}
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
    sym: Symbol,
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
  * @param typeInfo
  *   The Wasm type information that must be recreated in importing modules.
  * @param runtimeTags
  *   The class' runtime tag together with descendant class tags.
  * @param aliasSyms
  *   Additional symbols that should resolve to this class binding.
  */
final case class SessionClass(
    sym: BlockMemberSymbol,
    typeInfo: TypeInfo,
    runtimeTags: LinkedHashSet[Int],
    aliasSyms: Seq[Local] = Nil,
) extends SessionBinding:
  def bindingKey: Str = s"class:${sym.uid}"
  def bindingSyms: Seq[Local] = sym +: aliasSyms

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
end SessionExportCtx

object SessionExportCtx:
  def apply(
      symbolsToExport: Set[Local],
      collectedBindings: ArrayBuf[SessionBinding],
  ): SessionExportCtx =
    new SessionExportCtx(symbolsToExport, collectedBindings)

/** A Wasm function and its associated information.
  *
  * Each instance of [[FuncInfo]] represents a single function definition in a WebAssembly module.
  *
  * @param id
  *   Symbolic identifier for the function. If the function is anonymous, `id` should be generated from a fresh name
  *   allocated in the current scope.
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
    val id: SymIdx,
    val typeUse: TypeUse,
    params: Seq[Local -> Str],
    val resultTypes: Seq[Result],
    locals: Seq[Local -> Str],
    val body: Expr,
    val exportName: Opt[Str],
) extends ToWat:

  /** @param sym
    *   The source [[BlockMemberSymbol]] which this function is generated from.
    * @param typeIdx
    *   Index of the function's type in the module's type section.
    * @param params
    *   [[Seq]] of parameter local variables and their names.
    * @param nResults
    *   Number of results the function returns.
    * @param locals
    *   [[Seq]] of local variables (excluding parameters) and their names.
    * @param body
    *   The expression of the function body.
    */
  def this(
      sym: BlockMemberSymbol,
      typeUse: TypeUse,
      params: Seq[Local -> Str],
      nResults: Int,
      locals: Seq[Local -> Str],
      body: Expr,
  )(using Raise, Scope) = this(
    SymIdx(sym.optionIf(_.nameIsMeaningful).fold(summon[Scope].allocateName(sym))(_.nme)),
    typeUse,
    params,
    Seq.fill(nResults)(Result(RefType.anyref)),
    locals,
    body,
    sym.optionIf(_.nameIsMeaningful).map(_.nme),
  )

  def this(
      id: Opt[SymIdx],
      typeUse: TypeUse,
      params: Seq[Local -> Str],
      nResults: Int,
      locals: Seq[Local -> Str],
      body: Expr,
      `export`: Opt[Str],
  )(using Raise, Scope, State) = this(
    id.getOrElse(SymIdx(summon[Scope].allocateName(TempSymbol(N, "")))),
    typeUse,
    params,
    Seq.fill(nResults)(Result(RefType.anyref)),
    locals,
    body,
    `export`,
  )

  /** Returns the type of this function as a [[SignatureType]]. */
  def getSignatureType: SignatureType = SignatureType(
    params = params.map((_, varNme) => WasmParam(varNme, RefType.anyref)),
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
          doc"(local $$${p._2} ${RefType.anyref.toWat})"
        .mkDocument(doc" # ").surroundUnlessEmpty(doc" # ")
      } # ${body.toWat} #} )"""
end FuncInfo

/** A Wasm global and its associated information.
  *
  * Each instance of [[GlobalInfo]] represents a single global definition in a WebAssembly module.
  *
  * @param id
  *   Symbolic identifier for the global.
  * @param globalType
  *   The type of the global.
  * @param init
  *   The initializer expression for the global.
  * @param exportName
  *   Optional export name.
  */
class GlobalInfo(
    val id: SymIdx,
    val globalType: GlobalType,
    val init: Expr,
    val exportName: Opt[Str],
) extends ToWat:

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
  * @param id
  *   Symbolic identifier for the memory.
  * @param memType
  *   The type of the memory.
  */
class MemInfo(val id: SymIdx, val memType: MemType) extends ToWat:

  def toWat: Document = doc"(memory ${id.toWat} ${memType.toWat})"
end MemInfo

/** A Wasm type and its associated information.
  *
  * Each instance of [[TypeInfo]] represents a single type definition in a WebAssembly module.
  *
  * @param id
  *   Symbolic identifier for the type.
  * @param compType
  *   The composite type this type definition represents.
  * @param objectTag
  *   An optional object tag number associated with this type.
  */
class TypeInfo(val id: SymIdx, val compType: CompType, val objectTag: Opt[Int]) extends ToWat:

  /** @param sym
    *   The source [[BlockMemberSymbol]] which this type is generated from.
    * @param compType
    *   The composite type this type definition represents.
    */
  def this(sym: BlockMemberSymbol, compType: CompType, objectTag: Opt[Int])(using Raise, Scope) = this(
    SymIdx(sym.optionIf(_.nameIsMeaningful).fold(summon[Scope].allocateName(sym))(_.nme)),
    compType,
    objectTag,
  )

  def this(id: Opt[SymIdx], compType: CompType)(using Raise, Scope, State) =
    this(id.getOrElse(SymIdx(summon[Scope].allocateName(TempSymbol(N, "")))), compType, N)

  def toWat: Document = doc"(type ${id.toWat} ${compType.toWat})"

/** A WebAssembly exception tag declaration.
  *
  * In Wasm, a `tag` names an exception kind and points to a function type that describes the payload values carried by
  * `throw tag ...` and extracted by matching `catch tag ...`.
  *
  * @param id
  *   Symbolic identifier for the tag.
  * @param typeUse
  *   The function type referenced by this tag.
  */
class TagInfo(val id: SymIdx, val typeUse: TypeUse) extends ToWat:

  def toWat: Document =
    doc"""(tag ${id.toWat} (export "${id.id}") ${typeUse.toWat})"""
end TagInfo

enum WasmIntrinsicType:
  case TupleArray(mutable: Bool)

object Ctx:
  case class SingletonInfo(
      globalName: Str,
      globalTy: RefType,
  )

  case class LabelTarget(
      breakLabel: Str,
      continueLabel: Opt[Str],
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

  def empty: Ctx = Ctx()

  def ctx(using ctx: Ctx): Ctx = ctx

  extension (ref: CtxIdx | Symbol)
    private def prettyString: Str = ref match
      case idx: CtxIdx => s"type index `${idx.toWat.mkString()}`"
      case sym: Symbol => s"symbol `${sym.toString}`"
end Ctx

/** Context for [[WatBuilder]]. */
class Ctx extends ToWat:

  import Ctx.prettyString

  /** [[ListMap]] containing all type definitions in the module mapped by their symbolic identifiers. */
  private var types = ListMap.empty[SymIdx, TypeInfo]

  /** [[MutMap]] containing type symbols mapped to their corresponding [[TypeInfo]] instance. */
  private val namedTypes = MutMap.empty[BlockMemberSymbol, TypeInfo]

  /** [[ListMap]] containing all data segments in the module. */
  private var dataSegments = ListMap.empty[SymIdx, DataSegment]

  /** [[ListMap]] containing all element segments in the module. */
  private var elemSegments = ListMap.empty[SymIdx, ElemSegment]

  /** [[ListMap]] containing all function definitions and imports in the module mapped by their symbolic identifiers. */
  private var funcs = ListMap.empty[SymIdx, FuncInfo | Import[ExternType.Func]]

  /** [[MutMap]] containing function symbols mapped to the corresponding [[FuncInfo]] or [[Import]] instance. */
  private val namedFuncs = MutMap.empty[Symbol, FuncInfo | Import[ExternType.Func]]

  /** [[ListMap]] containing all memory definitions and imports in the module mapped by their symbolic identifiers. */
  private var memories = ListMap.empty[SymIdx, MemInfo | Import[ExternType.Mem]]

  /** [[ListMap]] containing all tag definitions in the module. */
  private var tags = ListMap.empty[SymIdx, TagInfo]

  /** [[ListMap]] containing all global definitions and imports in the module. */
  private var globals = ListMap.empty[SymIdx, GlobalInfo | Import[ExternType.Global]]

  /** [[MutMap]] containing global symbols mapped to their corresponding [[GlobalInfo]] or [[Import]] instance. */
  private val namedGlobals = MutMap.empty[Symbol, GlobalInfo | Import[ExternType.Global]]

  /** Stack of [[ListMap]] from local variable symbols to their symbolic indices within the current function scope. */
  private var locals = ListMap.empty[Local, SymIdx] :: Nil
  private var startFunc = N: Opt[FuncIdx]

  /** Counter for generating object tags. */
  private var objectTagNum = 0

  private val wasmIntrinsicFuncs = MutMap.empty[Str, FuncIdx]
  private val wasmIntrinsicTypes = MutMap.empty[WasmIntrinsicType, TypeIdx]
  private val wasmIntrinsicTags = MutMap.empty[Str, TagIdx]

  private val cachedMemoryImport = MutMap.empty[(Str, Str), SymIdx]
  private val cachedFunctionImports = MutMap.empty[(Str, Str), FuncIdx]
  private val cachedGlobalImports = MutMap.empty[(Str, Str), GlobalIdx]

  private var labelTargets = Nil: List[(LabelSymbol, Ctx.LabelTarget)]
  private val singletonByBms = MutMap.empty[BlockMemberSymbol, Ctx.SingletonInfo]
  private val singletonByIsym = MutMap.empty[ModuleOrObjectSymbol, Ctx.SingletonInfo]
  private val singletonInitActions = ArrayBuf.empty[Expr]
  private val runtimeClassTags = MutMap.empty[BlockMemberSymbol, LinkedHashSet[Int]]

  private def imports: Seq[Import[?]] =
    val importedFuncs = funcs.collect:
      case (_, imp: Import[ExternType.Func]) => imp
    val importedGlobals = globals.collect:
      case (_, imp: Import[ExternType.Global]) => imp
    val importedMems = memories.collect:
      case (_, imp: Import[ExternType.Mem]) => imp
    (importedFuncs ++ importedGlobals ++ importedMems).toSeq

  private def globalExternType(globalEntry: GlobalInfo | Import[ExternType.Global]): ExternType.Global =
    globalEntry match
      case globalInfo: GlobalInfo => ExternType.Global(globalInfo.id, globalInfo.globalType)
      case globalImport: Import[ExternType.Global] => globalImport.externType

  /** Pushes a label target for the dynamic extent of `body` and pops it afterwards. */
  def withLabel[T](label: LabelSymbol, target: Ctx.LabelTarget)(body: => T): T =
    labelTargets = (label, target) :: labelTargets
    val res = body
    labelTargets = labelTargets.tail
    res

  /** Looks up the nearest in-scope target for `label`. */
  def lookupLabel(label: LabelSymbol): Opt[Ctx.LabelTarget] =
    labelTargets.collectFirst:
      case (sym, target) if sym eq label => target

  /** Returns a new number to be used as an object tag. */
  def getFreshObjectTag(): Int =
    val tag = objectTagNum
    objectTagNum += 1
    tag

  /** Adds a type into this context. */
  def addType(sym: Opt[BlockMemberSymbol], typeInfo: TypeInfo): TypeIdx =
    val id = typeInfo.id
    types = types + (id -> typeInfo)
    sym.foreach:
      namedTypes(_) = typeInfo
    TypeIdx(id)

  @deprecated("Use the overload without `resolveSymIdx` instead.")
  def getType(typeref: TypeIdx | BlockMemberSymbol, resolveSymIdx: Bool): Opt[TypeIdx] =
    if resolveSymIdx then
      typeref match
        case TypeIdx(idx @ SymIdx(_)) =>
          types.zipWithIndex.collectFirst:
            case ((symIdx, _), i) if symIdx == idx => TypeIdx(NumIdx(i))
        case typeidx: TypeIdx => S(typeidx)
        case sym: BlockMemberSymbol =>
          namedTypes.get(sym).flatMap: typeInfo =>
            types.zipWithIndex.collectFirst:
              case ((_, ti), i) if ti === typeInfo => TypeIdx(NumIdx(i))
    else getType(typeref)

  /** Returns the [[TypeIdx]] of the given `typeref`.
    */
  def getType(typeref: TypeIdx | BlockMemberSymbol): Opt[TypeIdx] = typeref match
    case typeidx: TypeIdx => S(typeidx)
    case sym: BlockMemberSymbol => getTypeInfo(typeref).map(ti => TypeIdx(ti.id))

  @deprecated("Use the overload without `resolveSymIdx` instead.")
  def getType_!(typeref: TypeIdx | BlockMemberSymbol, resolveSymIdx: Bool): TypeIdx =
    getType(typeref, resolveSymIdx).getOrElse:
      lastWords(s"Missing type definition for ${typeref.prettyString}")

  /** Same as [[getType]] but throws an exception when the `typeref` is not found. */
  def getType_!(typeref: TypeIdx | BlockMemberSymbol): TypeIdx =
    getType(typeref).getOrElse:
      lastWords(s"Missing type definition for ${typeref.prettyString}")

  /** Returns the [[TypeInfo]] instance associated with the given `typeref`. */
  @nowarn("cat=deprecation")
  def getTypeInfo(typeref: TypeIdx | BlockMemberSymbol): Opt[TypeInfo] = typeref match
    case TypeIdx(NumIdx(idx)) => types.drop(idx).headOption.map(_._2)
    case TypeIdx(idx @ SymIdx(nme)) => types.get(idx)
    case sym: BlockMemberSymbol => namedTypes.get(sym)

  /** Same as [[getTypeInfo]] but throws an exception when the `typeref` is not found. */
  def getTypeInfo_!(typeref: TypeIdx | BlockMemberSymbol): TypeInfo =
    getTypeInfo(typeref).getOrElse:
      lastWords(s"Missing type definition for ${typeref.prettyString}")

  /** Records the class' runtime tag together with descendant class tags for `sym`. */
  def registerRuntimeClassTags(sym: BlockMemberSymbol, tags: LinkedHashSet[Int]): Unit =
    runtimeClassTags(sym) = tags

  /** Returns the class' runtime tag together with descendant class tags for `sym`. */
  def getAllRuntimeTags(sym: BlockMemberSymbol): Opt[LinkedHashSet[Int]] =
    runtimeClassTags.get(sym)

  @deprecated("Use the `Import[ExternType.Func]` overload instead.")
  def addFunctionImport(sym: Opt[Symbol], funcImport: FuncImport): FuncIdx =
    addFunctionImport(
      sym,
      Import(funcImport.module, funcImport.name, ExternType.Func(funcImport.id, TypeUse(funcImport.typeIdx))),
    )

  /** Adds a function import into this context.
    *
    * Returns the function index in the global function index space.
    */
  def addFunctionImport(sym: Opt[Symbol], funcImport: Import[ExternType.Func]): FuncIdx =
    val id = funcImport.externType.id
    funcs = funcs + (id -> funcImport)
    sym.foreach:
      namedFuncs(_) = funcImport
    FuncIdx(id)

  @deprecated("Use the `Import[ExternType.Func]` overload instead.")
  @targetName("getOrCreateFuncImport")
  def getOrCreateFunctionImport(
      module: Str,
      name: Str,
  )(createImport: => FuncImport): FuncIdx =
    cachedFunctionImports.getOrElseUpdate((module, name), addFunctionImport(N, createImport))

  /** Returns the cached function import for (`module`, `name`), creating it with `createImport` if needed.
    */
  def getOrCreateFunctionImport(
      module: Str,
      name: Str,
  )(createImport: => Import[ExternType.Func]): FuncIdx =
    cachedFunctionImports.getOrElseUpdate((module, name), addFunctionImport(N, createImport))

  /** Adds a global import into this context.
    *
    * Returns the global index in the global index space.
    */
  def addGlobalImport(sym: Opt[Symbol], globalImport: Import[ExternType.Global]): GlobalIdx =
    val id = globalImport.externType.id
    globals = globals + (id -> globalImport)
    sym.foreach:
      namedGlobals(_) = globalImport
    GlobalIdx(id)

  /** Returns the cached global import for (`module`, `name`), creating it with `createImport` if needed.
    */
  def getOrCreateGlobalImport(
      module: Str,
      name: Str,
  )(createImport: => Import[ExternType.Global]): GlobalIdx =
    cachedGlobalImports.getOrElseUpdate((module, name), addGlobalImport(N, createImport))

  /** Adds or updates a memory import. If the import already exists, its minimum pages are increased to at least
    * `minPages`.
    */
  def ensureMemoryImport(module: Str, name: Str, minPages: Int): Unit =
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
              ExternType.Mem(SymIdx(name), MemType(existing.externType.memType.lim.copy(min = minPages))),
            ))
      case N =>
        val id = SymIdx(name)
        memories = memories + (id -> Import(module, name, ExternType.Mem(id, MemType(Limits(minPages)))))
        cachedMemoryImport(key) = SymIdx(name)
  end ensureMemoryImport

  /** Returns the minimum page requirement of memory import (`module`, `name`) if present. */
  @deprecated("Use `getMemoryImport` instead to get the full memory import information.")
  def getMemoryImportMinPages(module: Str, name: Str): Opt[Int] =
    getMemoryImport(module, name).map(_.memType.lim.min)

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
  def addFunc(sym: Opt[Symbol], funcInfo: FuncInfo): FuncIdx =
    val id = funcInfo.id
    funcs = funcs + (id -> funcInfo)
    sym.foreach:
      namedFuncs(_) = funcInfo
    val idx = FuncIdx(funcInfo.id)
    val refType = RefType(funcInfo.typeUse.typeIdx, nullable = false)
    elemSegments = elemSegments +
      (id -> ElemSegment.Declare(id, refType -> Seq(ref.func(idx, refType))))
    idx

  @deprecated("Use the overload without `resolveSymIdx` instead.")
  def getFunc(funcref: FuncIdx | Symbol, resolveSymIdx: Bool): Opt[FuncIdx] =
    if resolveSymIdx then
      funcref match
        case FuncIdx(idx @ SymIdx(_)) =>
          funcs.zipWithIndex.collectFirst:
            case ((symIdx, _), i) if symIdx == idx => FuncIdx(NumIdx(i))
        case funcidx: FuncIdx => S(funcidx)
        case sym: Symbol =>
          namedFuncs.get(sym).flatMap: funcInfo =>
            funcs.zipWithIndex.collectFirst:
              case ((_, fi), i) if fi === funcInfo => FuncIdx(NumIdx(i))
    else getFunc(funcref)

  /** Returns the [[FuncIdx]] of the given `funcref`.
    */
  def getFunc(funcref: FuncIdx | Symbol): Opt[FuncIdx] = funcref match
    case funcidx: FuncIdx => S(funcidx)
    case sym: Symbol =>
      namedFuncs.get(sym).map: funcInfo =>
        funcInfo match
          case fi: FuncInfo => FuncIdx(fi.id)
          case imp: Import[ExternType.Func] => FuncIdx(imp.externType.id)

  @deprecated("Use the overload without `resolveSymIdx` instead.")
  def getFunc_!(funcref: FuncIdx | Symbol, resolveSymIdx: Bool): FuncIdx =
    getFunc(funcref, resolveSymIdx).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  /** Same as [[getFunc]] but throws an exception when the `funcref` is not found. */
  def getFunc_!(funcref: FuncIdx | Symbol): FuncIdx =
    getFunc(funcref).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  @nowarn("cat=deprecation")
  private def getFuncEntry(funcref: FuncIdx | Symbol): Opt[FuncInfo | Import[ExternType.Func]] = funcref match
    case FuncIdx(NumIdx(idx)) => funcs.drop(idx).headOption.map(_._2)
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
  def getGlobal(globalref: GlobalIdx | Symbol): Opt[GlobalIdx] = globalref match
    case globalidx: GlobalIdx => S(globalidx)
    case sym: Symbol =>
      namedGlobals.get(sym).map: globalEntry =>
        GlobalIdx(globalExternType(globalEntry).id)

  /** Same as [[getGlobal]] but throws an exception when the `globalref` is not found. */
  def getGlobal_!(globalref: GlobalIdx | Symbol): GlobalIdx =
    getGlobal(globalref).getOrElse:
      lastWords(s"Missing global definition for ${globalref.prettyString}")

  @nowarn("cat=deprecation")
  private def getGlobalEntry(globalref: GlobalIdx | Symbol): Opt[GlobalInfo | Import[ExternType.Global]] =
    globalref match
      case GlobalIdx(NumIdx(idx)) => globals.drop(idx.toInt).headOption.map(_._2)
      case GlobalIdx(idx @ SymIdx(_)) => globals.get(idx)
      case sym: Symbol => namedGlobals.get(sym)

  /** Returns the global extern metadata associated with the given `globalref`. */
  def getGlobalType(globalref: GlobalIdx | Symbol): Opt[ExternType.Global] =
    getGlobalEntry(globalref).map(globalExternType)

  /** Same as [[getGlobalType]] but throws an exception when the `globalref` is not found. */
  def getGlobalType_!(globalref: GlobalIdx | Symbol): ExternType.Global =
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

  /** Pushes a new local variable scope into this context. */
  def pushLocal(): Unit = locals = ListMap() :: locals

  /** Pops the top-most level local variable scope into this context. */
  def popLocal(): Unit = locals = locals.tail

  /** Adds a new local variable into the top-most variable scope. */
  def addLocal(sym: Local): LocalIdx =
    val idx = SymIdx(sym.nme)
    locals = (locals.head + (sym -> idx)) :: locals.tail
    LocalIdx(idx)

  /** Adds a [[Seq]] of local variables into the top-most variable scope. */
  def addLocals(syms: Seq[Local]): Seq[LocalIdx] =
    syms.map(addLocal)

  /** Checks whether the top-most level local variable scope contains the local variable `sym`. */
  def containsLocal(sym: Local): Bool = locals.head.contains(sym)

  /** Adds a new variable into the global variable scope. */
  def addGlobal(sym: Symbol, globalInfo: GlobalInfo): GlobalIdx =
    val id = globalInfo.id
    globals = globals + (id -> globalInfo)
    namedGlobals(sym) = globalInfo
    GlobalIdx(id)

  /** Adds a [[Seq]] of variables into the global variable scope. */
  def addGlobals(globalDefs: Seq[Symbol -> GlobalInfo]): Seq[GlobalIdx] =
    globalDefs.map(addGlobal.tupled)

  /** Checks whether the global variable scope contains the variable `sym`. */
  def containsGlobal(sym: Symbol): Bool = namedGlobals.contains(sym)

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

  /** Returns the runtime class tag for `sym`. */
  def getRuntimeClassTag(sym: BlockMemberSymbol): Opt[Int] =
    getAllRuntimeTags(sym).flatMap(_.headOption)

  /** Same as [[getRuntimeClassTag]] but throws if no runtime tag is known. */
  def getRuntimeClassTag_!(sym: BlockMemberSymbol): Int =
    getRuntimeClassTag(sym).getOrElse:
      lastWords(s"Missing runtime class tag for `${sym.toString}`")

  /** Configures the module start function. */
  def setStartFunc(funcIdx: FuncIdx): Unit =
    startFunc = S(funcIdx)

  /** Returns a tuple containing the variables in the current `global` and `local` scopes respectively.
    */
  def getWasmLocals: Seq[Symbol] -> Opt[Seq[Local]] =
    namedGlobals.keys.toSeq -> locals.headOption.map(l => l.keys.toSeq)

  /** Returns all local variable scopes and their variables. */
  def getAllWasmLocals: Ls[Seq[Local]] = locals match
    case Nil => namedGlobals.keys.toSeq :: Nil
    case locals => locals.init.map(l => l.keys.toSeq) :+ namedGlobals.keys.toSeq

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
