package hkmc2
package codegen
package wasm
package text

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import document.*
import document.Document
import semantics.*
import text.Param as WasmParam
import Instructions.*

import scala.collection.mutable.{ArrayBuffer as ArrayBuf, Map as MutMap}

/** A Wasm function and its associated information.
  *
  * Each instance of [[FuncInfo]] represents a single function definition in a WebAssembly module.
  *
  * @param id
  *   Symbolic identifier for the function, or `N` if the function is anonymous.
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
class FuncInfo(
    val id: Opt[SymIdx],
    val typeIdx: TypeIdx,
    params: Seq[Local -> Str],
    nResults: Int,
    locals: Seq[Local -> Str],
    val body: Expr,
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
      typeIdx: TypeIdx,
      params: Seq[Local -> Str],
      nResults: Int,
      locals: Seq[Local -> Str],
      body: Expr,
  ) = this(
    sym.optionIf(_.nameIsMeaningful).map(sym => SymIdx(sym.nme)),
    typeIdx,
    params,
    nResults,
    locals,
    body,
  )

  /** Returns the type of this function as a [[SignatureType]]. */
  def getSignatureType: SignatureType = SignatureType(
    params = params.map((_, varNme) => WasmParam(S(varNme), RefType.anyref)),
    results = Seq.fill(nResults)(Result(RefType.anyref)),
  )

  def toWat: Document =
    doc"""(func ${id.fold(doc"")(_.toWat)} (type ${typeIdx.toWat})${
        getSignatureType.toWat.surroundUnlessEmpty(doc" ")
      } #{ ${
        locals.map: p =>
          doc"(local $$${p._2} ${RefType.anyref.toWat})"
        .mkDocument(doc" # ").surroundUnlessEmpty(doc" # ")
      } # ${body.toWat} #} )${
        id.fold(doc""): id =>
          doc""" # (export "${id.id}" (func ${id.toWat})) # (elem declare func ${id.toWat})"""
      }"""
end FuncInfo

/** A Wasm global and its associated information.
  *
  * Each instance of [[GlobalInfo]] represents a single global definition in a WebAssembly module.
  *
  * @param id
  *   Symbolic identifier for the global.
  * @param valType
  *   The value type of the global.
  * @param mutable
  *   Whether the global is mutable.
  * @param init
  *   The initializer expression for the global.
  */
class GlobalInfo(val id: SymIdx, val valType: ValType, val mutable: Bool, val init: Expr) extends ToWat:

  /** Returns the symbolic identifier document used in global declarations. */
  private def idDoc: Document = id.toWat

  def toWat: Document =
    val typeDoc =
      if mutable then doc"(mut ${valType.toWat})"
      else valType.toWat
    doc"(global${idDoc.surroundUnlessEmpty(doc" ")} ${typeDoc} ${init.toWat})"
end GlobalInfo

/** A Wasm type and its associated information.
  *
  * Each instance of [[FuncInfo]] represents a single type defintion in a WebAssembly module.
  *
  * @param id
  *   Symbolic identifier for the function, or `N` if the function is anonymous.
  * @param compType
  *   The composite type this type definition represents.
  */
class TypeInfo(val id: Opt[SymIdx], val compType: CompType) extends ToWat:

  /** @param sym
    *   The source [[BlockMemberSymbol]] which this type is generated from.
    * @param compType
    *   The composite type this type definition represents.
    */
  def this(sym: BlockMemberSymbol, compType: CompType) = this(
    sym.optionIf(_.nameIsMeaningful).map(sym => SymIdx(sym.nme)),
    compType,
  )

  private def idDoc: Document = id.fold(doc"")(_.toWat)

  def toWat: Document = compType match
    case struct: StructType if struct.isSubtype =>
      val parentsDoc = struct.parents.optionIf(_.nonEmpty).fold(doc""): parents =>
        parents.map(_.toWat).mkDocument(doc" ")
      val structDoc = struct.copy(isSubtype = false).toWat
      doc"(type${idDoc.surroundUnlessEmpty(doc" ")} (sub${parentsDoc.surroundUnlessEmpty(doc" ")} ${structDoc}))"
    case _ =>
      doc"(type${idDoc.surroundUnlessEmpty(doc" ")} ${compType.toWat})"
end TypeInfo

/** A WebAssembly exception tag declaration.
  *
  * In Wasm, a `tag` names an exception kind and points to a function type that describes the payload values carried by
  * `throw tag ...` and extracted by matching `catch tag ...`.
  */
class TagInfo(val id: SymIdx, val typeIdx: TypeIdx) extends ToWat:

  def toWat: Document =
    doc"""(tag ${id.toWat} (type ${typeIdx.toWat})) # (export "${id.id}" (tag ${id.toWat}))"""
end TagInfo

enum WasmIntrinsicType:
  case TupleArray(mutable: Bool)

object Ctx:
  case class SingletonInfo(
      globalName: Str,
      globalTy: RefType,
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

  def empty: Ctx = Ctx(
    types = ArrayBuf.empty,
    namedTypes = MutMap.empty,
    memoryImports = ArrayBuf.empty,
    functionImports = ArrayBuf.empty,
    dataSegments = ArrayBuf.empty,
    funcs = ArrayBuf.empty,
    funcInfosByIndex = MutMap.empty,
    globals = ArrayBuf.empty,
    namedFuncs = MutMap.empty,
    tags = ArrayBuf.empty,
    namedGlobals = MutMap.empty,
    locals = MutMap() :: Nil,
    startFunc = N,
  )

  def ctx(using ctx: Ctx): Ctx = ctx

  extension (ref: CtxIdx | Symbol)
    private def prettyString: Str = ref match
      case idx: CtxIdx => s"type index `${idx.toWat.mkString()}`"
      case sym: Symbol => s"symbol `${sym.toString}`"
end Ctx

/** Context for [[WatBuilder]].
  *
  * @param types
  *   [[ArrayBuf]] containing all type definitions in the module.
  * @param namedTypes
  *   [[MutMap]] containing type symbols mapped to their corresponding Wasm type indices.
  * @param memoryImports
  *   [[ArrayBuf]] containing all memory imports in the module.
  * @param functionImports
  *   [[ArrayBuf]] containing all function imports in the module.
  * @param dataSegments
  *   [[ArrayBuf]] containing all data segments in the module.
  * @param funcs
  *   [[ArrayBuf]] containing all function definitions in the module.
  * @param globals
  *   [[ArrayBuf]] containing all global definitions in the module.
  * @param namedFuncs
  *   [[MutMap]] containing function symbols mapped to their corresponding Wasm function indices.
  * @param namedGlobals
  *   [[MutMap]] containing global symbols mapped to their corresponding Wasm global indices.
  * @param locals
  *   Stack of [[MutMap]] from local variable symbols to their numeric indices within the current function scope.
  */
class Ctx(
    types: ArrayBuf[TypeInfo],
    namedTypes: MutMap[BlockMemberSymbol, NumIdx],
    memoryImports: ArrayBuf[MemoryImport],
    functionImports: ArrayBuf[FuncImport],
    dataSegments: ArrayBuf[DataSegment],
    funcs: ArrayBuf[FuncInfo],
    funcInfosByIndex: MutMap[NumIdx, FuncInfo],
    globals: ArrayBuf[GlobalInfo],
    namedFuncs: MutMap[Symbol, NumIdx],
    tags: ArrayBuf[TagInfo],
    namedGlobals: MutMap[Symbol, NumIdx],
    var locals: Ls[MutMap[Local, NumIdx]],
    private var startFunc: Opt[FuncIdx],
) extends ToWat:

  import Ctx.prettyString

  private val wasmIntrinsicFuncs: MutMap[Str, FuncIdx] = MutMap.empty
  private val wasmIntrinsicTypes: MutMap[WasmIntrinsicType, TypeIdx] = MutMap.empty
  private val wasmIntrinsicTags: MutMap[Str, TagIdx] = MutMap.empty

  private val cachedMemoryImport: MutMap[(Str, Str), Int] = MutMap.empty
  private val cachedFunctionImports: MutMap[(Str, Str), FuncIdx] = MutMap.empty

  private val singletonByBms: MutMap[BlockMemberSymbol, Ctx.SingletonInfo] = MutMap.empty
  private val singletonByIsym: MutMap[ModuleOrObjectSymbol, Ctx.SingletonInfo] = MutMap.empty
  private val singletonInitActions: ArrayBuf[Expr] = ArrayBuf.empty

  /** Adds a type into this context. */
  def addType(sym: Opt[BlockMemberSymbol], typeInfo: TypeInfo): TypeIdx =
    val numIdx = NumIdx(types.size)
    types += typeInfo
    sym.foreach:
      namedTypes(_) = numIdx
    TypeIdx(typeInfo.id.getOrElse(numIdx))

  /** Returns the [[TypeIdx]] of the given `typeref`, optionally resolving the symbolic index into a numeric index.
    */
  def getType(typeref: TypeIdx | BlockMemberSymbol, resolveSymIdx: Bool = false): Opt[TypeIdx] =
    typeref match
      case TypeIdx(SymIdx(nme)) if resolveSymIdx =>
        namedTypes.find(_._1.nme == nme).map(t => TypeIdx(t._2))
      case typeidx: TypeIdx => S(typeidx)
      case sym: BlockMemberSymbol if resolveSymIdx => namedTypes.get(sym).map(TypeIdx(_))
      case sym: BlockMemberSymbol =>
        getType(sym, resolveSymIdx = true).map: numIdx =>
          getTypeInfo(numIdx).flatMap(_.id).fold(numIdx)(TypeIdx(_))

  /** Same as [[getType]] but throws an exception when the `typeref` is not found. */
  def getType_!(typeref: TypeIdx | BlockMemberSymbol, resolveSymIdx: Bool = false): TypeIdx =
    getType(typeref, resolveSymIdx).getOrElse:
      lastWords(s"Missing type definition for ${typeref.prettyString}")

  /** Returns the [[TypeInfo]] instance associated with the given `typeref`. */
  def getTypeInfo(typeref: TypeIdx | BlockMemberSymbol): Opt[TypeInfo] = typeref match
    case TypeIdx(NumIdx(idx)) => types.unapply(idx.toInt)
    case TypeIdx(SymIdx(nme)) =>
      namedTypes.find(_._1.nme == nme).flatMap(t => getTypeInfo(TypeIdx(t._2)))
    case sym: BlockMemberSymbol => namedTypes.get(sym).flatMap(idx => getTypeInfo(TypeIdx(idx)))

  /** Same as [[getTypeInfo]] but throws an exception when the `typeref` is not found. */
  def getTypeInfo_!(typeref: TypeIdx | BlockMemberSymbol): TypeInfo =
    getTypeInfo(typeref).getOrElse:
      lastWords(s"Missing type definition for ${typeref.prettyString}")

  /** Adds a function into this context. */
  def addFunc(sym: Opt[Symbol], funcInfo: FuncInfo): FuncIdx =
    val numIdx = NumIdx(functionImports.size + funcs.size)
    funcs += funcInfo
    funcInfosByIndex(numIdx) = funcInfo
    sym.foreach:
      namedFuncs(_) = numIdx
    FuncIdx(funcInfo.id.getOrElse(numIdx))

  /** Adds a function import into this context.
    *
    * Returns the function index in the global function index space.
    */
  def addFunctionImport(sym: Opt[Symbol], funcImport: FuncImport): FuncIdx =
    val numIdx = NumIdx(functionImports.size + funcs.size)
    functionImports += funcImport
    sym.foreach:
      namedFuncs(_) = numIdx
    FuncIdx(funcImport.id.getOrElse(numIdx))

  /** Returns the cached function import for (`module`, `name`), creating it with `createImport` if needed.
    */
  def getOrCreateFunctionImport(
      module: Str,
      name: Str,
  )(createImport: => FuncImport): FuncIdx =
    cachedFunctionImports.getOrElseUpdate((module, name), addFunctionImport(N, createImport))

  /** Adds or updates a memory import. If the import already exists, its minimum pages are increased to at least
    * `minPages`.
    */
  def ensureMemoryImport(module: Str, name: Str, minPages: Int): Unit =
    val key = module -> name
    cachedMemoryImport.get(key) match
      case S(idx) =>
        val existing = memoryImports(idx)
        val newMin = existing.minPages max minPages
        if newMin =/= existing.minPages then
          memoryImports(idx) = existing.copy(minPages = newMin)
      case N =>
        val idx = memoryImports.size
        memoryImports += MemoryImport(module, name, minPages)
        cachedMemoryImport(key) = idx

  /** Returns the minimum page requirement of memory import (`module`, `name`) if present. */
  def getMemoryImportMinPages(module: Str, name: Str): Opt[Int] =
    memoryImports.find(m => m.module === module && m.name === name).map(_.minPages)

  /** Adds a data segment into this context. */
  def addDataSegment(seg: DataSegment): Unit =
    dataSegments += seg

  /** Adds a tag into this context. */
  def addTag(tagInfo: TagInfo): TagIdx =
    tags += tagInfo
    TagIdx(tagInfo.id)

  /** Returns the [[FuncIdx]] of the given `funcref`, optionally resolving the symbolic index into a numeric index.
    */
  def getFunc(funcref: FuncIdx | Symbol, resolveSymIdx: Bool = false): Opt[FuncIdx] = funcref match
    case FuncIdx(SymIdx(nme)) if resolveSymIdx =>
      namedFuncs.find(_._1.nme == nme).map(f => FuncIdx(f._2))
    case funcidx: FuncIdx => S(funcidx)
    case sym: Symbol if resolveSymIdx => namedFuncs.get(sym).map(FuncIdx(_))
    case sym: Symbol =>
      getFunc(sym, resolveSymIdx = true).map: numIdx =>
        getFuncInfo(numIdx).flatMap(_.id).fold(numIdx)(FuncIdx(_))

  /** Same as [[getFunc]] but throws an exception when the `funcref` is not found. */
  def getFunc_!(funcref: FuncIdx | Symbol, resolveSymIdx: Bool = false): FuncIdx =
    getFunc(funcref, resolveSymIdx).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  /** Returns the [[FuncInfo]] instance associated with the given `funcref`. */
  def getFuncInfo(funcref: FuncIdx | Symbol): Opt[FuncInfo] = funcref match
    case FuncIdx(numIdx @ NumIdx(idx)) =>
      funcInfosByIndex.get(numIdx).orElse:
        val localIdx = idx.toInt - functionImports.size
        if localIdx < 0 then N else funcs.unapply(localIdx)
    case funcref => getFunc(funcref, resolveSymIdx = true).flatMap(getFuncInfo(_))

  /** Same as [[getFuncInfo]] but throws an exception when the `funcref` is not found. */
  def getFuncInfo_!(funcref: FuncIdx | Symbol): FuncInfo =
    getFuncInfo(funcref).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  /** Pushes a new local variable scope into this context. */
  def pushLocal(): Unit = locals = MutMap() :: locals

  /** Pops the top-most level local variable scope into this context. */
  def popLocal(): Unit = locals = locals.tail

  /** Adds a new local variable into the top-most variable scope. */
  def addLocal(sym: Local): LocalIdx =
    val numIdx = NumIdx(locals.head.size)
    locals.head(sym) = numIdx
    LocalIdx(numIdx)

  /** Adds a [[Seq]] of local variables into the top-most variable scope. */
  def addLocals(syms: Seq[Local]): Seq[LocalIdx] =
    syms.map(addLocal)

  /** Checks whether the top-most level local variable scope contains the local variable `sym`. */
  def containsLocal(sym: Local): Bool = locals.head.contains(sym)

  /** Adds a new variable into the global variable scope. */
  def addGlobal(sym: Symbol, globalInfo: GlobalInfo): GlobalIdx =
    val numIdx = NumIdx(globals.size)
    globals += globalInfo
    namedGlobals(sym) = numIdx
    GlobalIdx(globalInfo.id)

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

  /** Configures the module start function. */
  def setStartFunc(funcIdx: FuncIdx): Unit =
    startFunc = S(funcIdx)

  /** Converts a [[Map]] of symbols and their respective numeric identifiers into a [[Seq]] of symbols sorted by its
    * numeric index.
    */
  private def wasmLocalsToSeq(scope: Map[Symbol, NumIdx]): Seq[Local] =
    scope.toSeq.sortBy(_._2.index).map(_._1)

  /** Returns a tuple containing the variables in the current `global` and `local` scopes respectively.
    */
  def getWasmLocals: Seq[Symbol] -> Opt[Seq[Local]] =
    wasmLocalsToSeq(namedGlobals.toMap) -> locals.headOption.map(l => wasmLocalsToSeq(l.toMap))

  /** Returns all local variable scopes and their variables. */
  def getAllWasmLocals: Ls[Seq[Local]] = locals match
    case Nil => wasmLocalsToSeq(namedGlobals.toMap) :: Nil
    case _ => locals.init.map(l => wasmLocalsToSeq(l.toMap)) :+ wasmLocalsToSeq(namedGlobals.toMap)

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
    doc"(module #{  # ${
        (
          types.toSeq.map(_.toWat)
            ++ memoryImports.toSeq.map(_.toWat)
            ++ functionImports.toSeq.map(_.toWat)
            ++ dataSegments.toSeq.map(_.toWat)
            ++ globals.toSeq.map(_.toWat)
            ++ tags.toSeq.map(_.toWat)
            ++ startFunc.toSeq.map(funcIdx => doc"(start ${funcIdx.toWat})")
            ++ funcs.toSeq.map(_.toWat)
        ).mkDocument(doc" # ")
      } #} )"

end Ctx
