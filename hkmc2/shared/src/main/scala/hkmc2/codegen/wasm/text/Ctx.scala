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

/** Metadata for a REPL binding that can be imported by later Wasm modules. */
sealed trait WasmSessionBinding:
  /** Returns the deduplication key for this binding. */
  def bindingKey: Str
  /** Returns the symbols that should resolve to this binding. */
  def bindingSyms: Seq[Local]
  /** Returns the export name if this binding is re-exported. */
  def exportNameOpt: Opt[Str] = N

object WasmSessionBinding:
  val replModuleName: Str = "repl"

final case class WasmSessionFunc(
    sym: Symbol,
    moduleName: Str,
    exportName: Str,
    funcType: FunctionType
) extends WasmSessionBinding:
  def bindingKey: Str = s"func:$moduleName:$exportName"
  def bindingSyms: Seq[Local] = sym :: Nil
  override def exportNameOpt: Opt[Str] = S(exportName)

final case class WasmSessionGlobal(
    sym: Symbol,
    moduleName: Str,
    exportName: Str,
    valType: ValType,
    mutable: Bool
) extends WasmSessionBinding:
  def bindingKey: Str = s"global:$moduleName:$exportName"
  def bindingSyms: Seq[Local] = sym :: Nil
  override def exportNameOpt: Opt[Str] = S(exportName)

final case class WasmSessionClass(
    sym: BlockMemberSymbol,
    typeInfo: TypeInfo,
    runtimeTag: Int,
    aliasSyms: Seq[Local] = Nil
) extends WasmSessionBinding:
  def bindingKey: Str = s"class:${sym.uid}"
  def bindingSyms: Seq[Local] = sym +: aliasSyms

final case class WasmSessionSingleton(
    blockSym: BlockMemberSymbol,
    objectSym: Opt[ModuleOrObjectSymbol],
    moduleName: Str,
    exportName: Str,
    globalTy: RefType
) extends WasmSessionBinding:
  def bindingKey: Str = s"singleton:$moduleName:$exportName"
  def bindingSyms: Seq[Local] = blockSym +: objectSym.toSeq
  override def exportNameOpt: Opt[Str] = S(exportName)

final case class CompiledWasmModule(
    wat: Document,
    entryName: Str,
    sessionExports: Seq[WasmSessionBinding]
)

/**
 * A Wasm function and its associated information.
 *
 * Each instance of [[FuncInfo]] represents a single function definition in a WebAssembly module.
 *
 * @param id
 *   Symbolic identifier for the function, or `N` if the function is anonymous.
 * @param typeIdx
 *   Index of the function's type in the module's type section.
 * @param params
 *   [[Seq]] of parameter local variables and their names.
 * @param locals
 *   [[Seq]] of local variables (excluding parameters) and their names.
 * @param bodyOpt
 *   The expression of the function body, or `N` for imported functions.
 * @param resultTypes
 *   The result types of the function.
 * @param importModule
 *   The Wasm module name for imported functions.
 * @param importName
 *   The imported function name.
 * @param exportName
 *   Optional export name.
 */
class FuncInfo(
    val id: Opt[SymIdx],
    val typeIdx: TypeIdx,
    params: Seq[Local -> Str],
    locals: Seq[Local -> Str],
    val bodyOpt: Opt[Expr],
    val resultTypes: Seq[Result],
    val importModule: Opt[Str] = N,
    val importName: Opt[Str] = N,
    val exportName: Opt[Str] = N
) extends ToWat:

  /**
   * @param sym
   *   The source [[BlockMemberSymbol]] which this function is generated from.
   * @param typeIdx
   *   Index of the function's type in the module's type section.
   * @param params
   *   [[Seq]] of parameter local variables and their names.
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
      body: Expr
  ) = this(
    sym.optionIf(_.nameIsMeaningful).map(sym => SymIdx(sym.nme)),
    typeIdx,
    params,
    locals,
    S(body),
    Seq.fill(nResults)(Result(RefType.anyref)),
    N,
    N,
    sym.optionIf(_.nameIsMeaningful).map(_.nme)
  )

  def this(
      id: SymIdx,
      typeIdx: TypeIdx,
      params: Seq[Local -> Str],
      resultTypes: Seq[Result],
      importModule: Str,
      importName: Str
  ) = this(
    S(id),
    typeIdx,
    params,
    Seq.empty,
    N,
    resultTypes,
    S(importModule),
    S(importName),
    N
  )

  /** Returns the type of this function as a [[SignatureType]]. */
  def getSignatureType: SignatureType = SignatureType(
    params = params.map((_, varNme) => WasmParam(S(varNme), RefType.anyref)),
    results = resultTypes
  )

  /** Returns `true` when this function is declared via a Wasm import. */
  def isImported: Bool = importModule.nonEmpty

  def toWat: Document =
    importModule match
      case S(moduleName) =>
        doc"""(import "${moduleName}" "${importName.get}" (func ${id.fold(doc"")(_.toWat)}${
            getSignatureType.toWat.surroundUnlessEmpty(doc" ")
          }))"""
      case N =>
        val body = bodyOpt.getOrElse:
          lastWords(s"Missing body for function `${id.fold("<anonymous>")(_.id)}`")
        doc"""(func ${id.fold(doc"")(_.toWat)} (type ${typeIdx.toWat})${
            getSignatureType.toWat.surroundUnlessEmpty(doc" ")
          } #{ ${
            locals.map: p =>
              doc"(local $$${p._2} ${RefType.anyref.toWat})"
            .mkDocument(doc" # ").surroundUnlessEmpty(doc" # ")
          } # ${body.toWat} #} )${
            exportName.fold(doc""): name =>
              doc""" # (export "${name}" (func ${id.get.toWat})) # (elem declare func ${id.get.toWat})"""
          }"""
end FuncInfo

/**
 * A Wasm global and its associated information.
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
 *   The initializer expression for the global, or `N` for imported globals.
 * @param importModule
 *   The Wasm module name for imported globals.
 * @param importName
 *   The imported global name.
 * @param exportName
 *   Optional export name.
 */
class GlobalInfo(
    val id: SymIdx,
    val valType: ValType,
    val mutable: Bool,
    val init: Opt[Expr],
    val importModule: Opt[Str] = N,
    val importName: Opt[Str] = N,
    val exportName: Opt[Str] = N
) extends ToWat:

  /** Returns the symbolic identifier document used in global declarations. */
  private def idDoc: Document = id.toWat

  /** Returns `true` when this global is declared via a Wasm import. */
  def isImported: Bool = importModule.nonEmpty

  def toWat: Document =
    val typeDoc =
      if mutable then doc"(mut ${valType.toWat})"
      else valType.toWat
    importModule match
      case S(moduleName) =>
        doc"""(import "${moduleName}" "${importName.get}" (global${idDoc.surroundUnlessEmpty(doc" ")} ${typeDoc}))"""
      case N =>
        doc"(global${idDoc.surroundUnlessEmpty(doc" ")} ${typeDoc} ${init.get.toWat})${
          exportName.fold(doc""): name =>
            doc""" # (export "${name}" (global ${idDoc}))"""
        }"
end GlobalInfo

/**
 * A Wasm type and its associated information.
 *
 * Each instance of [[FuncInfo]] represents a single type defintion in a WebAssembly module.
 *
 * @param id
 *   Symbolic identifier for the function, or `N` if the function is anonymous.
 * @param compType
 *   The composite type this type definition represents.
 */
class TypeInfo(
    val id: Opt[SymIdx],
    val compType: CompType
) extends ToWat:

  /**
   * @param sym
   *   The source [[BlockMemberSymbol]] which this type is generated from.
   * @param compType
   *   The composite type this type definition represents.
   */
  def this(sym: BlockMemberSymbol, compType: CompType) = this(
    sym.optionIf(_.nameIsMeaningful).map(sym => SymIdx(sym.nme)),
    compType
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

enum WasmIntrinsicType:
  case TupleArray(mutable: Bool)

object Ctx:
  case class SingletonInfo(
      globalName: Str,
      globalTy: RefType
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
    "ge_impl" -> i32.ge_s
  )
  val unaryOps: Map[Str, Expr => Expr] = Map(
    "neg_impl" -> (value => i32.sub(i32.const(0), value)),
    "pos_impl" -> identity,
    "not_impl" -> i32.eqz
  )
  val wasmIntrinsicArities: Map[Str, Int] =
    (binaryOps.keys.map(_ -> 2) ++ unaryOps.keys.map(_ -> 1)).toMap
  val wasmIntrinsicNameSet: Set[Str] = wasmIntrinsicArities.keySet

  def empty: Ctx = Ctx(
    types = ArrayBuf.empty,
    namedTypes = MutMap.empty,
    funcs = ArrayBuf.empty,
    globals = ArrayBuf.empty,
    namedFuncs = MutMap.empty,
    namedGlobals = MutMap.empty,
    locals = MutMap() :: Nil,
    startFunc = N
  )

  def ctx(using ctx: Ctx): Ctx = ctx

  extension (ref: CtxIdx | Symbol)
    private def prettyString: Str = ref match
      case idx: CtxIdx => s"type index `${idx.toWat.mkString()}`"
      case sym: Symbol => s"symbol `${sym.toString}`"

/**
 * Context for [[WatBuilder]].
 *
 * @param types
 *   [[ArrayBuf]] containing all type definitions in the module.
 * @param namedTypes
 *   [[MutMap]] containing type symbols mapped to their corresponding Wasm type indices.
 * @param funcs
 *   [[ArrayBuf]] containing all function definitions in the module.
 * @param globals
 *   [[ArrayBuf]] containing all global definitions in the module.
 * @param namedFuncs
 *   [[MutMap]] containing function symbols mapped to their corresponding Wasm function indices.
 * @param namedGlobals
 *   [[MutMap]] containing global symbols mapped to their corresponding Wasm global indices.
 * @param locals
 *   Stack of [[MutMap]] from local variable symbols to their numeric indices within the current
 *   function scope.
 */
class Ctx(
    types: ArrayBuf[TypeInfo],
    namedTypes: MutMap[BlockMemberSymbol, NumIdx],
    funcs: ArrayBuf[FuncInfo],
    globals: ArrayBuf[GlobalInfo],
    namedFuncs: MutMap[Symbol, NumIdx],
    namedGlobals: MutMap[Symbol, NumIdx],
    var locals: Ls[MutMap[Local, NumIdx]],
    private var startFunc: Opt[FuncIdx]
) extends ToWat:

  import Ctx.prettyString

  private val wasmIntrinsicFuncs: MutMap[Str, FuncIdx] = MutMap.empty
  private val wasmIntrinsicTypes: MutMap[WasmIntrinsicType, TypeIdx] = MutMap.empty
  private val singletonByBms: MutMap[BlockMemberSymbol, Ctx.SingletonInfo] = MutMap.empty
  private val singletonByIsym: MutMap[ModuleOrObjectSymbol, Ctx.SingletonInfo] = MutMap.empty
  private val singletonInitActions: ArrayBuf[Expr] = ArrayBuf.empty
  private val runtimeClassTags: MutMap[BlockMemberSymbol, Int] = MutMap.empty

  /** Adds a type into this context. */
  def addType(sym: Opt[BlockMemberSymbol], typeInfo: TypeInfo): TypeIdx =
    val numIdx = NumIdx(types.size)
    types += typeInfo
    sym.foreach:
      namedTypes(_) = numIdx
    TypeIdx(typeInfo.id.getOrElse(numIdx))

  /**
   * Returns the [[TypeIdx]] of the given `typeref`, optionally resolving the symbolic index into a
   * numeric index.
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
    val numIdx = NumIdx(funcs.size)
    funcs += funcInfo
    sym.foreach:
      namedFuncs(_) = numIdx
    FuncIdx(funcInfo.id.getOrElse(numIdx))

  /**
   * Returns the [[FuncIdx]] of the given `funcref`, optionally resolving the symbolic index into a
   * numeric index.
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
    case FuncIdx(NumIdx(idx)) => funcs.unapply(idx.toInt)
    case funcref => getFunc(funcref, resolveSymIdx = true).flatMap(getFuncInfo(_))

  /** Same as [[getFuncInfo]] but throws an exception when the `funcref` is not found. */
  def getFuncInfo_!(funcref: FuncIdx | Symbol): FuncInfo =
    getFuncInfo(funcref).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  /**
   * Returns the [[GlobalIdx]] of the given `globalref`, optionally resolving the symbolic index
   * into a numeric index.
   */
  def getGlobal(globalref: GlobalIdx | Symbol, resolveSymIdx: Bool = false): Opt[GlobalIdx] =
    globalref match
      case GlobalIdx(SymIdx(nme)) if resolveSymIdx =>
        namedGlobals.find(_._1.nme == nme).map(g => GlobalIdx(g._2))
      case globalidx: GlobalIdx => S(globalidx)
      case sym: Symbol if resolveSymIdx => namedGlobals.get(sym).map(GlobalIdx(_))
      case sym: Symbol =>
        getGlobal(sym, resolveSymIdx = true).map: numIdx =>
          getGlobalInfo(numIdx).fold(numIdx)(info => GlobalIdx(info.id))

  /** Same as [[getGlobal]] but throws an exception when the `globalref` is not found. */
  def getGlobal_!(globalref: GlobalIdx | Symbol, resolveSymIdx: Bool = false): GlobalIdx =
    getGlobal(globalref, resolveSymIdx).getOrElse:
      lastWords(s"Missing global definition for ${globalref.prettyString}")

  /** Returns the [[GlobalInfo]] instance associated with the given `globalref`. */
  def getGlobalInfo(globalref: GlobalIdx | Symbol): Opt[GlobalInfo] = globalref match
    case GlobalIdx(NumIdx(idx)) => globals.unapply(idx.toInt)
    case globalref => getGlobal(globalref, resolveSymIdx = true).flatMap(getGlobalInfo(_))

  /** Same as [[getGlobalInfo]] but throws an exception when the `globalref` is not found. */
  def getGlobalInfo_!(globalref: GlobalIdx | Symbol): GlobalInfo =
    getGlobalInfo(globalref).getOrElse:
      lastWords(s"Missing global definition for ${globalref.prettyString}")

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

  /** Checks whether singleton info has been registered for `sym`. */
  def containsSingleton(sym: BlockMemberSymbol): Bool = singletonByBms.contains(sym)

  /** Returns singleton info for `sym`. */
  def getSingletonInfo(sym: Local): Opt[Ctx.SingletonInfo] = sym match
    case bms: BlockMemberSymbol => singletonByBms.get(bms)
    case isym: ModuleOrObjectSymbol => singletonByIsym.get(isym)
    case _ => N

  /** Registers singleton info under its available symbols. */
  def registerSingleton(
      bms: BlockMemberSymbol,
      isym: Opt[ModuleOrObjectSymbol],
      info: Ctx.SingletonInfo
  ): Unit =
    singletonByBms(bms) = info
    isym.foreach(singletonByIsym(_) = info)

  /** Appends a singleton initialization action. */
  def addSingletonInitAction(action: Expr): Unit =
    singletonInitActions += action

  /** Returns the singleton initialization actions. */
  def getSingletonInitActions: Seq[Expr] = singletonInitActions.toSeq

  /** Records the runtime class tag for `sym`. */
  def registerRuntimeClassTag(sym: BlockMemberSymbol, tag: Int): Unit =
    runtimeClassTags(sym) = tag

  /** Returns the runtime class tag for `sym`. */
  def getRuntimeClassTag(sym: BlockMemberSymbol): Opt[Int] =
    runtimeClassTags.get(sym)

  /** Same as [[getRuntimeClassTag]] but throws if no runtime tag is known. */
  def getRuntimeClassTag_!(sym: BlockMemberSymbol): Int =
    getRuntimeClassTag(sym).getOrElse:
      lastWords(s"Missing runtime class tag for `${sym.toString}`")

  /** Configures the module start function. */
  def setStartFunc(funcIdx: FuncIdx): Unit =
    startFunc = S(funcIdx)

  /**
   * Converts a [[Map]] of symbols and their respective numeric identifiers into a [[Seq]] of
   * symbols sorted by its numeric index.
   */
  private def wasmLocalsToSeq(scope: Map[Symbol, NumIdx]): Seq[Local] =
    scope.toSeq.sortBy(_._2.index).map(_._1)

  /**
   * Returns a tuple containing the variables in the current `global` and `local` scopes
   * respectively.
   */
  def getWasmLocals: Seq[Symbol] -> Opt[Seq[Local]] =
    wasmLocalsToSeq(namedGlobals.toMap) -> locals.headOption.map(l => wasmLocalsToSeq(l.toMap))

  /** Returns all local variable scopes and their variables. */
  def getAllWasmLocals: Ls[Seq[Local]] = locals match
    case Nil => wasmLocalsToSeq(namedGlobals.toMap) :: Nil
    case _ =>
      locals.init.map(l => wasmLocalsToSeq(l.toMap)) :+ wasmLocalsToSeq(namedGlobals.toMap)

  /**
   * Returns the cached [[FuncIdx]] for the intrinsic named `name`, creating it with
   * `createIntrinsic` if it does not yet exist in this context.
   */
  def getOrCreateWasmIntrinsic(name: Str, createIntrinsic: => FuncIdx): FuncIdx =
    wasmIntrinsicFuncs.getOrElseUpdate(name, createIntrinsic)

  /**
   * Returns the cached [[TypeIdx]] for the intrinsic type `key`, creating it with `createType` if
   * it does not yet exist in this context.
   */
  def getOrCreateWasmIntrinsicType(key: WasmIntrinsicType, createType: => TypeIdx): TypeIdx =
    wasmIntrinsicTypes.getOrElseUpdate(key, createType)

  def toWat: Document =
    val importedGlobals = globals.toSeq.filter(_.isImported).map(_.toWat)
    val definedGlobals = globals.toSeq.filterNot(_.isImported).map(_.toWat)
    val importedFuncs = funcs.toSeq.filter(_.isImported).map(_.toWat)
    val definedFuncs = funcs.toSeq.filterNot(_.isImported).map(_.toWat)
    val startDef = startFunc.toSeq.map(funcIdx => doc"(start ${funcIdx.toWat})")
    doc"(module #{  # ${(types.toSeq.map(_.toWat) ++ importedGlobals ++ importedFuncs ++ definedGlobals ++ startDef ++ definedFuncs).mkDocument(doc" # ")}) #} "

end Ctx
