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

/** A Wasm function and its associated information.
  *
  * Each instance of [[FuncInfo]] represents a single function definition in a WebAssembly module.
  *
  * @param id
  *   Symbolic identifier for the function. If the function is an anonymous function, `id` should be generated from a
  *   fresh name allocated in the current scope.
  * @param typeUse
  *   [[TypeUse]] of the function's type in the module's type section.
  * @param params
  *   [[Seq]] of parameter local variables and their names.
  * @param nResults
  *   Number of results the function returns.
  * @param locals
  *   [[Seq]] of local variables (excluding parameters) and their names.
  * @param body
  *   The expression of the function body.
  * @param exports
  *   Optional export name for the function.
  */
class FuncInfo(
    val id: SymIdx,
    val typeUse: TypeUse,
    params: Seq[Local -> Str],
    nResults: Int,
    locals: Seq[Local -> Str],
    val body: Expr,
    val `export`: Opt[Str],
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
    nResults,
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
    nResults,
    locals,
    body,
    `export`,
  )

  /** Returns the type of this function as a [[SignatureType]]. */
  def getSignatureType: SignatureType = SignatureType(
    params = params.map((_, varNme) => WasmParam(varNme, RefType.anyref)),
    results = Seq.fill(nResults)(Result(RefType.anyref)),
  )

  def toWat: Document =
    doc"""(func ${id.toWat}${
        `export`.fold(doc""): e =>
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
  * @param valType
  *   The value type of the global.
  * @param mutable
  *   Whether the global is mutable.
  * @param init
  *   The initializer expression for the global.
  */
class GlobalInfo(val id: SymIdx, val valType: ValType, val mutable: Bool, val init: Expr) extends ToWat:

  def toWat: Document =
    val typeDoc =
      if mutable then doc"(mut ${valType.toWat})"
      else valType.toWat
    doc"(global ${id.toWat} $typeDoc ${init.toWat})"
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
  * Each instance of [[FuncInfo]] represents a single type defintion in a WebAssembly module.
  *
  * @param id
  *   Symbolic identifier for the function, or `N` if the function is anonymous.
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

  /** [[ListMap]] containing all global definitions in the module. */
  private var globals = ListMap.empty[SymIdx, GlobalInfo]

  /** [[MutMap]] containing global symbols mapped to their corresponding Wasm global indices. */
  private val namedGlobals = MutMap.empty[Symbol, GlobalInfo]

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

  private var labelTargets = Nil: List[(LabelSymbol, Ctx.LabelTarget)]
  private val singletonByBms = MutMap.empty[BlockMemberSymbol, Ctx.SingletonInfo]
  private val singletonByIsym = MutMap.empty[ModuleOrObjectSymbol, Ctx.SingletonInfo]
  private val singletonInitActions = ArrayBuf.empty[Expr]
  private val runtimeClassTags = MutMap.empty[BlockMemberSymbol, LinkedHashSet[Int]]

  private def imports: Seq[Import[?]] =
    val importedFuncs = funcs.collect:
      case (_, imp: Import[ExternType.Func]) => imp
    val importedMems = memories.collect:
      case (_, imp: Import[ExternType.Mem]) => imp
    (importedFuncs ++ importedMems).toSeq

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

  def registerRuntimeClassTags(sym: BlockMemberSymbol, tags: LinkedHashSet[Int]): Unit =
    runtimeClassTags(sym) = tags

  def getRuntimeClassTags(sym: BlockMemberSymbol): Opt[LinkedHashSet[Int]] =
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

  /** Returns the [[FuncInfo]] instance associated with the given `funcref`. */
  @nowarn("cat=deprecation")
  def getFuncInfo(funcref: FuncIdx | Symbol): Opt[FuncInfo] =
    val func = funcref match
      case FuncIdx(NumIdx(idx)) => funcs.drop(idx).headOption.map(_._2)
      case FuncIdx(idx @ SymIdx(_)) => funcs.get(idx)
      case funcref: Symbol => namedFuncs.get(funcref)
    func.collect:
      case funcInfo: FuncInfo => funcInfo

  /** Same as [[getFuncInfo]] but throws an exception when the `funcref` is not found. */
  def getFuncInfo_!(funcref: FuncIdx | Symbol): FuncInfo =
    getFuncInfo(funcref).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

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
    val memDefns = memories.valuesIterator.collect:
      case memInfo: MemInfo => memInfo.toWat
    val funcDefns = funcs.valuesIterator.collect:
      case funcInfo: FuncInfo => funcInfo.toWat
    doc"(module #{  # ${
        (
          types.valuesIterator.map(_.toWat)
            ++ imports.iterator.map(_.toWat)
            ++ tags.valuesIterator.map(_.toWat)
            ++ globals.valuesIterator.map(_.toWat)
            ++ memDefns
            ++ funcDefns
            ++ dataSegments.valuesIterator.map(_.toWat)
            ++ elemSegments.valuesIterator.map(_.toWat)
            ++ startFunc.iterator.map(funcIdx => doc"(start ${funcIdx.toWat})")
        ).toSeq.mkDocument(doc" # ")
      } #} )"

end Ctx
