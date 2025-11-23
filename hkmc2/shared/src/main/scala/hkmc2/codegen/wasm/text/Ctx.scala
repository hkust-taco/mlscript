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

import scala.collection.mutable.{ArrayBuffer as ArrayBuf, Map as MutMap}

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
    val body: Expr
) extends ToWat:

  /**
   * @param sym
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
      body: Expr
  ) = this(
    sym.optionIf(_.nameIsMeaningful).map(sym => SymIdx(sym.nme)),
    typeIdx,
    params,
    nResults,
    locals,
    body
  )

  /** Returns the type of this function as a [[SignatureType]]. */
  def getSignatureType: SignatureType = SignatureType(
    params = params.map((_, varNme) => WasmParam(S(varNme), RefType.anyref)),
    results = Seq.fill(nResults)(Result(RefType.anyref))
  )

  def toWat: Document =
    doc"""(func ${id.fold(doc"")(_.toWat)} (type ${typeIdx.toWat})${
        getSignatureType.toWat.surroundUnlessEmpty(doc" ")
      } #{ ${
        locals.map: p =>
          doc"(local $$${p._2} ${RefType.anyref.toWat})"
        .toSeq.mkDocument(doc" # ").surroundUnlessEmpty(doc" # ")
      } # ${body.toWat} #} )${
        id.fold(doc""): id =>
          doc""" # (export "${id.id}" (func ${id.toWat})) # (elem declare func ${id.toWat})"""
      }"""
end FuncInfo

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

  def toWat: Document =
    doc"(type ${id.fold(doc"")(id => doc"${id.toWat} ")}${compType.toWat})"
end TypeInfo

object Ctx:
  def empty: Ctx = Ctx(
    types = ArrayBuf.empty,
    namedTypes = MutMap.empty,
    funcs = ArrayBuf.empty,
    namedFuncs = MutMap.empty,
    locals = MutMap() :: Nil
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
 * @param namedFuncs
 *   [[MutMap]] containing function symbols mapped to their corresponding Wasm function indices.
 * @param locals
 *   Stack of [[MutMap]] from local variable symbols to their numeric indices within the current
 *   function scope.
 */
class Ctx(
    types: ArrayBuf[TypeInfo],
    namedTypes: MutMap[BlockMemberSymbol, NumIdx],
    funcs: ArrayBuf[FuncInfo],
    namedFuncs: MutMap[Symbol, NumIdx],
    var locals: Ls[MutMap[Local, NumIdx]]
) extends ToWat:

  import Ctx.prettyString

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
  def addGlobal(sym: Symbol): GlobalIdx =
    val numIdx = NumIdx(locals.last.size)
    locals.last(sym) = numIdx
    GlobalIdx(numIdx)

  /** Adds a [[Seq]] of variables into the global variable scope. */
  def addGlobals(syms: Seq[Symbol]): Seq[GlobalIdx] =
    syms.map(addGlobal)

    /** Checks whether the global variable scope contains the variable `sym`. */
  def containsGlobal(sym: Symbol): Bool = locals.last.contains(sym)

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
    wasmLocalsToSeq(locals.last.toMap) -> locals.headOption.map(l => wasmLocalsToSeq(l.toMap))

  /** Returns all local variable scopes and their variables. */
  def getAllWasmLocals: Ls[Seq[Local]] = locals.map(l => wasmLocalsToSeq(l.toMap))

  def toWat: Document =
    doc"""(module #{  # ${(types.toSeq ++ funcs.toSeq).map(_.toWat).mkDocument(doc" # ")}) #} """

end Ctx
