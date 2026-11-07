package hkmc2
package codegen
package wasm
package text

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*

import document.*
import document.Document
import semantics.{
  BaseTypeSymbol, BlockMemberSymbol, Elaborator, InnerSymbol, LabelSymbol, LocalVarSymbol, ModuleOrObjectSymbol, Symbol,
  TempSymbol, TermSymbol,
},
  Elaborator.State
import text.Param as WasmParam
import Instructions.*
import Message.MessageContext

import scala.collection.immutable.ListMap
import scala.collection.mutable.{ArrayBuffer as ArrayBuf, Map as MutMap}
import scala.reflect.ClassTag

/** The emitted Wasm module.
  *
  * @param wat
  *   The generated WAT for the module.
  * @param entryName
  *   The name of the module entry function.
  * @param systemMemMinPages
  *   The minimum number of imported system-memory pages required by the module.
  */
final case class CompiledWasmModule(
    wat: Document,
    entryName: Str,
    systemMemMinPages: Int,
)

/** A Wasm function and its associated information.
  *
  * @param sym
  *   The source [[ExternSymbol]] which this function is generated from.
  * @param typeUse
  *   [[TypeUse]] of the function's type in the module's type section.
  * @param params
  *   [[Seq]] of parameter local variables with their identifiers and resolved Wasm parameter types.
  * @param resultTypes
  *   The result types of the function.
  * @param locals
  *   [[Seq]] of local variables (excluding parameters) and their names.
  * @param body
  *   The instructions of the function body. The last one leaves the function's results or transfers control.
  * @param optionalParams
  *   Physical parameter indices that host wrappers must supply as null when omitted.
  * @param wrapId
  *   A pair of optional strings for adding a prefix and suffix to the generated identifier of this function.
  */
class FuncInfo(
    val sym: ExternSymbol,
    val typeUse: TypeUse,
    val params: Seq[SlotSymbol -> WasmParam],
    val resultTypes: Seq[Result],
    val locals: Seq[SlotSymbol -> SymIdx],
    val body: Seq[Expr],
    val optionalParams: Set[Int],
    val wrapId: Opt[Str] -> Opt[Str] = N -> N,
)(using Ctx, Raise, State) extends ToWat:

  /** Symbolic identifier for the function. */
  val id = SymIdx(summon[Ctx].funcScp.allocateOrGetNameWrapped(sym, wrapId))

  assert(optionalParams.forall(i => i >= 0 && i < params.size), "Optional parameter index outside the Wasm signature")

  /** Returns the type of this function as a [[SignatureType]]. */
  def getSignatureType: SignatureType = SignatureType(
    params = params.map(_._2),
    results = resultTypes,
  )

  /** The name under which the module exports this function; see [[Ctx.fileExportName]]. */
  def exportName: Str = summon[Ctx].fileExportName(sym, "func", wrapId)

  def toWat: Document =
    doc"""(func ${id.toWat} (export "$exportName") ${typeUse.toWat}${
        getSignatureType.toWat.surroundUnlessEmpty(doc" ")
      } #{ ${
        locals.map: p =>
          doc"(local ${p._2.toWat} ${p._1.localType.toWat})"
        .mkDocument(doc" # ").surroundUnlessEmpty(doc" # ")
      } # ${body.map(_.toWat).mkDocument(doc" # ")} #} )"""
end FuncInfo

/** A Wasm global and its associated information.
  *
  * Each instance of [[GlobalInfo]] represents a single global definition in a WebAssembly module.
  *
  * @param globalType
  *   The type of the global.
  * @param init
  *   The initializer expression for the global.
  * @param sym
  *   The source [[ScopedSymbol]] which this global is generated from.
  * @param wrapId
  *   A pair of optional strings for adding a prefix and suffix to the generated identifier of this global.
  */
class GlobalInfo(
    val globalType: GlobalType,
    val init: Expr,
    val sym: ScopedSymbol,
    val wrapId: Opt[Str] -> Opt[Str] = N -> N,
)(using Ctx, Raise) extends ToWat:

  /** Symbolic identifier for the global. */
  val id: SymIdx = SymIdx(summon[Ctx].globalScp.allocateOrGetNameWrapped(sym, wrapId))

  /** The name under which the module exports this global; see [[Ctx.fileExportName]]. */
  def exportName: Str = summon[Ctx].fileExportName(sym, "global", wrapId)

  def toWat: Document =
    doc"""(global ${id.toWat} (export "$exportName") ${globalType.toWat} ${init.toWat})"""
end GlobalInfo

/** A WebAssembly memory and its associated information.
  *
  * Each instance of [[MemInfo]] represents a single memory definition in a WebAssembly module.
  *
  * @param sym
  *   The source [[ExternSymbol]] which this memory is generated from.
  * @param memType
  *   The type of the memory.
  * @param wrapId
  *   A pair of optional strings for adding a prefix and suffix to the generated identifier of this memory.
  */
class MemInfo(val sym: ExternSymbol, val memType: MemType, val wrapId: Opt[Str] -> Opt[Str] = N -> N)(using Ctx, Raise)
    extends ToWat:

  /** Symbolic identifier for the memory. */
  val id: SymIdx = SymIdx(summon[Ctx].memoryScp.allocateOrGetNameWrapped(sym, wrapId))

  def toWat: Document = doc"(memory ${id.toWat} ${memType.toWat})"
end MemInfo

/** A Wasm type and its associated information.
  *
  * Each instance of [[TypeInfo]] represents a single type definition in a WebAssembly module.
  *
  * @param sym
  *   The source [[ExternSymbol]] which this type is generated from.
  * @param wrapId
  *   A pair of optional strings for adding a prefix and suffix to the generated identifier of this type.
  * @param compType
  *   The composite type this type definition represents.
  * @param objectTag
  *   An optional object tag number associated with this type.
  */
final class TypeInfo(
    val sym: ExternSymbol,
    val compType: CompType,
    val objectTag: Opt[Int],
    val wrapId: Opt[Str] -> Opt[Str] = N -> N,
)(using Ctx, Raise) extends ToWat:

  /** Symbolic identifier for the type. */
  val id = SymIdx(summon[Ctx].typeScp.allocateOrGetNameWrapped(sym, wrapId))

  /** Returns this composite type as a [[FunctionType]], throwing an exception if it is not. */
  def asFunctionType_! : FunctionType = compType match
    case funcType: FunctionType => funcType
    case _ => lastWords(s"type `${id.id}` is not a function type")

  def toWat: Document = doc"(type ${id.toWat} ${compType.toWat})"

/** A WebAssembly exception tag declaration.
  *
  * In Wasm, a `tag` names an exception kind and points to a function type that describes the payload values carried by
  * `throw tag ...` and extracted by matching `catch tag ...`.
  *
  * @param typeUse
  *   The function type referenced by this tag.
  * @param sym
  *   The source [[LocalVarSymbol]] which this tag is generated from.
  */
class TagInfo(
    val typeUse: TypeUse,
    val sym: LocalVarSymbol,
    val wrapId: Opt[Str] -> Opt[Str] = N -> N,
)(using Ctx, Raise) extends ToWat:

  /** Symbolic identifier for the tag. */
  val id: SymIdx = SymIdx(summon[Ctx].tagScp.allocateOrGetNameWrapped(sym, wrapId))

  def toWat: Document =
    doc"""(tag ${id.toWat} (export "${id.id}") ${typeUse.toWat})"""
end TagInfo

enum WasmIntrinsicType:
  case TupleArray(mutable: Bool)
  
  /** Shared erased Wasm function type for a virtual method slot introduced by `baseSym` with the given non-`this` param
    * types, including a concretely-typed `this`. Keyed on the full param-type vector (not just arity) and the result
    * type so distinct virtual methods of the same arity on the same base class don't collide.
    */
  case VirtualMethod(baseSym: BaseTypeSymbol, paramTypes: List[ValType], resultType: ValType)

/** An argument passed to a Wasm intrinsic function.
  *
  * This class also stores the parameter's kind (i.e. instruction argument vs stack argument), since some wasm
  * intrinsics (e.g. `i32.const`) only accept a constant literal as part of the instruction.
  *
  * @param intrName
  *   The name of the intrinsic this argument was passed to, for diagnostics.
  * @param idx
  *   The zero-based position of this argument, for diagnostics.
  * @param mkOperand
  *   This argument compiled as an expression, paired with the name of the type the intrinsic declares for this
  *   parameter, present only if the compiled operand does not conform to it.
  *
  *   Compiled on demand, since an argument the intrinsic reads as an immediate need not be representable as a value
  *   at all: a decimal literal, for one, has no representation of its own in this backend, and compiling one would
  *   report that instead of the intrinsic using it as an `f32`/`f64` immediate perfectly well.
  * @param litValue
  *   The numeric literal this argument was written as, if it was written as one.
  * @param loc
  *   The source location of this argument.
  * @param irStr
  *   This argument's Block IR, reported as the extra info of a diagnostic that does not compile the operand.
  */
class IntrinsicArg(
    private val intrName: Str,
    private val idx: Int,
    mkOperand: => (Expr, Opt[Str]),
    private val litValue: Opt[BigInt | BigDecimal],
    private val loc: Opt[Loc],
    irStr: => Str,
):
  private lazy val compiled: (Expr, Opt[Str]) = mkOperand

  /** Reports `errMsg` and recovers with `recovery`, mirroring how `errExpr` recovers with `unreachable`. */
  private def fail[T](errMsg: Message, extra: => Any, recovery: T)(using Raise): T =
    raise(ErrorReport(Ls(errMsg -> loc), source = Diagnostic.Source.Compilation, extraInfo = S(extra)))
    recovery

  /** This argument as a value pushed on the stack. */
  def asOp(using Raise): Expr =
    val (operand, operandXtype) = compiled
    operandXtype.fold(operand): xtype =>
      fail(
        msg"Operand #${(idx + 1).toString} of wasm intrinsic '$intrName' must be of type '${xtype.toString}'",
        operand,
        unreachable,
      )

  /** Reports that this argument is not written as a literal of the kind its immediate needs. */
  private def notALiteral[T](expected: Str, recovery: T)(using Raise): T =
    fail(msg"Wasm intrinsic '$intrName' expects $expected literal immediate", irStr, recovery)

  /** Reports that this argument's literal does not denote a value its immediate's type can hold. */
  private def outOfRange[T](tpe: Str, recovery: T)(using Raise): T =
    fail(
      msg"Immediate #${(idx + 1).toString} of wasm intrinsic '$intrName' is outside the $tpe range",
      irStr,
      recovery,
    )

  /** This argument's literal as an exact decimal, whichever kind of numeric literal it was written as. */
  private def numericLit: Opt[BigDecimal] = litValue.map:
    case value: BigInt => BigDecimal(value)
    case value: BigDecimal => value

  /** This argument as an `i32` immediate, which must be written as an integer literal at the call site. */
  def asImm32(using Raise): Int = litValue match
    case S(value: BigInt) => if value.isValidInt then value.toInt else outOfRange("signed 32-bit", 0)
    case _ => notALiteral("an integer", 0)

  /** This argument as an `i64` immediate, which must be written as an integer literal at the call site. */
  def asImm64(using Raise): Long = litValue match
    case S(value: BigInt) => if value.isValidLong then value.toLong else outOfRange("signed 64-bit", 0L)
    case _ => notALiteral("an integer", 0L)

  /** This argument as an `f32` immediate, which must be written as a numeric literal at the call site.
    *
    * An integer literal is accepted alongside a decimal one, since `1` and `1.0` denote the same float. A literal of a
    * magnitude no `f32` can hold is reported rather than silently emitted as an infinity; one that merely needs more
    * precision than an `f32` has is rounded, as Wasm itself specifies - including one too small to hold at all, which
    * rounds to zero.
    */
  def asImmF32(using Raise): Float = numericLit match
    case S(value) =>
      val narrowed = value.toFloat
      if narrowed.isFinite then narrowed else outOfRange("f32", 0f)
    case N => notALiteral("a numeric", 0f)

  /** This argument as an `f64` immediate. See [[asImmF32]]. */
  def asImmF64(using Raise): Double = numericLit match
    case S(value) =>
      val narrowed = value.toDouble
      if narrowed.isFinite then narrowed else outOfRange("f64", 0d)
    case N => notALiteral("a numeric", 0d)
end IntrinsicArg

/** The body of a Wasm intrinsic function: builds the instruction from its resolved arguments.
  *
  * The implementation body can assume that the argument count is correct.
  */
type IntrinsicBody = Seq[IntrinsicArg] => Raise ?=> Expr

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

/** Tracks the parameter slots, local variables, and jump labels used while generating one Wasm function body. Slot
  * types describe the emitted function signature: virtual overrides use their inherited parameter slots.
  *
  * @param _params
  *   The parameters of this function.
  * @param thisSym
  *   The implicit `this` parameter symbol if this function is generated from a non-static method, or `N` otherwise.
  * @param resultType
  *   The physical result slot in which undefined returns must materialize a value.
  * @param loc
  *   The location of the function's definition, which locates a result-type error for a return that has no location of
  *   its own, such as one introduced by an optimization.
  * @param paramTypes
  *   Physical types for parameter slots, with the receiver first when `thisSym` is present. Slots without an entry
  *   derive their type from the parameter symbol. Methods pass their registered signature so loads, calls, and the
  *   emitted function declaration agree on the inherited slots.
  */
class FunctionCtx(
    _params: Ls[LoweredParamList],
    thisSym: Opt[InnerSymbol],
    val resultType: Opt[ValType],
    val loc: Opt[Loc],
    paramTypes: Opt[Seq[ValType]] = N,
)(using Ctx, Raise, State):

  /** [[Scope]] for generating WAT identifiers of locals. */
  private[text] val localScp = Scope.empty(Scope.Cfg.default)

  /** The parameter of this function, represented by a tuple of the symbol representing the parameter and its symbolic
    * identifier.
    */
  val params: Seq[SlotSymbol -> SymIdx] =
    if _params.length > 1 then
      lastWords("Multiple parameter lists are not yet supported")
    val thisParam = thisSym.map: dis =>
      dis -> SymIdx(localScp.addToBindings(dis, "this", shadow = false))
    thisParam.toSeq ++ _params.flatMap(_.paramSyms).map(p => p -> SymIdx(localScp.allocateName(p)))

  /** The declared Wasm value type of each parameter slot (including implicit `$this`), resolved eagerly at construction
    * (index 0 = `this`).
    */
  private val resolvedParamTypes: Map[SlotSymbol, ValType] =
    params.zipWithIndex.map:
      case ((sym, _), idx) => sym -> resolveParamType(sym, idx, paramTypes)
    .toMap

  /** The parameters of this function with their identifiers and resolved Wasm types, ready to hand to a [[FuncInfo]].
    */
  val resolvedParams: Seq[SlotSymbol -> WasmParam] =
    params.map:
      case (sym, idx) => sym -> WasmParam(idx, resolvedParamTypes(sym))
  private val _locals = ArrayBuf.empty[SlotSymbol]
  private var labels = ListMap.empty[LabelSymbol, FunctionCtx.ControlFlowCtx]

  /** Adds a Wasm local into this context.
    *
    * @param customName
    *   An optional name for the local variable. If provided, the local will be emitted with the given name instead of
    *   an auto-generated one.
    */
  def addLocal(local: SlotSymbol, customName: Opt[Str] = N): LocalIdx =
    customName match
      case S(name) => localScp.addToBindings(local, name, shadow = false)
      case N => localScp.allocateName(local)
    _locals += local
    LocalIdx(SymIdx(localScp.lookup_!(local, N)))

  /** Looks up the given `sym` in this function context, returning its [[LocalIdx]] if it exists. */
  def lookupLocal(sym: SlotSymbol): Opt[LocalIdx] =
    localScp.lookup(sym).map(idx => LocalIdx(SymIdx(idx)))

  /** Similar to [[lookupLocal]], but throws an exception if `sym` is not in this context. */
  def lookupLocal_!(sym: SlotSymbol, loc: Opt[Loc]): LocalIdx =
    LocalIdx(SymIdx(localScp.lookup_!(sym, loc)))

  /** The locals of this function, represented by a tuple of the symbol representing the parameter and its symbolic
    * identifier.
    */
  def locals: Seq[SlotSymbol -> SymIdx] = _locals.map(l => l -> SymIdx(localScp.lookup_!(l, N))).toSeq

  /** The declared Wasm value type of the param/local slot for `sym`.
    *
    * Parameter slot types are resolved eagerly at construction (see [[resolvedParamTypes]]): each comes from the slot's
    * `paramTypes` override if present, otherwise from the symbol's erased type via [[paramType]]. Local slots derive
    * their type from the symbol's erased type via [[localType]].
    */
  def slotType(sym: SlotSymbol)(using Ctx): ValType =
    resolvedParamTypes.getOrElse(sym, sym.localType)

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

/** Generates a body in a fresh [[FunctionCtx]] and returns it with the context that records its parameters and locals
  * for the function declaration. `paramTypes` supplies physical slot types, including any implicit receiver, as in
  * [[FunctionCtx]].
  *
  * Rejects unsupported rest parameters without compiling their bodies. Optional fixed parameters retain their slots:
  * callers supply null for omitted arguments when the slot's type permits it.
  */
def genFuncBody(
    params: Ls[LoweredParamList],
    thisSym: Opt[InnerSymbol],
    resultType: Opt[ValType],
    loc: Opt[Loc],
    paramTypes: Opt[Seq[ValType]] = N,
)(mkBody: FunctionCtx ?=> Vector[Expr])(using Ctx, Raise, State): Vector[Expr] -> FunctionCtx =
  // * Calls pad omitted optional arguments with null to preserve Wasm's fixed arity.
  // * Variadic parameters still need argument packing: binding one as a plain parameter would
  // * pass a single argument rather than an array of the remaining ones.
  params.foreach: ps =>
    ps.restParam.foreach: p =>
      // * The rest parameter introduced when lowering trailing parameters has no location of its own.
      raise(ErrorReport(
        msg"Variadic parameters are not supported by the WebAssembly backend." -> p.toLoc.orElse(ps.toLoc) :: Nil,
        source = Diagnostic.Source.Compilation,
      ))
  val funcCtx = FunctionCtx(params, thisSym, resultType, loc, paramTypes)
  val result = if params.exists(_.restParam.nonEmpty) then Vector(unreachable) else mkBody(using funcCtx)
  result -> funcCtx
end genFuncBody

object Ctx:
  case class SingletonInfo(
      globalName: Str,
      globalTy: RefType,
  )

  /** Information about a virtual method slot in the virtual table.
    *
    * @param sym
    *   The symbol of the method occupying this slot.
    * @param owner
    *   The symbol of the class that introduced this slot.
    * @param paramTypes
    *   The non-`this` parameter types of the method that introduced this slot.
    * @param resultType
    *   The result type of the method that introduced this slot. Overriding methods inherit it, since all overrides
    *   share the slot's Wasm function type.
    */
  case class VirtualMethodInfo(
      sym: TermSymbol,
      owner: BaseTypeSymbol,
      paramTypes: Seq[ValType],
      resultType: ValType,
  )

  /** Derived virtual-dispatch layout for one class.
    *
    * @param slots
    *   Slot-ordered information about virtual method symbols, used when declaring and initializing RTTI slot fields.
    * @param slotOf
    *   Reverse lookup from a resolved method symbol to its virtual slot index.
    */
  case class VirtualTable(
      slots: List[VirtualMethodInfo],
      slotOf: Map[TermSymbol, Int],
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

  /** The `wasm.`-prefixed intrinsics, keyed on the instruction they emit.
    *
    * Listed in the order the prelude declares them, so the two can be checked against each other by eye.
    */
  val wasmInstrIntrinsics: Map[Str, IntrinsicBody] = Map(
    "i32.const" -> (args => i32.const(args(0).asImm32)),
    "i32.add" -> (args => i32.add(args(0).asOp, args(1).asOp)),
    "i32.sub" -> (args => i32.sub(args(0).asOp, args(1).asOp)),
    "i32.mul" -> (args => i32.mul(args(0).asOp, args(1).asOp)),
    "i32.div_s" -> (args => i32.div_s(args(0).asOp, args(1).asOp)),
    "i32.rem_s" -> (args => i32.rem_s(args(0).asOp, args(1).asOp)),
    "i32.shl" -> (args => i32.shl(args(0).asOp, args(1).asOp)),
    "i32.shr_s" -> (args => i32.shr_s(args(0).asOp, args(1).asOp)),
    "i32.shr_u" -> (args => i32.shr_u(args(0).asOp, args(1).asOp)),
    "i32.eq" -> (args => i32.eq(args(0).asOp, args(1).asOp)),
    "i32.ne" -> (args => i32.ne(args(0).asOp, args(1).asOp)),
    "i32.lt_s" -> (args => i32.lt_s(args(0).asOp, args(1).asOp)),
    "i32.le_s" -> (args => i32.le_s(args(0).asOp, args(1).asOp)),
    "i32.gt_s" -> (args => i32.gt_s(args(0).asOp, args(1).asOp)),
    "i32.ge_s" -> (args => i32.ge_s(args(0).asOp, args(1).asOp)),
    "i32.eqz" -> (args => i32.eqz(args(0).asOp)),
    "i32.reinterpret_f32" -> (args => i32.reinterpret_f32(args(0).asOp)),

    "i64.const" -> (args => i64.const(args(0).asImm64)),
    "i64.add" -> (args => i64.add(args(0).asOp, args(1).asOp)),
    "i64.sub" -> (args => i64.sub(args(0).asOp, args(1).asOp)),
    "i64.mul" -> (args => i64.mul(args(0).asOp, args(1).asOp)),
    "i64.div_s" -> (args => i64.div_s(args(0).asOp, args(1).asOp)),
    "i64.rem_s" -> (args => i64.rem_s(args(0).asOp, args(1).asOp)),
    "i64.shl" -> (args => i64.shl(args(0).asOp, args(1).asOp)),
    "i64.shr_s" -> (args => i64.shr_s(args(0).asOp, args(1).asOp)),
    "i64.shr_u" -> (args => i64.shr_u(args(0).asOp, args(1).asOp)),
    "i64.eq" -> (args => i64.eq(args(0).asOp, args(1).asOp)),
    "i64.ne" -> (args => i64.ne(args(0).asOp, args(1).asOp)),
    "i64.lt_s" -> (args => i64.lt_s(args(0).asOp, args(1).asOp)),
    "i64.le_s" -> (args => i64.le_s(args(0).asOp, args(1).asOp)),
    "i64.gt_s" -> (args => i64.gt_s(args(0).asOp, args(1).asOp)),
    "i64.ge_s" -> (args => i64.ge_s(args(0).asOp, args(1).asOp)),
    "i64.eqz" -> (args => i64.eqz(args(0).asOp)),
    "i64.reinterpret_f64" -> (args => i64.reinterpret_f64(args(0).asOp)),

    "f32.const" -> (args => f32.const(args(0).asImmF32)),
    "f32.add" -> (args => f32.add(args(0).asOp, args(1).asOp)),
    "f32.sub" -> (args => f32.sub(args(0).asOp, args(1).asOp)),
    "f32.mul" -> (args => f32.mul(args(0).asOp, args(1).asOp)),
    "f32.div" -> (args => f32.div(args(0).asOp, args(1).asOp)),
    "f32.min" -> (args => f32.min(args(0).asOp, args(1).asOp)),
    "f32.max" -> (args => f32.max(args(0).asOp, args(1).asOp)),
    "f32.abs" -> (args => f32.abs(args(0).asOp)),
    "f32.neg" -> (args => f32.neg(args(0).asOp)),
    "f32.sqrt" -> (args => f32.sqrt(args(0).asOp)),
    "f32.eq" -> (args => f32.eq(args(0).asOp, args(1).asOp)),
    "f32.ne" -> (args => f32.ne(args(0).asOp, args(1).asOp)),
    "f32.lt" -> (args => f32.lt(args(0).asOp, args(1).asOp)),
    "f32.le" -> (args => f32.le(args(0).asOp, args(1).asOp)),
    "f32.gt" -> (args => f32.gt(args(0).asOp, args(1).asOp)),
    "f32.ge" -> (args => f32.ge(args(0).asOp, args(1).asOp)),
    "f32.reinterpret_i32" -> (args => f32.reinterpret_i32(args(0).asOp)),

    "f64.const" -> (args => f64.const(args(0).asImmF64)),
    "f64.add" -> (args => f64.add(args(0).asOp, args(1).asOp)),
    "f64.sub" -> (args => f64.sub(args(0).asOp, args(1).asOp)),
    "f64.mul" -> (args => f64.mul(args(0).asOp, args(1).asOp)),
    "f64.div" -> (args => f64.div(args(0).asOp, args(1).asOp)),
    "f64.min" -> (args => f64.min(args(0).asOp, args(1).asOp)),
    "f64.max" -> (args => f64.max(args(0).asOp, args(1).asOp)),
    "f64.abs" -> (args => f64.abs(args(0).asOp)),
    "f64.neg" -> (args => f64.neg(args(0).asOp)),
    "f64.sqrt" -> (args => f64.sqrt(args(0).asOp)),
    "f64.eq" -> (args => f64.eq(args(0).asOp, args(1).asOp)),
    "f64.ne" -> (args => f64.ne(args(0).asOp, args(1).asOp)),
    "f64.lt" -> (args => f64.lt(args(0).asOp, args(1).asOp)),
    "f64.le" -> (args => f64.le(args(0).asOp, args(1).asOp)),
    "f64.gt" -> (args => f64.gt(args(0).asOp, args(1).asOp)),
    "f64.ge" -> (args => f64.ge(args(0).asOp, args(1).asOp)),
    "f64.reinterpret_i64" -> (args => f64.reinterpret_i64(args(0).asOp)),

    "ref.i31" -> (args => ref.i31(args(0).asOp)),

    "i31.get_s" -> (args => i31.get_s(args(0).asOp)),
    "i31.get_u" -> (args => i31.get_u(args(0).asOp)),
  )

  def empty(using Elaborator.Ctx, State): Ctx = Ctx()

  def ctx(using ctx: Ctx): Ctx = ctx

  extension (ref: CtxIdx | ValueSymbol)
    private def prettyString: Str = ref match
      case idx: CtxIdx => s"type index `${idx.toWat.mkString()}`"
      case sym: ValueSymbol => s"symbol `${sym.toString}`"
end Ctx

/** Context for [[WatBuilder]]. */
class Ctx(using Elaborator.Ctx, State) extends ToWat:

  import Ctx.prettyString

  /** The [[Elaborator.Ctx]] associated with this instance. */
  def elabCtx: Elaborator.Ctx = summon[Elaborator.Ctx]

  private val fileNames = new FileExportNames
  private val importedTypes = MutMap.empty[(ValueSymbol, Opt[Str] -> Opt[Str]), TypeIdx]
  private val pendingTypes = MutMap.empty[BaseTypeSymbol, () => TypeInfo]
  private val pendingFunctions = MutMap.empty[WasmSymbol, () => Import[ExternType.Func]]
  private val pendingGlobals = MutMap.empty[ScopedSymbol, () => Import[ExternType.Global]]

  /** File modules export every function and global, so that importing modules can link to any definition. Names are
    * allocated on first request for each symbol, kind, and identifier wrapping.
    */
  def fileExportName(sym: WasmSymbol, kind: Str, wrap: Opt[Str] -> Opt[Str])(using Raise): Str =
    fileNames(sym, kind, wrap)

  /** Capture definitions only; dependency interfaces retain ownership of imported bindings. */
  def fileInterface(classes: Vector[AbiClass], namespaces: Vector[AbiNamespace], defaultExport: Opt[BlockMemberSymbol])
        (using Raise): FileInterface =
    FileInterface(
      types.valuesIterator.map(t => AbiType(TypeIdx(t.id), t.sym, t.wrapId, t.compType, t.objectTag)).toVector,
      orderedTypeGroups.map(_.map(TypeIdx(_)).toVector).toVector,
      funcs.valuesIterator.collect:
        case f: FuncInfo => AbiFunction(f.sym, f.wrapId, f.exportName, f.typeUse.typeIdx, f.optionalParams)
      .toVector,
      globals.valuesIterator.collect:
        case g: GlobalInfo => AbiGlobal(GlobalIdx(g.id), g.sym, g.wrapId, g.exportName, g.globalType)
      .toVector,
      classes, namespaces, defaultExport,
    )

  /** Register the complete interface for lookup, without emitting unused imports or
    * reserving their WAT names. Code generation demands individual bindings; each
    * binding brings in the transitive closure of its signature/layout types. */
  def importFile(dep: FileImport)(using Ctx, Raise): (TypeRelocation, GlobalIdx => GlobalIdx) =
    val byIndex = dep.interface.types.map(t => t.index -> t).toMap
    val groupOf = dep.interface.typeGroups.flatMap(group => group.map(_ -> group)).toMap
    lazy val relocate: TypeRelocation = new TypeRelocation(index =>
      val ty = byIndex.getOrElse(index, lastWords(s"WASM interface has an unbound type edge: $index"))
      importedTypes.getOrElse(ty.sym -> ty.wrap, {
        // Recursive group membership and member order are part of Wasm type identity.
        // Demand the whole originating group, reserving every index before following edges.
        val group = groupOf.getOrElse(index, lastWords(s"WASM interface type has no group: $index"))
        val members = group.map(byIndex)
        assert(members.forall(t => !importedTypes.contains(t.sym -> t.wrap)),
          "Partially imported recursive type group")
        val indices = members.map: t =>
          val result = TypeIdx(SymIdx(typeScp.allocateOrGetNameWrapped(t.sym, t.wrap)))
          importedTypes(t.sym -> t.wrap) = result
          result
        val ids = indices.map(_.idx)
        ids.foreach(id => importedTypeGroups(id) = ids)
        members.foreach(t => addType(TypeInfo(t.sym, relocate.body(t.body), t.tag, t.wrap)))
        importedTypes(ty.sym -> ty.wrap)
      }))
    dep.interface.types.foreach: ty =>
      ty.sym match
        case sym: BaseTypeSymbol if ty.wrap == (N -> N) =>
          pendingTypes.getOrElseUpdate(sym, () => getTypeInfo_!(relocate.index(ty.index)))
        case _ => ()
    dep.interface.functions.foreach: f =>
      lazy val imported =
        val binding = Import(dep.name, f.name, ExternType.Func(TypeUse(relocate.index(f.ty)), f.sym, f.wrap))
        addFunctionImport(binding)
        binding
      pendingFunctions.getOrElseUpdate(f.sym, () => imported)
    val globals = dep.interface.globals.map: g =>
      lazy val imported =
        val binding = Import(dep.name, g.name, ExternType.Global(relocate.global(g.ty), g.sym, g.wrap))
        addGlobalImport(binding)
        binding
      val binding = pendingGlobals.getOrElseUpdate(g.sym, () => imported)
      g.index -> (() => GlobalIdx(binding().externType.id))
    .toMap
    (relocate, index => globals.getOrElse(index,
      lastWords(s"WASM interface has an unbound global edge: $index"))())

  /** [[Scope]] for generating WAT identifiers of types. */
  private[text] val typeScp = new WasmScope

  /** [[ListMap]] containing all type definitions in the module mapped by their symbolic identifiers. */
  private var types = ListMap.empty[SymIdx, TypeInfo]

  /** Imported recursive groups retain their originating member order. */
  private val importedTypeGroups = MutMap.empty[SymIdx, Vector[SymIdx]]

  /** [[MutMap]] containing type symbols mapped to their corresponding [[TypeInfo]] instance. */
  private val namedTypes = MutMap.empty[TypeKey, TypeInfo]
  
  /** [[Scope]] for generating WAT identifiers of data segments. */
  private[text] val dataSegmentScp = new WasmScope

  /** [[ListMap]] containing all data segments in the module. */
  private var dataSegments = ListMap.empty[SymIdx, DataSegment]
  
  /** [[Scope]] for generating WAT identifiers of element segments. */
  private[text] val elemSegmentScp = new WasmScope

  /** [[ListMap]] containing all element segments in the module. */
  private var elemSegments = ListMap.empty[SymIdx, ElemSegment]

  /** [[Scope]] for generating WAT identifiers of functions. */
  private[text] val funcScp = new WasmScope

  /** [[ListMap]] containing all function definitions and imports in the module mapped by their symbolic identifiers. */
  private var funcs = ListMap.empty[SymIdx, FuncInfo | Import[ExternType.Func]]

  /** [[MutMap]] containing function symbols mapped to the corresponding [[FuncInfo]] or [[Import]] instance. */
  private val namedFuncs = MutMap.empty[WasmSymbol, FuncInfo | Import[ExternType.Func]]

  /** [[Scope]] for generating WAT identifiers of memories. */
  private[text] val memoryScp = new WasmScope

  /** [[ListMap]] containing all memory definitions and imports in the module mapped by their symbolic identifiers. */
  private var memories = ListMap.empty[SymIdx, MemInfo | Import[ExternType.Mem]]
  
  /** [[Scope]] for generating WAT identifiers of tags. */
  private[text] val tagScp = new WasmScope

  /** [[ListMap]] containing all tag definitions in the module. */
  private var tags = ListMap.empty[SymIdx, TagInfo | Import[ExternType.Tag]]

  /** [[Scope]] for generating WAT identifiers of globals. */
  private[text] val globalScp = new WasmScope

  /** [[ListMap]] containing all global definitions and imports in the module. */
  private var globals = ListMap.empty[SymIdx, GlobalInfo | Import[ExternType.Global]]

  /** [[MutMap]] containing global symbols mapped to their corresponding [[GlobalInfo]] or [[Import]] instance. */
  private val namedGlobals = MutMap.empty[ScopedSymbol, GlobalInfo | Import[ExternType.Global]]

  /** Counter for generating object tags. */
  private var objectTagNum = 0

  private val wasmIntrinsicFuncs = MutMap.empty[Str, FuncIdx]
  private val wasmIntrinsicTypes = MutMap.empty[WasmIntrinsicType, TypeIdx]
  private val wasmIntrinsicTags = MutMap.empty[Str, TagIdx]

  private val cachedMemoryImport = MutMap.empty[(Str, Str), SymIdx]
  private val cachedFunctionImports = MutMap.empty[(Str, Str), FuncIdx]

  private val singletons = MutMap.empty[ModuleOrObjectSymbol, () => Ctx.SingletonInfo]
  private val virtualTables = MutMap.empty[BaseTypeSymbol, () => Ctx.VirtualTable]
  private def imports: Seq[Import[?]] =
    val importedFuncs = funcs.collect:
      case (_, imp: Import[ExternType.Func]) => imp
    val importedGlobals = globals.collect:
      case (_, imp: Import[ExternType.Global]) => imp
    val importedMems = memories.collect:
      case (_, imp: Import[ExternType.Mem]) => imp
    val importedTags = tags.valuesIterator.collect:
      case imp @ Import(_, _, _: ExternType.Tag) => imp
    (importedFuncs ++ importedGlobals ++ importedMems).toSeq ++ importedTags

  private def globalExternType(
      globalEntry: GlobalInfo | Import[ExternType.Global],
  )(using Ctx, Raise): ExternType.Global =
    globalEntry match
      case globalInfo: GlobalInfo => ExternType.Global(globalInfo.globalType, globalInfo.sym, globalInfo.wrapId)
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
      case key: TypeKey => namedTypes(key) = typeInfo
      case _ =>
    TypeIdx(id)

  /** Returns the [[TypeIdx]] of the given `typeref`.
    */
  def getType(typeref: TypeIdx | TypeKey): Opt[TypeIdx] = typeref match
    case typeidx: TypeIdx => S(typeidx)
    case sym: TypeKey => getTypeInfo(typeref).map(ti => TypeIdx(ti.id))

  /** Same as [[getType]] but throws an exception when the `typeref` is not found. */
  def getType_!(typeref: TypeIdx | TypeKey): TypeIdx =
    getType(typeref).getOrElse:
      lastWords(s"Missing type definition for ${typeref.prettyString}")

  /** Returns the [[TypeInfo]] instance associated with the given `typeref`. */
  def getTypeInfo(typeref: TypeIdx | TypeKey): Opt[TypeInfo] = typeref match
    case TypeIdx(idx @ SymIdx(nme)) => types.get(idx)
    case sym: BaseTypeSymbol => namedTypes.get(sym).orElse(pendingTypes.get(sym).map(_()))
    case sym: BlockMemberSymbol => namedTypes.get(sym)

  /** Same as [[getTypeInfo]] but throws an exception when the `typeref` is not found. */
  def getTypeInfo_!(typeref: TypeIdx | TypeKey): TypeInfo =
    getTypeInfo(typeref).getOrElse:
      lastWords(s"Missing type definition for ${typeref.prettyString}")

  /** Records the derived virtual-dispatch layout for `sym`. */
  def registerVirtualTable(sym: BaseTypeSymbol, info: => Ctx.VirtualTable): Unit =
    lazy val cached = info
    virtualTables(sym) = () => cached

  /** Returns the derived virtual-dispatch layout for `sym`. */
  def getVirtualTable(sym: BaseTypeSymbol): Opt[Ctx.VirtualTable] =
    virtualTables.get(sym).map(_())

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
            Import(
              module,
              name,
              ExternType.Mem(MemType(Limits(minPages)), sym = TempSymbol(N, initErasedType = N, name)),
            ))
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
  def addTagImport(imp: Import[ExternType.Tag]): TagIdx =
    tags += imp.externType.id -> imp
    TagIdx(imp.externType.id)

  def addTag(tagInfo: TagInfo): TagIdx =
    val id = tagInfo.id
    tags = tags + (id -> tagInfo)
    TagIdx(id)

  /** Adds a function into this context. */
  def addFunc(funcInfo: FuncInfo)(using Ctx, Raise): FuncIdx =
    val id = funcInfo.id
    funcs = funcs + (id -> funcInfo)
    namedFuncs(funcInfo.sym) = funcInfo
    val idx = FuncIdx(funcInfo.id)
    val refType = RefType(funcInfo.typeUse.typeIdx, nullable = false)
    elemSegments = elemSegments +
      (id -> ElemSegment.Declare(refType -> Seq(ref.func(idx, refType)), funcInfo.sym, funcInfo.wrapId))
    idx

  /** Returns the [[FuncIdx]] of the given `funcref`.
    */
  def getFunc(funcref: FuncIdx | WasmSymbol): Opt[FuncIdx] = funcref match
    case idx: FuncIdx => S(idx)
    case sym: WasmSymbol =>
      getFuncEntry(sym).map:
        case fi: FuncInfo => FuncIdx(fi.id)
        case imp: Import[ExternType.Func] => FuncIdx(imp.externType.id)

  /** Same as [[getFunc]] but throws an exception when the `funcref` is not found. */
  def getFunc_!(funcref: FuncIdx | WasmSymbol): FuncIdx =
    getFunc(funcref).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  private def getFuncEntry(funcref: FuncIdx | WasmSymbol): Opt[FuncInfo | Import[ExternType.Func]] = funcref match
    case FuncIdx(idx @ SymIdx(_)) => funcs.get(idx)
    case funcref: WasmSymbol => namedFuncs.get(funcref).orElse(pendingFunctions.get(funcref).map(_()))

  /** Returns the [[FuncInfo]] instance associated with the given `funcref`. */
  def getFuncInfo(funcref: FuncIdx | WasmSymbol): Opt[FuncInfo] =
    getFuncEntry(funcref).collect:
      case funcInfo: FuncInfo => funcInfo

  /** Same as [[getFuncInfo]] but throws an exception when the `funcref` is not found. */
  def getFuncInfo_!(funcref: FuncIdx | WasmSymbol): FuncInfo =
    getFuncInfo(funcref).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  /** Returns the type use associated with the given `funcref`, whether it is a definition or an import. */
  def getFuncTypeUse(funcref: FuncIdx | WasmSymbol): Opt[TypeUse] =
    getFuncEntry(funcref).map:
      case funcInfo: FuncInfo => funcInfo.typeUse
      case funcImport: Import[ExternType.Func] => funcImport.externType.typeUse

  /** Same as [[getFuncTypeUse]] but throws an exception when the `funcref` is not found. */
  def getFuncTypeUse_!(funcref: FuncIdx | WasmSymbol): TypeUse =
    getFuncTypeUse(funcref).getOrElse:
      lastWords(s"Missing function definition for ${funcref.prettyString}")

  /** Returns the [[GlobalIdx]] of the given `globalref`. */
  def getGlobal(globalref: GlobalIdx | ScopedSymbol)(using Ctx, Raise): Opt[GlobalIdx] = globalref match
    case globalidx: GlobalIdx => S(globalidx)
    case sym: ScopedSymbol =>
      getGlobalEntry(sym).map: globalEntry =>
        GlobalIdx(globalExternType(globalEntry).id)

  /** Same as [[getGlobal]] but throws an exception when the `globalref` is not found. */
  def getGlobal_!(globalref: GlobalIdx | ScopedSymbol)(using Ctx, Raise): GlobalIdx =
    getGlobal(globalref).getOrElse:
      lastWords(s"Missing global definition for ${globalref.prettyString}")

  private def getGlobalEntry(globalref: GlobalIdx | ScopedSymbol): Opt[GlobalInfo | Import[ExternType.Global]] =
    globalref match
      case GlobalIdx(idx @ SymIdx(_)) => globals.get(idx)
      case sym: ScopedSymbol => namedGlobals.get(sym).orElse(pendingGlobals.get(sym).map(_()))

  /** Returns the global extern metadata associated with the given `globalref`. */
  def getGlobalType(globalref: GlobalIdx | ScopedSymbol)(using Ctx, Raise): Opt[ExternType.Global] =
    getGlobalEntry(globalref).map(globalExternType)

  /** Same as [[getGlobalType]] but throws an exception when the `globalref` is not found. */
  def getGlobalType_!(globalref: GlobalIdx | ScopedSymbol)(using Ctx, Raise): ExternType.Global =
    getGlobalType(globalref).getOrElse:
      lastWords(s"Missing global definition for ${globalref.prettyString}")

  /** Returns the [[GlobalInfo]] instance associated with the given `globalref` when it is a definition. */
  def getGlobalInfo(globalref: GlobalIdx | ScopedSymbol): Opt[GlobalInfo] =
    getGlobalEntry(globalref).collect:
      case globalInfo: GlobalInfo => globalInfo

  /** Same as [[getGlobalInfo]] but throws an exception when the `globalref` is not found. */
  def getGlobalInfo_!(globalref: GlobalIdx | ScopedSymbol): GlobalInfo =
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
  def containsGlobal(sym: ScopedSymbol): Bool = namedGlobals.contains(sym) || pendingGlobals.contains(sym)
  
  /** Returns all globals in this context. */
  def getGlobals: Seq[ScopedSymbol] = namedGlobals.keys.toSeq

  /** Checks whether singleton metadata has been registered for object symbol `sym`. */
  def containsSingleton(sym: ModuleOrObjectSymbol): Bool = singletons.contains(sym)

  /** Returns singleton metadata for `sym` when it denotes a registered singleton object. */
  def getSingletonInfo(sym: InnerSymbol): Opt[Ctx.SingletonInfo] = sym match
    case obj: ModuleOrObjectSymbol => singletons.get(obj).map(_())
    case _ => N

  /** Registers singleton metadata for object symbol `sym`.
    * Delay resolving imported storage and its types until the singleton is actually used.
    */
  def registerSingleton(sym: ModuleOrObjectSymbol, info: => Ctx.SingletonInfo): Unit =
    lazy val cached = info
    singletons(sym) = () => cached

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

  /** Order all type definitions by their dependencies, including lazy imports demanded
    * after local class placeholders. Imported recursive groups are indivisible: changing
    * their member order changes Wasm type identity and would break cross-instance linking.
    * Local cycles form new groups, with superclasses before subclasses within each group.
    */
  private def orderedTypeGroups: Ls[Ls[SymIdx]] =
    def parents(id: SymIdx): Ls[SymIdx] = types(id).compType match
      case st: StructType => st.parents.map(_.idx).toList
      case _ => Nil
    def references(ty: ValType): Ls[SymIdx] = ty match
      case RefType(idx: TypeIdx, _) => idx.idx :: Nil
      case _ => Nil
    def dependencies(id: SymIdx): Ls[SymIdx] = types(id).compType match
      case st: StructType => parents(id) ++ st.fields.toList.flatMap(f => references(f._2.ty))
      case ArrayType(elem, _) => references(elem)
      case FunctionType(SignatureType(params, results)) =>
        params.toList.flatMap(p => references(p.valtype)) ++ results.toList.flatMap(r => references(r.valtype))
    def groupHead(id: SymIdx): SymIdx = importedTypeGroups.get(id).fold(id)(_.head)
    def groupMembers(id: SymIdx): Ls[SymIdx] = importedTypeGroups.get(id).fold(id :: Nil)(_.toList)
    def groupDependencies(id: SymIdx): Ls[SymIdx] =
      groupMembers(id).flatMap(dependencies).map(groupHead).filterNot(_ == id).distinct
    val roots = types.keysIterator.map(groupHead).toVector.distinct
    SccAnalysis.sccsFrom(groupDependencies, roots).map: component =>
      component match
        case id :: Nil if importedTypeGroups.contains(id) => groupMembers(id)
        case _ =>
          assert(component.forall(id => !importedTypeGroups.contains(id)),
            "An imported recursive group cannot depend on local type definitions")
          val members = component.toSet
          SccAnalysis.sccsFrom((id: SymIdx) => parents(id).filter(members), component).flatMap: inheritanceComponent =>
            assert(inheritanceComponent.size === 1 && !parents(inheritanceComponent.head).contains(inheritanceComponent.head),
              s"Cyclic superclass dependencies in recursive type group: $inheritanceComponent")
            inheritanceComponent
  end orderedTypeGroups

  def toWat: Document =
    val definedGlobals = globals.valuesIterator.collect:
      case globalInfo: GlobalInfo => globalInfo.toWat
    val memDefns = memories.valuesIterator.collect:
      case memInfo: MemInfo => memInfo.toWat
    val funcDefns = funcs.valuesIterator.collect:
      case funcInfo: FuncInfo => funcInfo.toWat
    val typeDefns = orderedTypeGroups.map:
      case id :: Nil => types(id).toWat
      case component => doc"(rec #{  # ${component.map(types(_).toWat).mkDocument(doc" # ")} #} )"
    doc"(module #{  # ${
        (
          typeDefns
            ++ imports.iterator.map(_.toWat)
            ++ tags.valuesIterator.collect { case t: TagInfo => t.toWat }
            ++ definedGlobals
            ++ memDefns
            ++ funcDefns
            ++ dataSegments.valuesIterator.map(_.toWat)
            ++ elemSegments.valuesIterator.map(_.toWat)
        ).toSeq.mkDocument(doc" # ")
      } #} )"
  end toWat

end Ctx
