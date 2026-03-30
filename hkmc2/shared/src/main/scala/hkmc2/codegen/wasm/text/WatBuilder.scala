package hkmc2
package codegen
package wasm
package text

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import document.*
import document.Document
import js.CodeBuilder
import semantics.*, Elaborator.State
import syntax.Tree.{BoolLit, IntLit, StrLit, Ident}
import text.Param as WasmParam
import Message.MessageContext
import Scope.scope

import scala.collection.mutable.{ArrayBuffer as ArrayBuf, LinkedHashMap}
import scala.util.boundary, boundary.break
import sourcecode.Line

extension (instr: FoldedInstr)
  /** Returns the mneomic prefix of this instruction.
    *
    * For example, for `local.get` it returns `Some("local")`, and for `nop` it returns `None`.
    */
  private def mnemonicPrefix: Opt[Str] =
    instr.mnemonic.split('.').optionUnless(_.size == 1).map(_.head)

object WatBuilder:
  object ExternIntrinsics:
    val SystemModule = "system"
    val SystemMemoryImportName = "mem"
    val StringFromUtf16ImportName = "mlx_str_from_utf16"
    val WasmPageSizeBytes = 65536

class WatBuilder(using TraceLogger, State) extends CodeBuilder:
  import Ctx.ctx
  import Ctx.{SingletonInfo, binaryOps, unaryOps, wasmIntrinsicArities, wasmIntrinsicNameSet}
  import Instructions.{block as blockInstr, *}
  import WatBuilder.ExternIntrinsics

  type Context = Ctx

  private val baseObjectSym: BlockMemberSymbol = BlockMemberSymbol("Object", Nil)
  private val tagFieldSym: TermSymbol = TermSymbol(syntax.MutVal, owner = N, Ident("$tag"))

  private case class StringLitInfo(offset: Int, byteLen: Int, watBytes: Str)
  private val stringLits: LinkedHashMap[Str, StringLitInfo] = LinkedHashMap.empty
  private var nextStringDataOffset: Int = 0

  private def baseObjectTypeIdx(using Ctx): TypeIdx =
    ctx.getType_!(baseObjectSym)

  private def baseObjectStruct(using Ctx): StructType =
    ctx.getTypeInfo_!(baseObjectSym).compType match
      case struct: StructType => struct
      case other => lastWords(s"Base Object type must be a struct, found ${other.toWat.mkString()}")

  private def baseObjectRefType(nullable: Bool)(using Ctx): RefType =
    RefType(baseObjectTypeIdx, nullable = nullable)

  /** True if this top-level class can be declared as a Wasm struct type. */
  private def isSupportedTopLevelClass(defn: ClsLikeDefn): Bool =
    defn.owner.isEmpty
      && ((defn.k is syntax.Cls) || (defn.k is syntax.Obj))
      && defn.auxParams.isEmpty
      && defn.parentPath.isEmpty
      && defn.methods.isEmpty
      && defn.companion.isEmpty
      && (defn.preCtor match
        case End(_) => true
        case _ => false)

  /** Returns singleton metadata when `sym` resolves to a registered singleton object. */
  private def singletonInfoFor(sym: Local)(using Ctx): Opt[SingletonInfo] =
    ctx.getSingletonInfo(sym)

  /** Loads the singleton object reference from its backing mutable global. */
  private def singletonGlobalGet(info: SingletonInfo): Expr =
    global.get(GlobalIdx(SymIdx(info.globalName)), info.globalTy)

  /** The runtime representation of Unit as a singleton object. */
  private lazy val syntheticUnitDefn: ClsLikeDefn =
    ClsLikeDefn(
      owner = N,
      isym = State.unitSymbol,
      sym = BlockMemberSymbol("Unit", Nil),
      ctorSym = N,
      k = syntax.Obj,
      paramsOpt = N,
      auxParams = Nil,
      parentPath = N,
      methods = Nil,
      privateFields = Nil,
      publicFields = Nil,
      preCtor = End(""),
      ctor = End(""),
      companion = N,
      bufferable = N,
    )

  /** Registers the synthetic `Unit` singleton. */
  private def RegisterUnitSingleton()(using Ctx, Raise, Scope): Unit =
    val unitDefn = syntheticUnitDefn
    if ctx.containsSingleton(unitDefn.sym) then return

    if ctx.getType(unitDefn.sym).isEmpty then
      createDefnTypes(Define(unitDefn, End("")))

    ctx.pushLocal()
    returningTerm(Define(unitDefn, End("")))
    ctx.popLocal()

  /** Registers eager singleton runtime state by creating its global and start-init action. */
  private def registerSingletonInit(clsLikeDefn: ClsLikeDefn, typeref: TypeIdx)(using Ctx, Raise, Scope): Unit =
    if ctx.containsSingleton(clsLikeDefn.sym) then return

    val globalSym = BlockMemberSymbol(s"${clsLikeDefn.sym.nme}$$inst", Nil, nameIsMeaningful = false)
    val globalName = scope.allocateName(globalSym)
    val globalTy = RefType(typeref, nullable = true)
    val info = SingletonInfo(globalName, globalTy)
    val singletonOwner = clsLikeDefn.isym match
      case mos: ModuleOrObjectSymbol => S(mos)
      case _ => N
    ctx.registerSingleton(clsLikeDefn.sym, singletonOwner, info)

    val globalIdx = ctx.addGlobal(
      globalSym,
      GlobalInfo(
        id = SymIdx(globalName),
        valType = globalTy,
        mutable = true,
        init = ref.`null`(typeref),
      ),
    )

    val ctorCall = call(
      funcidx = ctx.getFunc_!(clsLikeDefn.sym),
      operands = Seq.empty,
      returnTypes = Seq(Result(RefType.anyref)),
    )
    ctx.addSingletonInitAction(global.set(globalIdx, ref.cast(ctorCall, globalTy)))
  end registerSingletonInit

  /** Recursively declares supported top-level class types (needed for nested function codegen). */
  private def createDefnTypes(b: Block)(using Ctx, Raise, Scope): Unit = b match
    case Define(defn: ClsLikeDefn, rst) =>
      if isSupportedTopLevelClass(defn) then
        val inheritedFields = baseObjectStruct.fields
        val inheritedSize = inheritedFields.size

        val classFields = (defn.publicFields.map(_._2) ++ defn.privateFields)
          .map: f =>
            f -> Field(RefType.anyref, mutable = true, id = SymIdx(f.nme))

        val allFields = inheritedFields ++ classFields

        // Only parent is base Object for now. For general inheritance add other parents.
        ctx.addType(
          sym = S(defn.sym),
          typeInfo = TypeInfo(
            sym = defn.sym,
            compType = StructType(fields = allFields, parents = Seq(baseObjectTypeIdx), isSubtype = true),
            objectTag = S(ctx.getFreshObjectTag()),
          ),
        )
      end if
      createDefnTypes(rst)
    case Define(_, rst) =>
      createDefnTypes(rst)
    case Match(_, arms, dflt, rst) =>
      arms.foreach((_, body) => createDefnTypes(body))
      dflt.foreach(createDefnTypes)
      createDefnTypes(rst)
    case Begin(_, rst) =>
      createDefnTypes(rst)
    case TryBlock(_, _, rst) =>
      createDefnTypes(rst)
    case Assign(_, _, rst) =>
      createDefnTypes(rst)
    case af @ AssignField(_, _, _, rst) =>
      createDefnTypes(rst)
    case AssignDynField(_, _, _, _, rst) =>
      createDefnTypes(rst)
    case HandleBlock(_, _, _, _, _, _, _, rst) =>
      createDefnTypes(rst)
    case Label(_, _, body, rst) =>
      createDefnTypes(body)
      createDefnTypes(rst)
    case Scoped(_, body) =>
      createDefnTypes(body)
    case _: BlockTail => ()

  /** Gets (and caches) the exception tag used for MLX `throw`. */
  private def exnTagIdx(using Ctx, Raise, Scope): TagIdx =
    val symNme = scope.allocateName(TempSymbol(N, "mlx_exn"))
    ctx.getOrCreateWasmIntrinsicTag(
      "mlx_exn",
      ctx.addTag(TagInfo(
        id = SymIdx("mlx_exn"),
        typeIdx = ctx.addType(
          sym = N,
          TypeInfo(
            id = SymIdx(symNme),
            FunctionType(params = Seq(WasmParam(N, RefType.anyref)), results = Seq.empty),
            objectTag = S(ctx.getFreshObjectTag()),
          ),
        ),
      )),
    )

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
  private def getOrLoadStrCtorFunction(using Ctx, Raise, Scope): FuncIdx =
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
      val importTyNme = scope.allocateName(TempSymbol(N, ExternIntrinsics.StringFromUtf16ImportName))
      val importTy = ctx.addType(
        sym = N,
        TypeInfo(
          id = SymIdx(importTyNme),
          FunctionType(
            params = Seq(WasmParam(N, RefType.anyref), WasmParam(N, RefType.anyref)),
            results = Seq(Result(RefType.anyref)),
          ),
          objectTag = N,
        ),
      )
      FuncImport(
        module = ExternIntrinsics.SystemModule,
        name = ExternIntrinsics.StringFromUtf16ImportName,
        id = SymIdx(ExternIntrinsics.StringFromUtf16ImportName),
        typeIdx = importTy,
      )
  end getOrLoadStrCtorFunction

  /** Gets (and caches) the Wasm GC array type used for tuples (`mut` selects mutability).
    */
  private def tupleArrayType(mut: Bool)(using Ctx, Raise, Scope): TypeIdx =
    ctx.getOrCreateWasmIntrinsicType(WasmIntrinsicType.TupleArray(mutable = mut)):
      val suffix = if mut then "Mut" else ""
      val sym = BlockMemberSymbol(s"TupleArray$suffix", Nil)
      ctx.addType(
        sym = S(sym),
        TypeInfo(
          sym,
          ArrayType(elemType = RefType.anyref, mutable = mut),
          objectTag = N,
        ),
      )

  /** Allocates a fresh temp local (typed `anyref`) and returns its `LocalIdx`.
    */
  private def mkTempLocal(base: Str)(using Ctx, Scope, Raise): LocalIdx =
    val sym = TempSymbol(N, base)
    val nme = scope.allocateName(sym)
    ctx.addLocal(sym)
    LocalIdx(SymIdx(nme))

  /** Binds constructor self (`thisSym`) to the Wasm local name `this` in the current scope/context.
    */
  private def bindCtorThis(thisSym: Local)(using Ctx, Raise, Scope): LocalIdx -> Str =
    val thisName = "this"
    scope.lookup(thisSym) match
      case S(`thisName`) => ()
      case _ => scope.addToBindings(thisSym, thisName, shadow = true)
    if !ctx.containsLocal(thisSym) then
      ctx.addLocal(thisSym)
    LocalIdx(SymIdx(thisName)) -> thisName

  /** Compiles a class/object constructor body under its own Wasm-local frame.
    */
  private def setupCtorLocals(
      clsLikeDefn: ClsLikeDefn,
  )(using Ctx, Raise, Scope): (Seq[Local -> Str], LocalIdx, Expr, Seq[Local -> Str]) =
    ctx.pushLocal()
    val clsParams = clsLikeDefn.paramsOpt.fold(Nil)(_.paramSyms)
    val ctorParams = clsParams.map: p =>
      ctx.addLocal(p)
      p -> scope.allocateName(p)
    val (thisVar, thisVarName) = bindCtorThis(clsLikeDefn.isym)
    val (ctorWat, ctorLocals) = block(clsLikeDefn.ctor)
    val localsWithNames = (clsLikeDefn.isym -> thisVarName) +: ctorLocals.map(l => l -> scope.lookup_!(l, l.toLoc))
    ctx.popLocal()
    (ctorParams, thisVar, ctorWat, localsWithNames)

  /** Returns locals allocated during codegen (e.g., temp locals). */
  private def getExtraLocals(using Ctx): Seq[Local] =
    ctx.getWasmLocals._2.getOrElse(Seq.empty)

  /** Converts expression result types to WAT result clauses, dropping unreachable types. */
  private def resultClauses(expr: Expr): Seq[Result] =
    if expr.resultTypes.exists(_ is UnreachableType) then Seq.empty
    else expr.resultTypes.map(ty => Result(ty.asValType_!))

  /** Normalizes the exported `entry` body so it always returns single result. */
  private def normalizeEntryExpr(expr: Expr, isAbortive: Bool)(using Ctx, Raise, Scope): Expr =
    if expr.resultTypes.isEmpty && !isAbortive then
      blockInstr(
        label = N,
        children = Seq(expr, result(Value.Ref(State.unitSymbol))),
        resultTypes = Seq(Result(RefType.anyref)),
      )
    else
      expr

  /** Validates an IntLit value fits signed 32-bit and delegates codegen to `onValid`.
    */
  private def withValidIntLit(
      value: BigInt,
      loc: Opt[Loc],
  )(onValid: Int => Expr)(using Ctx, Raise, Line): Expr =
    if value.isValidInt then onValid(value.toInt)
    else
      errExpr(
        Ls(msg"WatBuilder::IntLit lowering with value outside signed 32-bit range not implemented yet" -> loc),
        extraInfo = S(value.toString),
      )

  /** Emits a tuple element load that works for both mutable and immutable tuple arrays.
    */
  private def tupleArrayGet(tupleExpr: Expr, idxBuilder: Expr => Expr)(using Ctx, Raise, Scope): Expr =
    val elemType = RefType.anyref
    val mutArrayType = tupleArrayType(true)
    val immArrayType = tupleArrayType(false)
    val tupleTmp = mkTempLocal("tuple")
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
  )(using Ctx, Raise, Scope): Expr => Expr =
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

        val idxTmp = mkTempLocal("idx")

        tupleRef =>
          val storeIdx = local.set(idxTmp, ref.i31(idxI32))
          def idxVal: Expr = i31.get(ref.cast(local.get(idxTmp, RefType.anyref), RefType.i31ref), signed = true)

          val normalizedIdx = `if`(
            condition = i32.lt_s(idxVal, i32.const(0)),
            ifTrue = i32.add(idxVal, array.len(tupleRef)),
            ifFalse = S(idxVal),
            resultTypes = Seq(Result(I32Type)),
          )

          blockInstr(
            label = N,
            children = Seq(storeIdx, normalizedIdx),
            resultTypes = Seq(Result(I32Type)),
          )

  /** Raises a [[WarningReport]] with the given `warnMsgs` and `extraInfo`, and emits the `defaultValue` instruction.
    */
  def warnExpr(
      warnMsgs: Ls[Message -> Opt[Loc]],
      extraInfo: Opt[Any] = N,
  )(defaultValue: => FoldedInstr = unreachable)(using Ctx, Raise)(using Line): Expr =
    raise(WarningReport(warnMsgs, source = Diagnostic.Source.Compilation, extraInfo = extraInfo))
    defaultValue

  /** Raises an [[ErrorReport]] with the given `warnMsgs` and `extraInfo`, and emits an `unreachable` instruction.
    */
  def errExpr(
      errMsgs: Ls[Message -> Opt[Loc]],
      extraInfo: => Opt[Any] = N,
  )(using Ctx, Raise)(using Line): Expr =
    raise(ErrorReport(errMsgs, source = Diagnostic.Source.Compilation, extraInfo = extraInfo))
    unreachable

  def getVar(l: Local, loc: Opt[Loc])(using Ctx, Raise, Scope): Expr =
    singletonInfoFor(l) match
      case S(info) => singletonGlobalGet(info)
      case N => l match
          case ts: semantics.TermSymbol =>
            errExpr(
              Ls(msg"WatBuilder::getVar for TermSymbol not implemented yet" -> l.toLoc),
              extraInfo = S(ts.toString),
            )
          case ts: semantics.ModuleOrObjectSymbol if ts.asMod.isDefined =>
            errExpr(
              Ls(
                msg"WatBuilder::getVar for ModuleOrObjectSymbol (`ts.asMod.isDefined`) not implemented yet" -> l.toLoc,
              ),
              extraInfo = S(ts.toString),
            )
          case ts: semantics.InnerSymbol =>
            if !ctx.containsLocal(l) then
              return errExpr(
                Ls(
                  msg"WatBuilder::getVar for InnerSymbol (symbol not in top-level scope) not implemented yet" ->
                    ts.toLoc,
                ),
                extraInfo = S(
                  s"Block IR: `${ts.toString}`\nScope: ${scope.toString}\nWasm Locals: ${ctx.getAllWasmLocals.toString}",
                ),
              )
            local.get(LocalIdx(SymIdx(scope.lookup_!(ts, ts.toLoc))), RefType.anyref)
          case l =>
            if ctx.containsLocal(l) then
              local.get(LocalIdx(SymIdx(scope.lookup_!(l, l.toLoc))), RefType.anyref)
            else if ctx.containsGlobal(l) then
              global.get(GlobalIdx(SymIdx(scope.lookup_!(l, l.toLoc))), RefType.anyref)
            else
              errExpr(
                Ls(
                  msg"WatBuilder::getVar for ${
                      l.getClass.getSimpleName
                    } (symbol not in top-level scope) not implemented yet" ->
                    l.toLoc,
                ),
                extraInfo = S(
                  s"Block IR: `${l.toString}`\nScope: ${scope.toString}\nWasm Locals: ${ctx.getAllWasmLocals.toString}",
                ),
              )
  end getVar

  def argument(a: Arg)(using Ctx, Raise, Scope): Expr =
    if a.spread.nonEmpty then
      errExpr(
        Ls(msg"WatBackend::argument for spread expression not implemented yet" -> a.value.toLoc),
        extraInfo = S(a.showAsTree),
      )
    else result(a.value)

  def operand(a: Arg)(using Ctx, Raise, Scope): Expr =
    if a.spread.nonEmpty then die else subexpression(a.value)

  def subexpression(r: codegen.Result)(using Ctx, Raise, Scope): Expr = r match
    case r: Lambda =>
      errExpr(
        Ls(msg"WatBuilder::subexpression for Lambda not implemented yet" -> r.toLoc),
        extraInfo = S(r.showAsTree),
      )
    case r => result(r)

  def fieldSelect(
      thisSym: BlockMemberSymbol,
      sym: DefinitionSymbol[?],
  )(using Ctx, Raise): FieldIdx =
    val structInfo = ctx.getTypeInfo_!(thisSym)
    val symToField = structInfo.compType match
      case ty: StructType => ty.fieldsBySym
      case _ => lastWords(s"Cannot select field from non-struct type: ${structInfo.compType.toWat}")
    val fieldIdx = symToField.get(sym)
      .orElse:
        // Workaround: TermSymbols are not correctly resolved, so match the fields by name instead
        sym match
          case trmSym: TermSymbol if trmSym.owner.flatMap(_.asBlkMember).exists(_ == thisSym) =>
            symToField.find((fieldSym, _) => fieldSym.nme == sym.nme).map((_, v) => v)
          case _ => N
      .map(_.id)
    FieldIdx(
      fieldIdx getOrElse:
        lastWords(
          s"Missing field `${sym.toString}` in struct `${thisSym.toString}` with type `${structInfo.toWat.mkString()}`",
        ),
    )
  end fieldSelect

  def result(r: codegen.Result)(using Ctx, Raise, Scope): Expr = r match
    case Value.This(sym) =>
      // TODO(Derppening): Add type tracking and refinement for locals, remove the `ref.cast`
      ref.cast(
        local.get(LocalIdx(SymIdx(scope.lookup_!(sym, sym.toLoc))), RefType.anyref),
        RefType(
          sym.asBlkMember.fold(baseObjectTypeIdx)(ctx.getType_!(_)),
          nullable = false,
        ),
      )
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
    case Value.Ref(l, disamb) =>
      if (l is State.unitSymbol) || disamb.contains(State.unitSymbol) then
        RegisterUnitSingleton()
      singletonInfoFor(l) match
        case S(info) => singletonGlobalGet(info)
        case N =>
          ctx.getFunc(l) match
            case S(funcIdx) => ref.func(funcIdx, RefType(ctx.getFuncInfo_!(l).typeIdx, nullable = false))
            case N => getVar(l, r.toLoc)

    case Call(Value.Ref(l: BuiltinSymbol, _), lhs :: rhs :: Nil) if !l.functionLike =>
      if l.binary then
        errExpr(
          Ls(
            msg"WatBuilder::result encountered builtin '${
                l.nme
              }' which should be lowered to an intrinsic function" ->
              r.toLoc,
          ),
          extraInfo = S(r.toString),
        )
      else
        errExpr(Ls(msg"Cannot call non-binary builtin symbol '${l.nme}'" -> r.toLoc))

    case c @ Call(fun, args) =>
      wasmIntrinsicName(fun) match
        case S(intrName) =>
          val expectedArity = wasmIntrinsicArities(intrName)
          if expectedArity =/= args.length then
            return errExpr(
              Ls(msg"Wasm intrinsic '$intrName' called with incorrect arity (${args.length})" -> c.toLoc),
              extraInfo = S(c.toString),
            )
          val funcIdx = getIntrinsic(intrName)
          call(
            funcidx = funcIdx,
            operands = args.map(argument),
            returnTypes = Seq(Result(RefType.anyref)),
          )
        case N =>
          val base = subexpression(fun)
          if base.resultTypes.exists(_ is UnreachableType) then return base
          val wasmArgs = args.map(argument)

          val baseTypeIdx = base.resultType match
            case S(RefType(idx: TypeIdx, _)) => idx
            case ty =>
              return errExpr(
                Ls(msg"Expected WAT of `fun` expression in Call(...) to have a `(ref <typeidx>)` type" -> r.toLoc),
                extraInfo = S(
                  s"Block IR: `${
                      fun.toString
                    }`\nCompiled WAT: `${
                      base.toWat.toString
                    }`\n... which has type `${
                      ty.fold("(none)")(_.toWat.toString)
                    }`",
                ),
              )
          val baseTypeInfo = ctx.getTypeInfo_!(baseTypeIdx)

          call_ref(
            target = base,
            operands = wasmArgs.toSeq,
            typeIdx = baseTypeIdx,
            funcType = baseTypeInfo.compType.asInstanceOf[FunctionType],
          )

    case sel @ Select(qual, id) =>
      sel.symbol match
        case S(selObj: ModuleOrObjectSymbol) =>
          if selObj is State.unitSymbol then
            RegisterUnitSingleton()
          singletonInfoFor(selObj) match
            case S(info) => singletonGlobalGet(info)
            case N =>
              errExpr(
                Ls(msg"WatBuilder::result for object selection `${id.name}` not implemented yet" -> sel.toLoc),
                extraInfo = S(sel),
              )

        case S(selSym: TermSymbol) =>
          val qualRes = result(qual)
          val selOwner = selSym.owner getOrElse:
            lastWords(s"Expected resolved Select(...) expression `$selSym` to have an owner")
          val selCls = selOwner.asBlkMember getOrElse:
            lastWords(
              s"Expected resolved class for Select(...) expression to be a BlockMemberSymbol, but got $selOwner (${
                  selOwner.getClass.getName
                })",
            )
          val fieldidx = fieldSelect(selCls, selSym)
          struct.get(
            fieldidx,
            ref = ref.cast(qualRes, RefType(ctx.getType_!(selCls), nullable = false)),
            ty = RefType.anyref,
          )
        case S(otherSym) =>
          lastWords(
            s"Expected resolved Select(...) expression to be a TermSymbol, but got $otherSym (${
                otherSym.getClass.getName
              })",
          )
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

    case dyn @ DynSelect(qual, fld, arrayIdx) =>
      val qualRes = result(qual)
      if arrayIdx then
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

    case Instantiate(_, cls, as) =>
      cls match
        // TODO: Implement proper lowering for Errors with unit payloads.
        case Select(Value.Ref(sym, _), id)
            if (sym eq State.globalThisSymbol) && id.name == "Error" =>
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
      val ctorClsSymOpt = cls match
        case ref: Value.Ref => ref.disamb
        case sel: Select => sel.symbol
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
      val ctorClsBlkSym = ctorClsSym.asBlkMember match
        case S(sym) => sym
        case N => lastWords(
            s"Expected resolved class for an Instantiate(...) expression to be a BlockMemberSymbol, but got ${
                ctorClsSym.getClass.getName
              }",
          )
      val ctorFuncIdx = ctx.getFunc(ctorClsBlkSym) match
        case S(idx) => idx
        case N => lastWords(s"Missing constructor definition for class ${ctorClsBlkSym.toString}")

      val objType = ctx.getFuncInfo_!(ctorFuncIdx).body.resultType_!
      call(funcidx = ctorFuncIdx, as.map(argument), Seq(Result(objType.asValType_!)))

    case Tuple(mut, elems) =>
      val tupleValues = elems.map(argument)
      array.new_fixed(tupleArrayType(mut), tupleValues)

    case r =>
      errExpr(
        Ls(msg"WatBackend::result for expression not implemented yet" -> r.toLoc),
        extraInfo = S(s"Block IR: `${r.toString}`"),
      )
  end result

  /** Returns the intrinsic name if `path` refers to a builtin under `wasm`, or `N` otherwise.
    */
  private def wasmIntrinsicName(path: Path): Opt[Str] = path match
    case Select(Value.Ref(sym, _), ident) if (sym eq State.wasmSymbol) && wasmIntrinsicNameSet.contains(ident.name) =>
      S(ident.name)
    case _ => N

  /** Gets (or creates) the intrinsic function implementing the wasm operator `name`.
    */
  private def getIntrinsic(name: Str)(using Ctx, Raise, Scope): FuncIdx =
    ctx.getOrCreateWasmIntrinsic(name, createIntrinsic(name))

  /** Creates the intrinsic definition for `name`.
    */
  private def createIntrinsic(name: Str)(using Ctx, Raise, Scope): FuncIdx =
    if binaryOps.contains(name) then createBinaryInt31Func(name, binaryOps(name))
    else if unaryOps.contains(name) then createUnaryInt31Func(name, unaryOps(name))
    else lastWords(s"Unsupported wasm intrinsic '$name'")

  /** Creates a binary Int31 intrinsic with two parameters and body built from `op`.
    */
  private def createBinaryInt31Func(
      name: Str,
      op: (Expr, Expr) => Expr,
  )(using Ctx, Raise, Scope): FuncIdx =
    val params = mkIntrinsicParams(name, Seq("lhs", "rhs"))
    val lhsName = params.head._2
    val rhsName = params(1)._2
    val body = binaryInt31Body(lhsName, rhsName, op)
    createIntrinsicFunc(name, params, body)

  /** Creates a unary Int31 intrinsic with a single parameter and body built from `op`.
    */
  private def createUnaryInt31Func(name: Str, op: Expr => Expr)(using Ctx, Raise, Scope): FuncIdx =
    val params = mkIntrinsicParams(name, Seq("arg"))
    val argName = params.head._2
    val body = unaryInt31Body(argName, op)
    createIntrinsicFunc(name, params, body)

  /** Allocates the Wasm type and function definition for an intrinsic with the given signature.
    */
  private def createIntrinsicFunc(
      name: Str,
      params: Seq[(TempSymbol, Str)],
      body: Expr,
  )(using Ctx, Raise, Scope): FuncIdx =
    val funcTy = ctx.addType(
      sym = N,
      TypeInfo(
        id = SymIdx(scope.allocateName(TempSymbol(N, name))),
        FunctionType(
          params = params.map((_, nme) => WasmParam(S(nme), RefType.anyref)),
          results = Seq(Result(RefType.anyref)),
        ),
        objectTag = N,
      ),
    )
    val funcInfo = FuncInfo(
      id = SymIdx(scope.allocateName(TempSymbol(N, name))),
      typeIdx = funcTy,
      params = params,
      nResults = 1,
      locals = Seq.empty,
      body = body,
      `export` = N,
    )
    ctx.addFunc(N, funcInfo)
  end createIntrinsicFunc

  /** Builds the body for an Int31 binary operator.
    */
  private def binaryInt31Body(
      lhsName: Str,
      rhsName: Str,
      op: (Expr, Expr) => Expr,
  )(using Ctx, Scope): Expr =
    val cond = i32.and(
      ref.test(getLocalAnyref(lhsName), RefType.i31ref),
      ref.test(getLocalAnyref(rhsName), RefType.i31ref),
    )
    val i31Op = ref.i31(op(getI32FromAnyref(lhsName), getI32FromAnyref(rhsName)))
    `if`(
      condition = cond,
      ifTrue = i31Op,
      ifFalse = S(unreachable),
      resultTypes = Seq(Result(RefType.anyref)),
    )

  /** Builds the body for an Int31 unary operator.
    */
  private def unaryInt31Body(paramName: Str, op: Expr => Expr)(using Ctx, Scope): Expr =
    val cond = ref.test(getLocalAnyref(paramName), RefType.i31ref)
    val i31Op = ref.i31(op(getI32FromAnyref(paramName)))
    `if`(
      condition = cond,
      ifTrue = i31Op,
      ifFalse = S(unreachable),
      resultTypes = Seq(Result(RefType.anyref)),
    )

  /** Creates parameters for an intrinsic.
    */
  private def mkIntrinsicParams(name: Str, suffixes: Seq[Str]): Seq[(TempSymbol, Str)] =
    suffixes.map: suffix =>
      val sym = TempSymbol(N, suffix)
      sym -> suffix

  /** Loads the local `name` as an `anyref`.
    */
  private def getLocalAnyref(name: Str): Expr =
    local.get(LocalIdx(SymIdx(name)), RefType.anyref)

  /** Extracts the signed i32 value from the Int31 stored in the local `name`.
    */
  private def getI32FromAnyref(name: Str): Expr =
    i31.get(ref.cast(getLocalAnyref(name), RefType.i31ref), true)

  def returningTerm(t: Block)(using Ctx, Raise, Scope): Expr =
    def isControlTransfer(expr: Expr): Bool =
      expr.resultType.contains(UnreachableType) || expr.mnemonic == "return"

    def asStatement(expr: Expr): Expr =
      if isControlTransfer(expr) then expr
      else
        expr.resultType match
          case S(_) => drop(expr)
          case N => expr

    t match
      case _: HandleBlock =>
        errExpr(Ls(msg"This code requires effect handler instrumentation but was compiled without it." -> N))
      case Assign(l, r, rst) if l is State.noSymbol =>
        val rExpr = result(r)
        val evalExpr = rExpr.resultType match
          case S(_) => drop(rExpr)
          case N => rExpr
        val rstBlk = returningTerm(rst)
        blockInstr(
          label = N,
          children = Seq(evalExpr, rstBlk),
          resultTypes = rstBlk.resultTypes.map(r => Result(r.asValType_!)),
        )

      case Assign(l, r, rst) =>
        val lExpr = getVar(l, l.toLoc)
        val rExpr = result(r)
        val idx = lExpr.instrargs(0).asInstanceOf[LocalIdx]
        val assignExpr = lExpr.mnemonicPrefix match
          case S("global") =>
            errExpr(
              Ls(msg"WatBuilder::returningTerm for Assign(...) to global variable not implemented yet" -> l.toLoc),
              extraInfo = S(s"Block IR: ${t.showAsTree}"),
            )
          case S("local") => local.set(idx, rExpr)
          case _ =>
            lastWords(
              s"Expected `global.*` or `local.*` when compiling instruction for `$l`, but got ${lExpr.mnemonic}",
            )

        val rstBlk = returningTerm(rst)
        blockInstr(
          label = N,
          children = Seq(assignExpr, rstBlk),
          resultTypes = resultClauses(rstBlk),
        )

      case assign @ AssignField(lhs, nme, rhs, rst) =>
        val lhsExpr = result(lhs)
        val rhsExpr = result(rhs)
        val assignInstr = assign.symbol match
          case S(selSym: TermSymbol) =>
            val selOwner = selSym.owner getOrElse
              lastWords(s"Expected resolved AssignField(...) expression `$selSym` to have an owner")
            val selCls = selOwner.asBlkMember getOrElse
              lastWords(
                s"Expected resolved class for AssignField(...) expression to be a BlockMemberSymbol, but got $selOwner (${
                    selOwner.getClass.getName
                  })",
              )
            val fieldidx = fieldSelect(selCls, selSym)
            val objRef = ref.cast(lhsExpr, RefType(ctx.getType_!(selCls), nullable = false))
            struct.set(fieldidx, objRef, rhsExpr)
          case S(otherSym) =>
            lastWords(
              s"Expected resolved AssignField(...) expression to be a TermSymbol, but got $otherSym (${
                  otherSym.getClass.getName
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
        blockInstr(
          label = N,
          children = Seq(assignInstr, rstBlk),
          resultTypes = resultClauses(rstBlk),
        )

      case assign @ AssignDynField(lhs, fld, arrayIdx, rhs, rst) =>
        val lhsExpr = result(lhs)
        val rhsExpr = result(rhs)
        val assignInstr =
          if arrayIdx then
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
              Ls(msg"WatBuilder::returningTerm for AssignDynField(...) where `arrayIdx = false` is not implemented yet" ->
                lhs.toLoc),
              extraInfo = S(assign),
            )

        val rstBlk = returningTerm(rst)
        blockInstr(
          label = N,
          children = Seq(assignInstr, rstBlk),
          resultTypes = resultClauses(rstBlk),
        )

      case Define(defn, rst) =>
        def mkThis(sym: InnerSymbol): Expr = result(Value.This(sym))
        defn match
          case ValDefn(tsym, sym, p) =>
            // * Currently we allow `val` outside of object/module scopes,
            // * in which case it has no owner and is just a glorified local variable rather than a field
            tsym.owner match
              case N => errExpr(
                  Ls(
                    msg"WatBuilder::returningTerm for ValDefn(...) where `tsym.owner.isEmpty` not implemented yet" ->
                      sym.toLoc,
                  ),
                  extraInfo = S(s"Block IR of `defn`: ${defn.toString}\nBlock IR of `defn.tsym`: ${tsym.toString}"),
                )
              case S(owner) =>
                val ownerBlkMem = owner.asBlkMember.get
                val rstWat = returningTerm(rst)
                blockInstr(
                  label = N,
                  children = Seq(
                    struct.set(
                      index = fieldSelect(ownerBlkMem, tsym),
                      ref = mkThis(owner),
                      value = result(p),
                    ),
                    rstWat,
                  ),
                  resultTypes = resultClauses(rstWat),
                )

          case defn: (FunDefn | ClsLikeDefn) =>
            val res = scope.nest givenIn:
              boundary:
                defn match
                  case FunDefn(params = Nil) =>
                    lastWords("cannot generate function with no parameter list")
                  case fd @ FunDefn(own, sym, dSym, ps :: pss, bod) =>
                    if own.nonEmpty then
                      break(errExpr(
                        Ls(
                          msg"WatBuilder::returningTerm for Define(...) with `owner.nonEmpty` not implemented yet" ->
                            defn.sym.toLoc,
                        ),
                        extraInfo = S(defn.showAsTree),
                      ))

                    val result = pss.foldRight(bod):
                      case (ps, block) =>
                        Return(Lambda(ps, block), false)
                    val (params, bodyWat, locals) = setupFunction(ps, result)
                    if sym.nameIsMeaningful then
                      val funcTy = ctx.addType(
                        sym = N,
                        TypeInfo(
                          id = SymIdx(scope.allocateName(TempSymbol(N, sym.nme))),
                          FunctionType(
                            params = params.map(_._1),
                            results = Seq.fill(bodyWat.resultTypes.length)(Result(RefType.anyref)),
                          ),
                          objectTag = N,
                        ),
                      )

                      val funcInfo =
                        FuncInfo(
                          sym,
                          typeIdx = funcTy,
                          params = ps.params.zip(params.map(_._2)).map((p, nme) => p.sym -> nme),
                          nResults = bodyWat.resultTypes.length,
                          locals = locals,
                          body = bodyWat,
                        )
                      val func = ctx.addFunc(S(defn.sym), funcInfo)

                      nop
                    else
                      errExpr(
                        Ls(
                          msg"WatBuilder::returningTerm for FunDefn(...) where `!sym.nameIsMeaningful` not implemented yet" ->
                            defn.sym.toLoc,
                        ),
                        extraInfo = S(defn.showAsTree),
                      )
                    end if
                  case clsLikeDefn: ClsLikeDefn =>
                    // Guard against unsupported features
                    def errUnimplExpr(cond: Str): Nothing = break(errExpr(
                      Ls(
                        msg"WatBackend::returningTerm for ClsLikeDefn(...) where `$cond` not implemented yet" ->
                          clsLikeDefn.sym.toLoc,
                      ),
                      extraInfo = S(defn.showAsTree),
                    ))
                    val isSingletonObj = clsLikeDefn.k is syntax.Obj
                    if clsLikeDefn.owner.nonEmpty then
                      break(errUnimplExpr("owner.nonEmpty"))
                    if !(clsLikeDefn.k is syntax.Cls) && !isSingletonObj then
                      break(errUnimplExpr("unsupported ClsLikeDefn kind"))
                    if isSingletonObj && clsLikeDefn.paramsOpt.nonEmpty then
                      break(errUnimplExpr("paramsOpt.nonEmpty for object"))
                    if clsLikeDefn.auxParams.nonEmpty then
                      break(errUnimplExpr("auxParams.nonEmpty"))
                    if clsLikeDefn.parentPath.nonEmpty then
                      break(errUnimplExpr("parentPath.nonEmpty"))
                    if clsLikeDefn.methods.nonEmpty then
                      break(errUnimplExpr("methods.nonEmpty"))
                    clsLikeDefn.preCtor match
                      case End(_) => ()
                      case _ => break(errUnimplExpr("preCtor is not End"))
                    if clsLikeDefn.companion.isDefined then
                      break(errUnimplExpr("companion.isDefined"))

                    val ctorAuxParams = clsLikeDefn.auxParams.map: ps =>
                      ps.params.map: p =>
                        p -> scope.allocateName(p.sym)

                    // Use the symbolic type reference (e.g. `$Foo`) in emitted WAT for readability.
                    // Numeric indices are only needed for `$tag` values.
                    val typeref = ctx.getType_!(clsLikeDefn.sym)
                    val typeinfo = ctx.getTypeInfo_!(typeref)

                    val (ctorParams, thisVar, ctorWat, ctorLocals) = setupCtorLocals(clsLikeDefn)

                    // * If there are no ctor params, pop one param list off the aux params
                    val (newCtorAuxParams, initialCtorParams) = clsLikeDefn.paramsOpt match
                      case None => ctorAuxParams match
                          case head :: next => (next, head)
                          case Nil => (ctorAuxParams, Nil)
                      case Some(_) => (ctorAuxParams, ctorParams)

                    val tagValue = typeinfo.objectTag.getOrElse:
                      lastWords(s"Expected class ${clsLikeDefn.sym} to have an object tag")

                    val ctorCode = blockInstr(
                      label = N,
                      Seq(
                        local.set(thisVar, struct.new_default(typeref)),
                        struct.set(
                          FieldIdx(typeinfo.compType.asInstanceOf[StructType].fields(0)._2.id),
                          ref.cast(
                            local.get(thisVar, RefType.anyref),
                            RefType(typeref, nullable = false),
                          ),
                          i32.const(tagValue),
                        ),
                        ctorWat,
                        `return`(S(local.get(thisVar, RefType(typeref, nullable = false)))),
                      ),
                      resultTypes = Seq(Result(RefType.anyref)),
                    )

                    val ctorAux = if newCtorAuxParams.isEmpty then
                      ctorCode
                    else
                      break(errUnimplExpr("newCtorAuxParams.nonEmpty"))

                    val funcTyId = clsLikeDefn.sym
                      .optionIf: sym =>
                        !isSingletonObj && sym.nameIsMeaningful
                      .map: sym =>
                        s"${sym.nme}_ctor"
                      .getOrElse:
                        scope.allocateName(TempSymbol(N, s"${clsLikeDefn.sym.nme}_ctor"))
                    val funcTy = ctx.addType(
                      sym = N,
                      TypeInfo(
                        id = SymIdx(funcTyId),
                        FunctionType(
                          params = ctorParams.map(p => WasmParam(S(p._2), RefType.anyref)),
                          results = Seq(Result(RefType.anyref)),
                        ),
                        objectTag = N,
                      ),
                    )

                    val ctorId = clsLikeDefn.sym
                      .optionIf: sym =>
                        !isSingletonObj && sym.nameIsMeaningful
                      .map: sym =>
                        s"${sym.nme}_ctor"
                    ctx.addFunc(
                      S(clsLikeDefn.sym),
                      FuncInfo(
                        id =
                          SymIdx(ctorId.getOrElse(scope.allocateName(TempSymbol(N, s"${clsLikeDefn.sym.nme}_ctor")))),
                        typeIdx = funcTy,
                        params = ctorParams,
                        nResults = ctorCode.resultTypes.length,
                        locals = ctorLocals,
                        body = ctorAux,
                        `export` = ctorId,
                      ),
                    )
                    if isSingletonObj then
                      registerSingletonInit(clsLikeDefn, typeref)

                    nop

                  case defn =>
                    errExpr(
                      Ls(msg"WatBuilder::returningTerm for Define(...) not implemented yet" -> defn.sym.toLoc),
                      extraInfo = S(defn.showAsTree),
                    )
                end match

            val rstBlk = returningTerm(rst)
            blockInstr(
              label = N,
              children = Seq(res, rstBlk),
              resultTypes = resultClauses(rstBlk),
            )
        end match

      case Return(res, true) =>
        val resWat = result(res)
        resWat.resultType match
          case S(RefType(heapType, _)) => heapType match
              case HeapType.Func =>
                errExpr(Ls(msg"Returning function instances is not supported" -> res.toLoc))
              case typeidx: TypeIdx if ctx.getTypeInfo_!(typeidx).compType.isInstanceOf[FunctionType] =>
                errExpr(Ls(msg"Returning function instances is not supported" -> res.toLoc))
              case _ => ()
          case _ => ()

        resWat
      case Return(res, false) =>
        val resWat = result(res)
        resWat.resultType match
          case S(RefType(heapType, _)) => heapType match
              case HeapType.Func =>
                errExpr(Ls(msg"Returning function instances is not supported" -> res.toLoc))
              case typeidx: TypeIdx if ctx.getTypeInfo_!(typeidx).compType.isInstanceOf[FunctionType] =>
                errExpr(Ls(msg"Returning function instances is not supported" -> res.toLoc))
              case _ => ()
          case _ => ()

        `return`(S(resWat))

      case Scoped(syms, body) =>
        blockPreamble(syms)
        returningTerm(body)
      case Break(label) =>
        ctx.lookupLabel(label) match
          case S(target) => br(target.breakLabel)
          case N =>
            errExpr(
              Ls(
                msg"WatBuilder::returningTerm for Break(...) to unknown label `${label.nme}`" -> label.toLoc,
              ),
              extraInfo = S(t.showAsTree),
            )
      case Continue(label) =>
        ctx.lookupLabel(label) match
          case S(target) =>
            target.continueLabel match
              case S(continueLabel) => br(continueLabel)
              case N =>
                errExpr(
                  Ls(
                    msg"WatBuilder::returningTerm for Continue(...) to non-loop label `${label.nme}`" -> label.toLoc,
                  ),
                  extraInfo = S(t.showAsTree),
                )
          case N =>
            errExpr(
              Ls(
                msg"WatBuilder::returningTerm for Continue(...) to unknown label `${label.nme}`" -> label.toLoc,
              ),
              extraInfo = S(t.showAsTree),
            )
      case Label(label, loop, body, rst) =>
        val breakLabel = scope.allocateName(label)
        val continueLabel =
          if loop then S(scope.allocateName(TempSymbol(N, s"${label.nme}_cont")))
          else N

        val bodyExpr = ctx.withLabel(
          label,
          Ctx.LabelTarget(breakLabel, continueLabel),
        ):
          returningTerm(body)
        val bodyStmt = asStatement(bodyExpr)

        val labeledRegion =
          if loop then
            Instructions.block(
              label = S(breakLabel),
              children = Seq(
                Instructions.loop(
                  label = continueLabel,
                  children = Seq(bodyStmt),
                  resultTypes = Seq.empty,
                ),
              ),
              resultTypes = Seq.empty,
            )
          else
            Instructions.block(
              label = S(breakLabel),
              children = Seq(bodyStmt),
              resultTypes = Seq.empty,
            )

        val rstExpr = returningTerm(rst)
        val rstResultTypes = rstExpr.resultTypes.flatMap(ty => ty.asValType.map(Result(_)))
        Instructions.block(
          label = N,
          children = Seq(labeledRegion, rstExpr),
          resultTypes = rstResultTypes,
        )
      case Match(scrut, arms, dflt, rst) =>
        val matchLabelSym = TempSymbol(N, "match")
        val matchLabel = scope.allocateName(matchLabelSym)
        val tailMode = rst.isInstanceOf[End]
        val matchResLocal =
          if tailMode then S(mkTempLocal("matchRes"))
          else N

        def getScrutExpr: Expr = result(scrut)

        def assignTailResult(target: LocalIdx, expr: Expr): Expr =
          if isControlTransfer(expr) then expr
          else
            expr.resultType match
              case S(_) => local.set(target, expr)
              case N => Instructions.block(
                  label = N,
                  children = Seq(
                    expr,
                    local.set(target, result(Value.Ref(State.unitSymbol))),
                  ),
                  resultTypes = Seq.empty,
                )

        def lowerMatchBody(expr: Expr): Expr =
          matchResLocal match
            case S(localIdx) => assignTailResult(localIdx, expr)
            case N => asStatement(expr)

        val matchResInitExpr = matchResLocal.map: localIdx =>
          local.set(localIdx, ref.`null`(HeapType.Any))

        // Compile each match arm
        boundary:
          val armExprs = arms.zipWithIndex.flatMap: (caseAndBody, armIdx) =>
            val (cse, body) = caseAndBody
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
                  case _ =>
                    break(errExpr(Ls(msg"Pattern matching for unit literals not implemented yet" -> lit.toLoc)))

                val bodyExpr = returningTerm(body)
                val armBodyExpr = lowerMatchBody(bodyExpr)
                val armLabelSym = TempSymbol(N, "arm")
                val armLabel = scope.allocateName(armLabelSym)
                S(`if`(
                  condition = testExpr,
                  ifTrue = blockInstr(
                    label = S(armLabel),
                    children = Seq(armBodyExpr, br(matchLabel)),
                    resultTypes = Seq.empty,
                  ),
                  ifFalse = N,
                  resultTypes = Seq.empty,
                ))

              case Case.Cls(cls, _) =>
                val clsBlkMemberSym = cls.asBlkMember.getOrElse:
                  break(errExpr(
                    Ls(msg"Could not resolve BlockMemberSymbol for class pattern" -> cls.toLoc),
                    extraInfo = S(s"ClassLikeSymbol: ${cls.toString}"),
                  ))
                val clsTypeIdx = ctx.getType_!(clsBlkMemberSym)
                val typeinfo = ctx.getTypeInfo_!(clsTypeIdx)

                val expectedTag = typeinfo.objectTag.getOrElse:
                  lastWords(s"Expected class $clsBlkMemberSym to have an object tag")

                val scrutExpr = getScrutExpr
                val isStructCompatible = ref.test(scrutExpr, baseObjectRefType(nullable = true))

                val bodyExpr = returningTerm(body)
                val armBodyExpr = lowerMatchBody(bodyExpr)
                val armLabelSym = TempSymbol(N, "arm")
                val armLabel = scope.allocateName(armLabelSym)

                // Safe to cast and extract tag since ref.test passed
                val scrutAsObject = ref.cast(scrutExpr, baseObjectRefType(nullable = false))
                val scrutTag = struct.get(
                  FieldIdx(typeinfo.compType.asInstanceOf[StructType].fields(0)._2.id),
                  scrutAsObject,
                  I32Type,
                )
                val tagMatches = i32.eq(scrutTag, i32.const(expectedTag))

                S(`if`(
                  condition = isStructCompatible,
                  ifTrue = `if`(
                    condition = tagMatches,
                    ifTrue = blockInstr(
                      label = S(armLabel),
                      children = Seq(armBodyExpr, br(matchLabel)),
                      resultTypes = Seq.empty,
                    ),
                    ifFalse = N,
                    resultTypes = Seq.empty,
                  ),
                  ifFalse = N,
                  resultTypes = Seq.empty,
                ))
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
                val bodyExpr = returningTerm(body)
                val armBodyExpr = lowerMatchBody(bodyExpr)
                val armLabelSym = TempSymbol(N, "arm")
                val armLabel = scope.allocateName(armLabelSym)
                S(`if`(
                  condition = testExpr,
                  ifTrue = blockInstr(
                    label = S(armLabel),
                    children = Seq(armBodyExpr, br(matchLabel)),
                    resultTypes = Seq.empty,
                  ),
                  ifFalse = N,
                  resultTypes = Seq.empty,
                ))
              case _ =>
                break(errExpr(
                  Ls(msg"WatBuilder::returningTerm for Match(...) with case `${cse.toString}` not implemented yet" ->
                    N),
                  extraInfo = S(cse.toString),
                ))
            end match

          val defaultExpr =
            val rawDefaultExpr = dflt match
              case S(defaultBody) => returningTerm(defaultBody)
              case N => unreachable
            lowerMatchBody(rawDefaultExpr)

          // Generate the match block
          val matchBlock = blockInstr(
            label = S(matchLabel),
            children = matchResInitExpr.toSeq ++ armExprs :+ defaultExpr,
            resultTypes = Seq.empty,
          )

          if tailMode then
            Instructions.block(
              label = N,
              children = Seq(
                matchBlock,
                local.get(matchResLocal.get, RefType.anyref),
              ),
              resultTypes = Seq(Result(RefType.anyref)),
            )
          else
            val rstExpr = returningTerm(rst)
            Instructions.block(
              label = N,
              children = Seq(matchBlock, rstExpr),
              resultTypes = rstExpr.resultTypes.flatMap(ty => ty.asValType.map(Result(_))),
            )

      // * Try/finally lowering is intentionally rejected for now: the previous implementation required `exnref` support
      // * which can only be enabled with the `--experimental-wasm-exnref` flag.
      // * Later, it will be implemented using intrinsic function.
      case TryBlock(sub, _, _) =>
        errExpr(
          Ls(msg"WatBuilder::returningTerm for TryBlock(...) not implemented yet" -> N),
          extraInfo = S(sub.showAsTree),
        )

      case Throw(res) =>
        val excWat = result(res)
        `throw`(exnTagIdx, Seq(excWat))

      case End(_) => nop

      case t =>
        errExpr(
          Ls(msg"WatBuilder::returningTerm for expression not implemented yet" -> N),
          extraInfo = S(t.showAsTree),
        )
    end match
  end returningTerm

  def program(
      p: Program,
      exprt: Opt[BlockMemberSymbol],
      wd: io.Path,
  )(using Raise, Scope): (Document, Str, Int) =
    for imprt <- p.imports do
      raise(
        ErrorReport(
          msg"Import of symbol `${imprt._2}` not implemented yet" -> imprt._1.toLoc :: Nil,
          extraInfo = S(imprt),
          source = Diagnostic.Source.Compilation,
        ),
      )
    exprt.foreach: exprt =>
      raise(
        ErrorReport(
          msg"Export of symbol `${exprt.nme}` not implemented yet" -> exprt.toLoc :: Nil,
          extraInfo = S(exprt),
          source = Diagnostic.Source.Compilation,
        ),
      )

    val ctx = Ctx.empty
    given Ctx = ctx

    // Create base Object struct with tag field that all other structs will inherit
    ctx.addType(
      sym = S(baseObjectSym),
      TypeInfo(
        id = SymIdx("Object"),
        StructType(
          Seq(tagFieldSym -> Field(I32Type, mutable = true, id = SymIdx("$tag"))),
          isSubtype = true,
        ),
        objectTag = S(ctx.getFreshObjectTag() ensuring (_ == 0)),
      ),
    )

    // Two-pass scheme: register all supported top-level class struct types before compiling any
    // functions, so all class types are available during nested function codegen.
    createDefnTypes(p.main)

    // Compile the entry function under a dedicated local scope so that any temp locals introduced
    // during codegen (e.g., via `local.tee`) are declared in the entry function.
    ctx.pushLocal()
    val (rawEntryFnExpr, entryFnLocals) =
      block(p.main)
    val entryFnExpr = normalizeEntryExpr(rawEntryFnExpr, p.main.isAbortive)
    val entryExtraLocals = getExtraLocals.filterNot(entryFnLocals.toSet.contains)

    val entrySym = BlockMemberSymbol("entry", Nil)
    val entryNme = scope.allocateName(entrySym)

    val entryFnTy = ctx.addType(
      sym = N,
      TypeInfo(
        id = SymIdx(scope.allocateName(TempSymbol(N, entryNme))),
        FunctionType(params = Seq.empty, results = Seq(Result(RefType.anyref))),
        objectTag = N,
      ),
    )
    val entryFnInfo = FuncInfo(
      id = SymIdx(entryNme),
      typeIdx = entryFnTy,
      params = Seq.empty,
      nResults = 1,
      // TODO(Derppening): Should we place top-level scope variables in the global section?
      locals = (entryFnLocals ++ entryExtraLocals).map(l => l -> scope.allocateOrGetName(l)),
      body = entryFnExpr,
      `export` = S(entryNme),
    )

    ctx.popLocal()
    if stringLits.nonEmpty then
      stringLits.valuesIterator.foreach: lit =>
        if lit.byteLen > 0 then
          ctx.addDataSegment(DataSegment(i32.const(lit.offset), lit.watBytes))

    val singletonInitActions = ctx.getSingletonInitActions
    if singletonInitActions.nonEmpty then
      val initTy = ctx.addType(
        sym = N,
        TypeInfo(
          id = SymIdx(scope.allocateName(TempSymbol(N, "start"))),
          FunctionType(params = Seq.empty, results = Seq.empty),
          objectTag = N,
        ),
      )
      val initBody = blockInstr(
        label = N,
        children = singletonInitActions.toSeq,
        resultTypes = Seq.empty,
      )
      val initFn = ctx.addFunc(
        sym = N,
        FuncInfo(
          id = SymIdx(scope.allocateName(TempSymbol(N, "start"))),
          typeIdx = initTy,
          params = Seq.empty,
          nResults = 0,
          locals = Seq.empty,
          body = initBody,
          `export` = N,
        ),
      )
      ctx.setStartFunc(initFn)
    end if

    ctx.addFunc(S(entrySym), entryFnInfo)

    val systemMemMinPages =
      ctx.getMemoryImport(ExternIntrinsics.SystemModule, ExternIntrinsics.SystemMemoryImportName).fold(0)(_.minPages)
    (ctx.toWat, entryNme, systemMemMinPages)
  end program

  /** Captures the local symbols introduced while compiling `expr`.
    */
  private def withLocalDelta(expr: => Expr)(using Ctx): (Expr, Seq[Local]) =
    val before = ctx.getWasmLocals._2.getOrElse(Seq.empty).toSet
    val compiled = expr
    val after = ctx.getWasmLocals._2.getOrElse(Seq.empty)
    (compiled, after.filterNot(before.contains))

  def blockPreamble(ss: Iterable[Symbol])(using Ctx, Raise, Scope): Seq[Local] =
    val vars = ss
      .toSeq
      .toArray
      .sortBy(_.uid)
      .iterator
      .map: l =>
        scope.allocateName(l)
        l
      .toSeq
    ctx.addLocals(vars)
    vars

  def nonNestedScoped(blk: Block)(k: Block => Expr)(using Ctx, Raise, Scope): Expr = blk match
    case Scoped(syms, body) =>
      blockPreamble(syms.view.filter(body.freeVars))
      k(body)
    case _ => k(blk)

  def block(t: Block)(using Ctx, Raise, Scope): (Expr, Seq[Local]) =
    withLocalDelta:
      nonNestedScoped(t)(returningTerm)

  def setupFunction(
      params: ParamList,
      body: Block,
  )(using Ctx, Raise, Scope): (Seq[WasmParam -> Str], Expr, Seq[(Local, Str)]) =
    // Add a frame for `ctx.locals`
    ctx.pushLocal()

    val result = scope.nest givenIn:
      val wasmParams = params.params.map: p =>
        val paramNme = scope.allocateName(p.sym)
        val param = WasmParam(S(paramNme), RefType.anyref)
        ctx.addLocal(p.sym)
        param -> paramNme
      val (wasmBody, locals) = block(body)
      val paramSyms: Set[Local] = params.params.map(p => (p.sym: Local)).toSet
      val extraLocals = getExtraLocals.filterNot((locals.toSet ++ paramSyms).contains)
      val localsWithNames = (locals ++ extraLocals).map(l => l -> scope.allocateOrGetName(l))
      (wasmParams.toSeq, wasmBody, localsWithNames)

    // Restore `ctx.locals`
    ctx.popLocal()

    result
  end setupFunction

end WatBuilder
