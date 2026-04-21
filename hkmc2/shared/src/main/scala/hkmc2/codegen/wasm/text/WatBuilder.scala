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
import text.{Import as WasmImport, Param as WasmParam}
import Message.MessageContext
import Scope.scope

import scala.collection.mutable.{ArrayBuffer as ArrayBuf, LinkedHashMap, LinkedHashSet, Queue}
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
  /** The maximum number of characters taken to be part of the identifier asscoiated with string constants. */
  val StringConstantIdentMaxLength = 16

  object ExternIntrinsics:
    val SystemModule = "system"
    val SystemMemoryImportName = "mem"
    val StringFromUtf16ImportName = "mlx_str_from_utf16"
    val WasmPageSizeBytes = 65536

class WatBuilder(using TraceLogger, State) extends CodeBuilder:
  import Ctx.ctx
  import Ctx.{SingletonInfo, binaryOps, unaryOps, wasmIntrinsicArities, wasmIntrinsicNameSet}
  import FunctionCtx.funcCtx
  import Instructions.{block as blockInstr, loop as loopInstr, *}
  import WatBuilder.ExternIntrinsics

  type Context = Ctx

  private val baseObjectSym: BlockMemberSymbol = BlockMemberSymbol("Object", Nil)
  private val tagFieldSym: TermSymbol = TermSymbol(syntax.MutVal, owner = N, Ident("$tag"))

  private case class StringLitInfo(offset: Int, byteLen: Int, watBytes: Str)
  private val stringLits: LinkedHashMap[Str, StringLitInfo] = LinkedHashMap.empty
  private val initFuncSyms: LinkedHashMap[BlockMemberSymbol, BlockMemberSymbol] = LinkedHashMap.empty
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
      && (!(defn.k is syntax.Obj) || defn.parentPath.isEmpty)
      && (!(defn.k is syntax.Obj) || defn.methods.isEmpty)
      && defn.companion.isEmpty

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
      sym = State.unitBlockMemberSymbol,
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
    )(N)

  /** Registers the synthetic `Unit` singleton. */
  private def RegisterUnitSingleton()(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Unit =
    val unitDefn = syntheticUnitDefn
    val singletonOwner = unitDefn.isym match
      case mos: ModuleOrObjectSymbol => S(mos)
      case _ => N
    if ctx.containsSingleton(unitDefn.sym) then return

    if ctx.getType(unitDefn.sym).isEmpty then
      predeclareClassType(unitDefn)
      predeclareClassInit(unitDefn)
      predeclareClassConstructor(unitDefn)

    returningTerm(Define(unitDefn, End("")))

    val typeInfo = ctx.getTypeInfo_!(unitDefn.sym)
    val singletonInfo = ctx.getSingletonInfo(unitDefn.sym) getOrElse:
      lastWords("Missing singleton metadata for synthetic Unit object")
    // Record session metadata for the synthetic Unit singleton.
    summon[SessionExportCtx].emit(SessionClass(
      sym = unitDefn.sym,
      typeInfo = typeInfo,
      runtimeTags = ctx.getAllRuntimeTags(unitDefn.sym) getOrElse:
        LinkedHashSet(ctx.getRuntimeClassTag_!(unitDefn.sym))
      ,
      aliasSyms = singletonOwner.toSeq,
    ))
    summon[SessionExportCtx].emit(SessionSingleton(
      blockSym = unitDefn.sym,
      objectSym = singletonOwner,
      moduleName = SessionBinding.ReplModuleName,
      exportName = singletonInfo.globalName,
      globalTy = singletonInfo.globalTy,
    ))
  end RegisterUnitSingleton

  /** Registers eager singleton runtime state by creating its global and start-init action. */
  private def registerSingletonInit(
      clsLikeDefn: ClsLikeDefn,
      typeref: TypeIdx,
  )(using Ctx, Raise, Scope): Unit =
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
        globalType = GlobalType(globalTy, mutable = true),
        init = ref.`null`(typeref),
        exportName = S(globalName),
      ),
    )

    val ctorCall = call(
      funcidx = ctx.getFunc_!(clsLikeDefn.sym),
      operands = Seq.empty,
      returnTypes = Seq(Result(RefType.anyref)),
    )
    ctx.addSingletonInitAction(global.set(globalIdx, ref.cast(ctorCall, globalTy)))
  end registerSingletonInit

  /** Collects only top-level class definitions in `block`. */
  private def collectTopLevelClassDefns(block: Block): List[ClsLikeDefn] =
    val acc = ArrayBuf.empty[ClsLikeDefn]
    new BlockTraverserShallow:
      applyBlock(block)
      override def applyBlock(b: Block): Unit = b match
        case Match(_, _, _, rst) => applySubBlock(rst)
        case Label(_, _, _, rst) => applySubBlock(rst)
        case TryBlock(_, _, rst) => applySubBlock(rst)
        case _ => super.applyBlock(b)
      override def applyDefn(defn: Defn): Unit = defn match
        case clsLikeDefn: ClsLikeDefn =>
          clsLikeDefn.optionIf(isSupportedTopLevelClass).foreach(acc += _)
        case _ => ()
    acc.toList

  /** Resolves the parent symbol for a top-level class definition, if present. */
  private def resolveParentSym(defn: ClsLikeDefn)(using Raise): Opt[BlockMemberSymbol] =
    def unsupportedParent(): Opt[BlockMemberSymbol] =
      raise(ErrorReport(
        msg"Wasm inheritance ordering only supports direct resolved parent class references." ->
          defn.parentPath.flatMap(_.toLoc) :: Nil,
        extraInfo = S(defn.showAsTree),
        source = Diagnostic.Source.Compilation,
      ))
      N

    defn.parentPath match
      case N => N
      case S(Value.Ref(sym, _)) =>
        sym.asCls.flatMap(_.asBlkMember).orElse(unsupportedParent())
      case S(sel: Select) =>
        sel.symbol.flatMap(_.asCls).flatMap(_.asBlkMember).orElse(unsupportedParent())
      case S(_) =>
        unsupportedParent()

  /** Orders top-level classes using a Kahn topological sort. */
  private def sortTopLevelClasses(defns: List[ClsLikeDefn])(using Raise): List[ClsLikeDefn] =
    val defnsBySym = defns.iterator.map(defn => defn.sym -> defn).toMap
    val childrenBySym = LinkedHashMap.empty[BlockMemberSymbol, ArrayBuf[BlockMemberSymbol]]
    val indegrees = LinkedHashMap.empty[BlockMemberSymbol, Int]

    defns.foreach: defn =>
      childrenBySym(defn.sym) = ArrayBuf.empty
      indegrees(defn.sym) = 0

    defns.foreach: defn =>
      if defn.parentPath.nonEmpty then
        val parentSym = resolveParentSym(defn).getOrElse(lastWords("unreachable"))
        if defnsBySym.contains(parentSym) then
          childrenBySym(parentSym) += defn.sym
          indegrees(defn.sym) += 1
        else
          raise(ErrorReport(
            msg"Wasm inheritance ordering requires parent classes to be supported top-level classes." ->
              defn.parentPath.flatMap(_.toLoc) :: Nil,
            extraInfo = S(s"${defn.sym.nme} extends ${parentSym.nme}"),
            source = Diagnostic.Source.Compilation,
          ))

    val zeroIndegree = Queue.from:
      defns.iterator.collect:
        case defn if indegrees(defn.sym) == 0 => defn.sym

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
            .filter(defn => indegrees(defn.sym) > 0)
            .map(_.sym.nme)
            .mkString(", "),
        ),
        source = Diagnostic.Source.Compilation,
      ))

    ordered.toList
  end sortTopLevelClasses

  /** Declares one supported top-level class type for early wasm registration. */
  private def predeclareClassType(defn: ClsLikeDefn)(using Ctx, Raise, Scope): Unit =
    val parentTypeIdx =
      if defn.parentPath.isEmpty then baseObjectTypeIdx
      else
        ctx.getType_!(
          resolveParentSym(defn) getOrElse:
            lastWords(s"Expected resolved parent class symbol when predeclaring ${defn.sym.nme}"),
        )
    val inheritedFields = ctx.getTypeInfo_!(parentTypeIdx).compType match
      case struct: StructType => struct.fields
      case other => lastWords(s"Parent type must be a struct, found ${other.toWat.mkString()}")

    val classFields = (defn.publicFields.map(_._2) ++ defn.privateFields)
      .map: f =>
        f -> Field(RefType.anyref, mutable = true, id = f.nme)

    val allFields = inheritedFields ++ classFields
    val runtimeTag = ctx.getFreshObjectTag()

    ctx.addType(
      sym = S(defn.sym),
      typeInfo = TypeInfo(
        sym = defn.sym,
        compType = StructType(fields = allFields, parents = Seq(parentTypeIdx)),
        objectTag = S(runtimeTag),
      ),
    )
    ctx.registerRuntimeClassTags(defn.sym, LinkedHashSet(runtimeTag))
  end predeclareClassType

  /** Records the runtime tag accepted by each class pattern: the class's own tag and descendant tags. */
  private def predeclareClassTags(
      orderedDefns: List[ClsLikeDefn],
  )(using Ctx, Raise, Scope): Unit =
    val childrenBySym = LinkedHashMap.empty[BlockMemberSymbol, ArrayBuf[BlockMemberSymbol]]
    orderedDefns.foreach: defn =>
      childrenBySym(defn.sym) = ArrayBuf.empty
    orderedDefns.foreach: defn =>
      resolveParentSym(defn).foreach: parentSym =>
        childrenBySym(parentSym) += defn.sym
    orderedDefns.reverseIterator.foreach: defn =>
      val ownTag = ctx.getTypeInfo_!(defn.sym).objectTag getOrElse:
        lastWords(s"Expected class ${defn.sym} to have an object tag")
      val childTags = childrenBySym(defn.sym).flatMap: childSym =>
        ctx.getAllRuntimeTags(childSym).getOrElse(lastWords("unreachable"))
      ctx.registerRuntimeClassTags(defn.sym, LinkedHashSet(ownTag) ++ childTags)

  /** Declares the shared Wasm function type used by a class-associated function placeholder. */
  private def declareClassFuncType(
      defn: ClsLikeDefn,
      suffix: Str,
      params: Seq[Local -> SymIdx],
  )(using Ctx, Raise, Scope): TypeIdx =
    val isSingletonObj = defn.k is syntax.Obj
    val funcTyId = defn.sym
      .optionIf: sym =>
        !isSingletonObj && sym.nameIsMeaningful
      .fold(scope.allocateName(TempSymbol(N, s"${defn.sym.nme}_$suffix"))): sym =>
        s"${sym.nme}_$suffix"
    ctx.addType(
      sym = N,
      TypeInfo(
        id = SymIdx(funcTyId),
        FunctionType(
          params = params.map(p => WasmParam(p._2, RefType.anyref)),
          results = Seq(Result(RefType.anyref)),
        ),
        objectTag = N,
      ),
    )
  end declareClassFuncType

  /** Returns the symbol used to predeclare and later overwrite a class init function. */
  private def initFuncSym(sym: BlockMemberSymbol): BlockMemberSymbol =
    initFuncSyms.getOrElseUpdate(sym, BlockMemberSymbol(s"${sym.nme}_init", Nil, nameIsMeaningful = false))

  /** Registers a placeholder class-associated function so later lowering can overwrite it. */
  private def predeclareClassFunc(
      defn: ClsLikeDefn,
      suffix: Str,
      params: Seq[Local -> SymIdx],
      sym: Opt[Symbol],
      id: Opt[SymIdx],
      exportName: Opt[Str],
  )(using Ctx, Raise, Scope): Unit =
    val funcTy = declareClassFuncType(defn, suffix, params)
    ctx.addFunc(
      sym,
      FuncInfo(
        id = id getOrElse:
          SymIdx(exportName getOrElse:
            scope.allocateName(TempSymbol(N, s"${defn.sym.nme}_$suffix")))
        ,
        typeUse = TypeUse(funcTy),
        params = params,
        resultTypes = Seq(Result(RefType.anyref)),
        locals = Seq.empty,
        body = ref.`null`(ctx.getType_!(defn.sym)),
        exportName = exportName,
      ),
    )
  end predeclareClassFunc

  /** Declares one top-level class init function. */
  private def predeclareClassInit(defn: ClsLikeDefn)(using Ctx, Raise, Scope): Unit =
    val initParams = (defn.isym -> SymIdx("this")) +:
      defn.paramsOpt.fold(Nil): ps =>
        ps.params.map: p =>
          p.sym -> SymIdx(p.sym.nme)
    val initId = defn.sym
      .optionIf: sym =>
        !(defn.k is syntax.Obj) && sym.nameIsMeaningful
      .map: sym =>
        SymIdx(s"${sym.nme}_init")
    predeclareClassFunc(defn, "init", initParams, S(initFuncSym(defn.sym)), initId, N)

  /** Declares one top-level class constructor. */
  private def predeclareClassConstructor(defn: ClsLikeDefn)(using Ctx, Raise, Scope): Unit =
    val ctorParams = defn.paramsOpt.fold(Nil): ps =>
      ps.params.map: p =>
        p.sym -> SymIdx(p.sym.nme)
    val ctorId = defn.sym
      .optionIf: sym =>
        !(defn.k is syntax.Obj) && sym.nameIsMeaningful
      .map: sym =>
        SymIdx(s"${sym.nme}_ctor")
    val ctorExportName = defn.sym
      .optionIf: sym =>
        !(defn.k is syntax.Obj) && sym.nameIsMeaningful
      .map(_.nme)
    predeclareClassFunc(defn, "ctor", ctorParams, S(defn.sym), ctorId, ctorExportName)

  /** Collects the symbols that should live in mutable globals so later REPL blocks can import them.
    *
    * TODO: replace this structural scan with an explicit "session-visible bindings" set from lowering once that
    * information is available directly in the IR.
    */
  private def collectSessionGlobalSymbols(
      b: Block,
      sessionExportCtx: SessionExportCtx,
  ): Set[Symbol] =
    def restOf(block: Block): Opt[Block] = block match
      case Define(_, rst) => S(rst)
      case Assign(_, _, rst) => S(rst)
      case AssignField(_, _, _, rst) => S(rst)
      case AssignDynField(_, _, _, _, rst) => S(rst)
      case Match(_, _, _, rst) => S(rst)
      case TryBlock(_, _, rst) => S(rst)
      case Label(_, _, _, rst) => S(rst)
      case _ => N

    def recur(block: Block): Set[Symbol] = block match
      case Scoped(_, body) =>
        recur(body)
      case Begin(sub, rst) =>
        recur(sub) ++ recur(rst)
      case Define(ValDefn(_, sym, _), rst) if sessionExportCtx.shouldExport(sym) =>
        recur(rst) + sym
      case Define(_, rst) =>
        recur(rst)
      case Assign(sym: Symbol, _, rst) if sessionExportCtx.shouldExport(sym) =>
        recur(rst) + sym
      case _: BlockTail =>
        Set.empty
      case block =>
        restOf(block).fold(Set.empty)(recur)

    recur(b)
  end collectSessionGlobalSymbols

  /** Declares a mutable exported global for a REPL-visible binding produced by the current block. */
  private def registerSessionGlobal(
      sym: Symbol,
  )(using Ctx, Raise, Scope, SessionExportCtx): Unit =
    if ctx.containsGlobal(sym) then return
    val exportName = sym.nme
    ctx.addGlobal(
      sym,
      GlobalInfo(
        id = SymIdx(scope.allocateOrGetName(sym)),
        globalType = GlobalType(RefType.anyref, mutable = true),
        init = ref.`null`(HeapType.Any),
        exportName = S(exportName),
      ),
    )
    summon[SessionExportCtx].emit(SessionGlobal(
      sym = sym,
      moduleName = SessionBinding.ReplModuleName,
      exportName = exportName,
      globalType = GlobalType(RefType.anyref, mutable = true),
    ))
  end registerSessionGlobal

  /** Registers imported REPL bindings into the current module before codegen starts. */
  private def registerSessionImports(
      sessionImports: Seq[SessionBinding],
  )(using Ctx, Raise, Scope): Unit =
    sessionImports.foreach:
      case cls: SessionClass =>
        if ctx.getType(cls.sym).isEmpty then
          ctx.addType(sym = S(cls.sym), typeInfo = cls.typeInfo)
        ctx.registerRuntimeClassTags(cls.sym, cls.runtimeTags)
      case _ => ()

    sessionImports.foreach:
      case func: SessionFunc =>
        val funcName = scope.allocateOrGetName(func.sym)
        val typeIdx = ctx.addType(
          sym = N,
          TypeInfo(id = N, func.funcType),
        )
        ctx.addFunctionImport(
          S(func.sym),
          WasmImport(
            func.moduleName,
            func.exportName,
            ExternType.Func(SymIdx(funcName), TypeUse(typeIdx)),
          ),
        )
      case glob: SessionGlobal =>
        val globalName = scope.allocateOrGetName(glob.sym)
        ctx.addGlobalImport(
          S(glob.sym),
          WasmImport(
            glob.moduleName,
            glob.exportName,
            ExternType.Global(SymIdx(globalName), glob.globalType),
          ),
        )
      case singleton: SessionSingleton =>
        val globalName = scope.allocateOrGetName(singleton.blockSym)
        ctx.addGlobalImport(
          S(singleton.blockSym),
          WasmImport(
            singleton.moduleName,
            singleton.exportName,
            ExternType.Global(SymIdx(globalName), GlobalType(singleton.globalTy, mutable = true)),
          ),
        )
        ctx.registerSingleton(singleton.blockSym, singleton.objectSym, SingletonInfo(globalName, singleton.globalTy))
      case _: SessionClass => ()
  end registerSessionImports

  /** Declares one top-level class method. */
  private def predeclareMethod(methodDefn: FunDefn, ownerCls: ClsLikeDefn)(using Ctx, Raise, Scope): Unit =
    val methodParams = (ownerCls.isym -> SymIdx("this")) +:
      methodDefn.params.headOption.fold(Nil): ps =>
        ps.params.map: p =>
          p.sym -> SymIdx(p.sym.nme)
    val methodId = ownerCls.sym
      .optionIf: sym =>
        !(ownerCls.k is syntax.Obj) && sym.nameIsMeaningful
      .map: sym =>
        SymIdx(s"${sym.nme}_${methodDefn.sym.nme}")
    predeclareClassFunc(ownerCls, methodDefn.sym.nme, methodParams, S(methodDefn.sym), methodId, N)

  /** Declares placeholders for all methods on one top-level class. */
  private def predeclareClassMethods(defn: ClsLikeDefn)(using Ctx, Raise, Scope): Unit =
    defn.methods.foreach:
      case methodDefn @ FunDefn(_, _, _, Nil | _ :: Nil, _) =>
        predeclareMethod(methodDefn, defn)
      case FunDefn(_, sym, _, _ :: _ :: _, _) =>
        raise(ErrorReport(
          msg"WatBuilder::predeclareClassMethods for ClsLikeDefn(...) with `multi-parameter-list method` not implemented yet" ->
            sym.toLoc :: Nil,
          source = Diagnostic.Source.Compilation,
        ))
      case _ => ()

  /** Gets (and caches) the exception tag used for MLX `throw`. */
  private def exnTagIdx(using Ctx, Raise, Scope): TagIdx =
    val symNme = scope.allocateName(TempSymbol(N, "mlx_exn"))
    ctx.getOrCreateWasmIntrinsicTag(
      "mlx_exn",
      ctx.addTag(TagInfo(
        id = SymIdx("mlx_exn"),
        typeUse = TypeUse(ctx.addType(
          sym = N,
          TypeInfo(
            id = SymIdx(symNme),
            FunctionType(params = Seq(WasmParam(SymIdx("ex"), RefType.anyref)), results = Seq.empty),
            objectTag = S(ctx.getFreshObjectTag()),
          ),
        )),
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
            params = Seq(WasmParam(SymIdx("glob_offset"), RefType.anyref), WasmParam(SymIdx("len"), RefType.anyref)),
            results = Seq(Result(RefType.anyref)),
          ),
          objectTag = N,
        ),
      )
      WasmImport(
        module = ExternIntrinsics.SystemModule,
        name = ExternIntrinsics.StringFromUtf16ImportName,
        externType = ExternType.Func(
          id = SymIdx(ExternIntrinsics.StringFromUtf16ImportName),
          typeUse = TypeUse(importTy),
        ),
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
  private def mkTempLocal(base: Str)(using Ctx, FunctionCtx, Scope, Raise): LocalIdx =
    funcCtx.addLocal(TempSymbol(N, base))

  /** Binds constructor self (`thisSym`) to the Wasm local name `this` in the current function context.
    */
  private def bindCtorThis(thisSym: Local)(using Ctx, FunctionCtx, Raise): LocalIdx =
    funcCtx.addLocal(thisSym, S("this"))

  /** Compiles a class init body under its own Wasm-local frame with explicit `this`. */
  private def setupInitLocals(
      clsLikeDefn: ClsLikeDefn,
  )(using Ctx, Raise, Scope, SessionExportCtx): (Expr, FunctionCtx) =
    genFuncBody(clsLikeDefn.paramsOpt.toList, thisSym = S(clsLikeDefn.isym)):
      val thisVar = funcCtx.lookupLocal_!(clsLikeDefn.isym, N)
      val preCtorWat = compilePreCtor(clsLikeDefn, thisVar)
      val ctorWat = block(clsLikeDefn.ctor)
      blockInstr(
        label = N,
        children = Seq(
          preCtorWat,
          ctorWat,
          `return`(S(local.get(thisVar, RefType.anyref))),
        ),
        resultTypes = Seq(Result(RefType.anyref)),
      )

  /** Lowers an inherited pre-constructor by preserving its setup code and rewriting the final `super(...)` into
    * `Parent_init(this, ...)`.
    */
  private def compilePreCtor(
      clsLikeDefn: ClsLikeDefn,
      thisVar: LocalIdx,
  )(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Expr =
    def withRest(block: NonBlockTail, rest: Block): Block = block match
      case Scoped(syms, _) => Scoped(syms, rest)
      case Begin(sub, _) => Begin(sub, rest)
      case TryBlock(sub, finallyDo, _) => TryBlock(sub, finallyDo, rest)
      case Assign(lhs, rhs, _) => Assign(lhs, rhs, rest)
      case af @ AssignField(lhs, nme, rhs, _) => AssignField(lhs, nme, rhs, rest)(af.symbol)
      case AssignDynField(lhs, fld, arrayIdx, rhs, _) => AssignDynField(lhs, fld, arrayIdx, rhs, rest)
      case Define(defn, _) => Define(defn, rest)
      case Match(scrut, arms, dflt, _) => Match(scrut, arms, dflt, rest)
      case Label(label, loop, body, _) => Label(label, loop, body, rest)

    def splitSuperTail(block: Block): Opt[Block -> Ls[Arg]] = block match
      case End(_) => N
      case Return(Call(Value.Ref(bs: BuiltinSymbol, _), args), true) if bs eq State.builtinOpsMap("super") =>
        S(End("") -> args)
      case b: NonBlockTail =>
        splitSuperTail(b.rest).map: (prefix, args) =>
          withRest(b, prefix) -> args
      case _ => N

    clsLikeDefn.preCtor match
      case End(_) => nop
      case _ =>
        splitSuperTail(clsLikeDefn.preCtor) match
          case S((prefixBlock, args)) =>
            val prefixWat = block(prefixBlock)
            resolveParentSym(clsLikeDefn) match
              case S(parentSym) =>
                val parentInitFunc = initFuncSym(parentSym)
                val superCall = call(
                  funcidx = ctx.getFunc_!(parentInitFunc),
                  operands = local.get(thisVar, RefType.anyref) +: args.map(argument),
                  returnTypes = Seq(Result(RefType.anyref)),
                )
                blockInstr(
                  label = N,
                  children = Seq(asStatement(prefixWat), drop(superCall)),
                  resultTypes = Seq.empty,
                )
              case N =>
                nop
          case N =>
            raise(ErrorReport(
              msg"Wasm preCtor lowering only supports lowered super(...) shapes." ->
                clsLikeDefn.sym.toLoc :: Nil,
              extraInfo = S(clsLikeDefn.preCtor.showAsTree),
              source = Diagnostic.Source.Compilation,
            ))
            nop
    end match
  end compilePreCtor

  /** Converts expression result types to WAT result clauses, dropping unreachable types. */
  private def resultClauses(expr: Expr): Seq[Result] =
    if expr.resultTypes.exists(_ is UnreachableType) then Seq.empty
    else expr.resultTypes.map(ty => Result(ty.asValType_!))

  /** Normalizes the exported `entry` body so it always returns single result. */
  private def normalizeEntryExpr(
      expr: Expr,
      isAbortive: Bool,
  )(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Expr =
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
  private def tupleArrayGet(tupleExpr: Expr, idxBuilder: Expr => Expr)(using Ctx, FunctionCtx, Raise, Scope): Expr =
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
  )(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Expr => Expr =
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

  def getVar(l: Local, loc: Opt[Loc])(using Ctx, FunctionCtx, Raise, Scope): Expr =
    singletonInfoFor(l) match
      case S(info) => singletonGlobalGet(info)
      case N => l match
          case ts: semantics.TermSymbol =>
            errExpr(
              Ls(msg"WatBuilder::getVar for TermSymbol not implemented yet" -> ts.toLoc),
              extraInfo = S(ts.toString),
            )
          case ts: semantics.ModuleOrObjectSymbol if ts.asMod.isDefined =>
            errExpr(
              Ls(
                msg"WatBuilder::getVar for ModuleOrObjectSymbol (`ts.asMod.isDefined`) not implemented yet" -> ts.toLoc,
              ),
              extraInfo = S(ts.toString),
            )
          case ts: semantics.InnerSymbol =>
            funcCtx.lookupLocal(ts) match
              case S(localIdx) => local.get(localIdx, RefType.anyref)
              case N =>
                errExpr(
                  Ls(
                    msg"WatBuilder::getVar for InnerSymbol `${ts.toString}` (symbol not in top-level scope) not implemented yet" ->
                      ts.toLoc,
                  ),
                  extraInfo = S(
                    s"Locals: ${(funcCtx.params ++ funcCtx.locals).toString}\nGlobals: ${ctx.getGlobals.toString}",
                  ),
                )
          case l =>
            funcCtx.lookupLocal(l) match
              case S(localIdx) => local.get(localIdx, RefType.anyref)
              case N if ctx.containsGlobal(l) =>
                global.get(GlobalIdx(SymIdx(scope.lookup_!(l, l.toLoc))), ctx.getGlobalType_!(l).globalType.valType)
              case _ =>
                errExpr(
                  Ls(
                    msg"Cannot find variable `${l.toString}` (${l.getClass.getSimpleName}) in local or global scope." ->
                      l.toLoc,
                  ),
                  extraInfo = S(
                    s"Locals: ${(funcCtx.params ++ funcCtx.locals).toString}\nGlobals: ${ctx.getGlobals.toString}",
                  ),
                )
  end getVar

  def argument(a: Arg)(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Expr =
    if a.spread.nonEmpty then
      errExpr(
        Ls(msg"WatBackend::argument for spread expression not implemented yet" -> a.value.toLoc),
        extraInfo = S(a.showAsTree),
      )
    else result(a.value)

  def operand(a: Arg)(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Expr =
    if a.spread.nonEmpty then die else subexpression(a.value)

  def subexpression(r: codegen.Result)(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Expr = r match
    case r: Lambda =>
      errExpr(
        Ls(msg"WatBuilder::subexpression for Lambda not implemented yet" -> r.toLoc),
        extraInfo = S(r.showAsTree),
      )
    case r => result(r)

  /** Returns the owning class symbol for a resolved field/member symbol, when available. */
  private def fieldOwner(sym: Symbol): Opt[BlockMemberSymbol] = sym match
    case ts: TermSymbol => ts.owner.flatMap(_.asBlkMember)
    case ms: MemberSymbol => ms.asTrm.flatMap(_.owner.flatMap(_.asBlkMember))
    case _ => N

  def fieldSelect(thisSym: BlockMemberSymbol, sym: DefinitionSymbol[?])(using Ctx, Raise): FieldIdx =
    val structInfo = ctx.getTypeInfo_!(thisSym)
    val symToField = structInfo.compType match
      case ty: StructType => ty.fieldsBySym
      case _ => lastWords(s"Cannot select field from non-struct type: ${structInfo.compType.toWat.mkString()}")
    val fieldIdx = symToField.get(sym).fold(lastWords(
      s"Missing field `${sym.toString}` in struct `${thisSym.toString}` with type `${structInfo.toWat.mkString()}`",
    )): field =>
      field.id
    FieldIdx(SymIdx(fieldIdx))
  end fieldSelect

  /** Resolves `sym` to a predeclared class method symbol, if any. */
  private def predeclaredClassMethodSym(sym: DefinitionSymbol[?])(using Ctx): Opt[BlockMemberSymbol] =
    sym.asBlkMember.filter: methodSym =>
      methodSym.asTrm.exists(_.owner.exists(_.asCls.isDefined)) && ctx.getFunc(methodSym).nonEmpty

  def result(r: codegen.Result)(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Expr = r match
    case Value.This(sym) =>
      // TODO(Derppening): Add type tracking and refinement for locals, remove the `ref.cast`
      ref.cast(
        local.get(funcCtx.lookupLocal_!(sym, sym.toLoc), RefType.anyref),
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
          if disamb.exists(_.isInstanceOf[ClassSymbol]) then
            errExpr:
              Ls(msg"Plain class references are not supported in Wasm; instantiate the class instead." -> r.toLoc)
          else
            ctx.getFunc(l) match
              case S(funcIdx) => ref.func(funcIdx, RefType(ctx.getFuncTypeUse_!(l).typeIdx, nullable = false))
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

    case Call(sel @ Select(qual, _), args) if sel.symbol.flatMap(predeclaredClassMethodSym).nonEmpty =>
      val methodSym = sel.symbol.flatMap(predeclaredClassMethodSym).get
      call(
        funcidx = ctx.getFunc_!(methodSym),
        operands = result(qual) +: args.map(argument),
        returnTypes = Seq(Result(RefType.anyref)),
      )

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
          fun match
            case Value.Ref(l, _) =>
              val base = fun match
                case Value.Ref(l, _) => ctx.getFunc(l)
                case _ => N
              val baseFuncIdx = base match
                case S(idx) => idx
                case N => return errExpr(
                    Ls(msg"Expected static function reference in Call(...) expression" -> fun.toLoc),
                    extraInfo = S(fun.toString),
                  )
              val baseTypeInfo = ctx.getTypeInfo_!(ctx.getFuncTypeUse_!(baseFuncIdx).typeIdx)
              val wasmArgs = args.map(argument)

              call(
                funcidx = baseFuncIdx,
                operands = wasmArgs.toSeq,
                returnTypes = baseTypeInfo.compType.asInstanceOf[FunctionType].sigType.results,
              )
            case _ =>
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
                          base.toWat.mkString()
                        }`\n... which has type `${
                          ty.fold("(none)")(_.toWat.mkString())
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

        case S(selSym) if predeclaredClassMethodSym(selSym).nonEmpty =>
          val methodSym = predeclaredClassMethodSym(selSym).get
          methodSym.asTrm.flatMap(_.defn) match
            case S(defn: TermDefinition) if defn.params.isEmpty =>
              call(
                funcidx = ctx.getFunc_!(methodSym),
                operands = Seq(result(qual)),
                returnTypes = Seq(Result(RefType.anyref)),
              )
            case _ =>
              errExpr(
                Ls(
                  msg"`${methodSym.toString}` is neither a field access nor a callable method" ->
                    sel.toLoc,
                ),
                extraInfo = S(sel),
              )

        case S(selSym: MemberSymbol) =>
          val qualRes = result(qual)
          val ownerInfo = fieldOwner(selSym)
          val selCls = fieldOwner(selSym) getOrElse:
            lastWords(
              s"Expected resolved class for Select(...) expression to be a BlockMemberSymbol, but got ${ownerInfo.fold("(none)")(
                  _.toString,
                )}",
            )
          val fieldidx = fieldSelect(selCls, selSym)
          struct.get(
            fieldidx,
            ref = ref.cast(qualRes, RefType(ctx.getType_!(selCls), nullable = false)),
            ty = RefType.anyref,
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
      call(funcidx = ctorFuncIdx, as.map(argument), Seq(Result(RefType.anyref)))

    case Tuple(mut, elems) =>
      val tupleValues = elems.map(argument)
      array.new_fixed(tupleArrayType(mut), tupleValues)

    case r =>
      errExpr(
        Ls(msg"WatBackend::result for ${r.getClass.getSimpleName} expression not implemented yet" -> r.toLoc),
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
    ctx.getOrCreateWasmIntrinsic(name, importIntrinsic(name))

  private def importIntrinsic(name: Str)(using Ctx, Raise, Scope): FuncIdx =
    val typeIdx = declareIntrinsicType(name)
    ctx.addFunctionImport(
      N,
      WasmImport(
        ExternIntrinsics.SystemModule,
        name,
        ExternType.Func(SymIdx(name), TypeUse(typeIdx)),
      ),
    )

  /** Creates the intrinsic definition for `name`.
    */
  private def createIntrinsic(name: Str, exportName: Opt[Str])(using Ctx, Raise, Scope): FuncIdx =
    if binaryOps.contains(name) then createBinaryInt31Func(name, binaryOps(name), exportName)
    else if unaryOps.contains(name) then createUnaryInt31Func(name, unaryOps(name), exportName)
    else lastWords(s"Unsupported wasm intrinsic '$name'")

  private def intrinsicParamSuffixes(name: Str): Seq[Str] =
    if binaryOps.contains(name) then Seq("lhs", "rhs") else Seq("arg")

  private def declareIntrinsicType(name: Str)(using Ctx, Raise, Scope): TypeIdx =
    ctx.addType(
      sym = N,
      TypeInfo(
        id = SymIdx(scope.allocateName(TempSymbol(N, name))),
        FunctionType(
          params = intrinsicParamSuffixes(name).map(nme => WasmParam(SymIdx(nme), RefType.anyref)),
          results = Seq(Result(RefType.anyref)),
        ),
        objectTag = N,
      ),
    )

  /** Creates a binary Int31 intrinsic with two parameters and body built from `op`.
    */
  private def createBinaryInt31Func(
      name: Str,
      op: (Expr, Expr) => Expr,
      exportName: Opt[Str],
  )(using Ctx, Raise, Scope): FuncIdx =
    val params = mkIntrinsicParams(name, Seq("lhs", "rhs"))
    val lhsName = params.head._2
    val rhsName = params(1)._2
    val body = binaryInt31Body(LocalIdx(lhsName), LocalIdx(rhsName), op)
    createIntrinsicFunc(name, params, body, exportName)

  /** Creates a unary Int31 intrinsic with a single parameter and body built from `op`.
    */
  private def createUnaryInt31Func(
      name: Str,
      op: Expr => Expr,
      exportName: Opt[Str],
  )(using Ctx, Raise, Scope): FuncIdx =
    val params = mkIntrinsicParams(name, Seq("arg"))
    val argName = params.head._2
    val body = unaryInt31Body(LocalIdx(argName), op)
    createIntrinsicFunc(name, params, body, exportName)

  /** Allocates the Wasm type and function definition for an intrinsic with the given signature.
    */
  private def createIntrinsicFunc(
      name: Str,
      params: Seq[TempSymbol -> SymIdx],
      body: Expr,
      exportName: Opt[Str],
  )(using Ctx, Raise, Scope): FuncIdx =
    val funcTy = declareIntrinsicType(name)
    val funcInfo = FuncInfo(
      id = SymIdx(scope.allocateName(TempSymbol(N, name))),
      typeUse = TypeUse(funcTy),
      params = params,
      locals = Seq.empty,
      body = body,
      resultTypes = Seq(Result(RefType.anyref)),
      exportName = exportName,
    )
    ctx.addFunc(N, funcInfo)
  end createIntrinsicFunc

  def intrinsicSupportModule()(using Raise, Scope): Document =
    val ctx = Ctx.empty
    given Ctx = ctx
    wasmIntrinsicNameSet.toSeq.sorted.foreach: name =>
      createIntrinsic(name, S(name))
    ctx.toWat

  /** Builds the body for an Int31 binary operator.
    */
  private def binaryInt31Body(
      lhsIdx: LocalIdx,
      rhsIdx: LocalIdx,
      op: (Expr, Expr) => Expr,
  )(using Ctx, Scope): Expr =
    val cond = i32.and(
      ref.test(getLocalAnyref(lhsIdx), RefType.i31ref),
      ref.test(getLocalAnyref(rhsIdx), RefType.i31ref),
    )
    val i31Op = ref.i31(op(getI32FromAnyref(lhsIdx), getI32FromAnyref(rhsIdx)))
    `if`(
      condition = cond,
      ifTrue = i31Op,
      ifFalse = S(unreachable),
      resultTypes = Seq(Result(RefType.anyref)),
    )

  /** Builds the body for an Int31 unary operator.
    */
  private def unaryInt31Body(paramIdx: LocalIdx, op: Expr => Expr)(using Ctx, Scope): Expr =
    val cond = ref.test(getLocalAnyref(paramIdx), RefType.i31ref)
    val i31Op = ref.i31(op(getI32FromAnyref(paramIdx)))
    `if`(
      condition = cond,
      ifTrue = i31Op,
      ifFalse = S(unreachable),
      resultTypes = Seq(Result(RefType.anyref)),
    )

  /** Creates parameters for an intrinsic.
    */
  private def mkIntrinsicParams(name: Str, suffixes: Seq[Str]): Seq[TempSymbol -> SymIdx] =
    suffixes.map: suffix =>
      val sym = TempSymbol(N, suffix)
      sym -> SymIdx(suffix)

  /** Loads the local `name` as an `anyref`.
    */
  private def getLocalAnyref(idx: LocalIdx): Expr =
    local.get(idx, RefType.anyref)

  /** Extracts the signed i32 value from the Int31 stored in the local `name`.
    */
  private def getI32FromAnyref(idx: LocalIdx): Expr =
    i31.get(ref.cast(getLocalAnyref(idx), RefType.i31ref), true)

  extension (expr: Expr)
    private def isControlTransfer: Bool =
      expr.resultType.contains(UnreachableType) || expr.mnemonic == "return"

  private def asStatement(expr: Expr): Expr =
    if expr.isControlTransfer then expr
    else
      expr.resultType match
        case S(_) => drop(expr)
        case N => expr

  def returningTerm(t: Block)(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Expr =
    t match
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
        val assignExpr = lExpr.mnemonicPrefix match
          case S("global") =>
            global.set(lExpr.instrargs(0).asInstanceOf[GlobalIdx], rExpr)
          case S("local") =>
            local.set(lExpr.instrargs(0).asInstanceOf[LocalIdx], rExpr)
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
          case S(selSym) =>
            selSym.asTrm match
              case S(fieldSym) =>
                val selOwner = fieldSym.owner getOrElse
                  lastWords(s"Expected resolved AssignField(...) expression `$fieldSym` to have an owner")
                val selCls = selOwner.asBlkMember getOrElse
                  lastWords(
                    s"Expected resolved class for AssignField(...) expression to be a BlockMemberSymbol, but got $selOwner (${
                        selOwner.getClass.getName
                      })",
                  )
                val fieldidx = fieldSelect(selCls, fieldSym)
                val objRef = ref.cast(lhsExpr, RefType(ctx.getType_!(selCls), nullable = false))
                struct.set(fieldidx, objRef, rhsExpr)
              case N =>
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
              case N =>
                val symExpr = getVar(sym, sym.toLoc)
                val defineExpr = symExpr.mnemonicPrefix match
                  case S("global") =>
                    global.set(symExpr.instrargs(0).asInstanceOf[GlobalIdx], result(p))
                  case S("local") =>
                    local.set(symExpr.instrargs(0).asInstanceOf[LocalIdx], result(p))
                  case _ =>
                    lastWords(
                      s"Expected `global.*` or `local.*` when compiling definition for `$sym`, but got ${symExpr.mnemonic}",
                    )
                val rstWat = returningTerm(rst)
                blockInstr(
                  label = N,
                  children = Seq(
                    defineExpr,
                    rstWat,
                  ),
                  resultTypes = rstWat.resultTypes.map(r => Result(r.asValType_!)),
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
                    val (bodyWat, fnCtx) = setupFunction(N, ps, result)
                    if sym.nameIsMeaningful then
                      val funcTy = ctx.addType(
                        sym = N,
                        TypeInfo(
                          id = SymIdx(scope.allocateName(TempSymbol(N, sym.nme))),
                          FunctionType(
                            params = fnCtx.params.map(p => WasmParam(p._2, RefType.anyref)),
                            results = Seq.fill(bodyWat.resultTypes.length)(Result(RefType.anyref)),
                          ),
                          objectTag = N,
                        ),
                      )

                      val funcInfo =
                        FuncInfo(
                          sym,
                          typeUse = TypeUse(funcTy),
                          params = ps.params.zip(fnCtx.params.map(_._2)).map((p, idx) => p.sym -> idx),
                          nResults = bodyWat.resultTypes.length,
                          locals = fnCtx.locals,
                          body = bodyWat,
                        )
                      ctx.addFunc(S(defn.sym), funcInfo)
                      if summon[SessionExportCtx].shouldExport(defn.sym) then
                        summon[SessionExportCtx].emit(SessionFunc(
                          sym = defn.sym,
                          moduleName = SessionBinding.ReplModuleName,
                          exportName = sym.nme,
                          funcType = FunctionType(funcInfo.getSignatureType),
                        ))

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
                    if isSingletonObj && clsLikeDefn.parentPath.nonEmpty then
                      break(errUnimplExpr("parentPath.nonEmpty for object"))
                    if isSingletonObj && clsLikeDefn.methods.nonEmpty then
                      break(errUnimplExpr("methods.nonEmpty for object"))
                    if clsLikeDefn.companion.isDefined then
                      break(errUnimplExpr("companion.isDefined"))

                    val ctorAuxParams = clsLikeDefn.auxParams.map: ps =>
                      ps.params.map: p =>
                        p -> errUnimplExpr("auxParams.nonEmpty")

                    // Use the symbolic type reference (e.g. `$Foo`) in emitted WAT for readability.
                    // Numeric indices are only needed for `$tag` values.
                    val typeref = ctx.getType_!(clsLikeDefn.sym)
                    val typeinfo = ctx.getTypeInfo_!(typeref)

                    val (initWat, initFnCtx) = setupInitLocals(clsLikeDefn)

                    // * If there are no ctor params, pop one param list off the aux params
                    val newCtorAuxParams = clsLikeDefn.paramsOpt match
                      case None => ctorAuxParams match
                          case head :: next => next
                          case Nil => ctorAuxParams
                      case Some(_) => ctorAuxParams

                    val tagValue = typeinfo.objectTag getOrElse:
                      lastWords(s"Expected class ${clsLikeDefn.sym} to have an object tag")

                    val initFuncRef = initFuncSym(clsLikeDefn.sym)
                    val (ctorCode, ctorFnCtx) = genFuncBody(clsLikeDefn.paramsOpt.toList, thisSym = N):
                      val thisVar = bindCtorThis(clsLikeDefn.isym)
                      val initCall = call(
                        funcidx = ctx.getFunc_!(initFuncRef),
                        operands = local.get(thisVar, RefType.anyref) +:
                          funcCtx.params.map((_, nme) => getLocalAnyref(LocalIdx(nme))),
                        returnTypes = Seq(Result(RefType.anyref)),
                      )
                      blockInstr(
                        label = N,
                        Seq(
                          local.set(thisVar, struct.new_default(typeref)),
                          struct.set(
                            FieldIdx(SymIdx(typeinfo.compType.asInstanceOf[StructType].fields(0)._2.id)),
                            ref.cast(
                              local.get(thisVar, RefType.anyref),
                              RefType(typeref, nullable = false),
                            ),
                            i32.const(tagValue),
                          ),
                          drop(initCall),
                          `return`(S(local.get(thisVar, RefType(typeref, nullable = false)))),
                        ),
                        resultTypes = Seq(Result(RefType.anyref)),
                      )

                    val ctorAux =
                      if newCtorAuxParams.isEmpty then ctorCode
                      else break(errUnimplExpr("newCtorAuxParams.nonEmpty"))

                    val predeclaredInit = ctx.getFuncInfo_!(initFuncRef)
                    ctx.addFunc(
                      S(initFuncRef),
                      FuncInfo(
                        id = predeclaredInit.id,
                        typeUse = predeclaredInit.typeUse,
                        params = initFnCtx.params,
                        resultTypes = initWat.resultTypes.map(ty => Result(ty.asValType_!)),
                        locals = initFnCtx.locals,
                        body = initWat,
                        exportName = predeclaredInit.exportName,
                      ),
                    )

                    val predeclaredCtor = ctx.getFuncInfo_!(clsLikeDefn.sym)
                    ctx.addFunc(
                      S(clsLikeDefn.sym),
                      FuncInfo(
                        id = predeclaredCtor.id,
                        typeUse = predeclaredCtor.typeUse,
                        params = ctorFnCtx.params,
                        resultTypes = ctorAux.resultTypes.map(ty => Result(ty.asValType_!)),
                        locals = ctorFnCtx.locals,
                        body = ctorAux,
                        exportName = predeclaredCtor.exportName,
                      ),
                    )

                    def overwriteMethod(
                        sym: BlockMemberSymbol,
                        ps: ParamList,
                        bod: Block,
                    ): Unit =
                      val (bodyWat, fnCtx) = setupFunction(S(clsLikeDefn.isym), ps, bod)
                      val predeclaredMethod = ctx.getFuncInfo_!(sym)
                      ctx.addFunc(
                        S(sym),
                        FuncInfo(
                          id = predeclaredMethod.id,
                          typeUse = predeclaredMethod.typeUse,
                          params = fnCtx.params,
                          resultTypes = Seq.fill(bodyWat.resultTypes.length)(Result(RefType.anyref)),
                          locals = fnCtx.locals,
                          body = bodyWat,
                          exportName = predeclaredMethod.exportName,
                        ),
                      )

                    clsLikeDefn.methods.foreach:
                      case FunDefn(_, sym, _, Nil, bod) =>
                        overwriteMethod(sym, PlainParamList(Nil), bod)
                      case FunDefn(_, sym, _, ps :: Nil, bod) =>
                        overwriteMethod(sym, ps, bod)
                      case methodDefn =>
                        lastWords(
                          s"Class method `$methodDefn` with multiple parameter lists should be rejected in predeclaration pass",
                        )
                    if summon[SessionExportCtx].shouldExport(clsLikeDefn.sym) then
                      summon[SessionExportCtx].emit(SessionClass(
                        sym = clsLikeDefn.sym,
                        typeInfo = typeinfo,
                        runtimeTags = ctx.getAllRuntimeTags(clsLikeDefn.sym).getOrElse(LinkedHashSet(tagValue)),
                        aliasSyms = clsLikeDefn.isym match
                          case mos: ModuleOrObjectSymbol => mos :: Nil
                          case _ => Nil,
                      ))
                      if !isSingletonObj && clsLikeDefn.sym.nameIsMeaningful then
                        summon[SessionExportCtx].emit(SessionFunc(
                          sym = clsLikeDefn.sym,
                          moduleName = SessionBinding.ReplModuleName,
                          exportName = clsLikeDefn.sym.nme,
                          funcType = FunctionType(
                            SignatureType(
                              params = ctorFnCtx.params.map(p => WasmParam(p._2, RefType.anyref)),
                              results = Seq(Result(RefType.anyref)),
                            ),
                          ),
                        ))
                    end if
                    if isSingletonObj then
                      registerSingletonInit(clsLikeDefn, typeref)
                      if summon[SessionExportCtx].shouldExport(clsLikeDefn.sym) then
                        ctx.getSingletonInfo(clsLikeDefn.sym).foreach: info =>
                          val singletonOwner = clsLikeDefn.isym match
                            case mos: ModuleOrObjectSymbol => S(mos)
                            case _ => N
                          summon[SessionExportCtx].emit(SessionSingleton(
                            blockSym = clsLikeDefn.sym,
                            objectSym = singletonOwner,
                            moduleName = SessionBinding.ReplModuleName,
                            exportName = info.globalName,
                            globalTy = info.globalTy,
                          ))

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
          case S(refTy: RefType) =>
            refTy.heapType match
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
          case S(refTy: RefType) =>
            refTy.heapType match
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
        funcCtx.lookupLabel(label) match
          case S(target) => br(target.breakLabel)
          case N =>
            errExpr(
              Ls(
                msg"WatBuilder::returningTerm for Break(...) to unknown label `${label.nme}`" -> label.toLoc,
              ),
              extraInfo = S(t.showAsTree),
            )
      case Continue(label) =>
        funcCtx.lookupLabel(label) match
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
                    children = Seq(bodyStmt),
                    resultTypes = Seq.empty,
                  ),
                ),
                resultTypes = Seq.empty,
              )
            else
              blockInstr(
                label = S(breakLabel),
                children = Seq(bodyStmt),
                resultTypes = Seq.empty,
              )

        val rstExpr = returningTerm(rst)
        val rstResultTypes = rstExpr.resultTypes.flatMap(ty => ty.asValType.map(Result(_)))
        blockInstr(
          label = N,
          children = Seq(labeledRegion, rstExpr),
          resultTypes = rstResultTypes,
        )
      case Match(scrut, arms, dflt, rst) =>
        val tailMode = rst.isInstanceOf[End]
        val matchResLocal =
          if tailMode then S(mkTempLocal("matchRes"))
          else N

        def getScrutExpr: Expr = result(scrut)

        def assignTailResult(target: LocalIdx, expr: Expr): Expr =
          if expr.isControlTransfer then expr
          else
            expr.resultType match
              case S(_) => local.set(target, expr)
              case N => blockInstr(
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
        val matchBlock = funcCtx.withLabel(LabelSymbol(N, "match"), hasContinueLabel = false):
          case LabelTarget(matchLabel, _) =>
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
                    funcCtx.withLabel(LabelSymbol(N, "arm"), hasContinueLabel = false):
                      case LabelTarget(armLabel, _) =>
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
                    val clsBlkMemberSym = cls.asBlkMember getOrElse:
                      break(errExpr(
                        Ls(msg"Could not resolve BlockMemberSymbol for class pattern" -> cls.toLoc),
                        extraInfo = S(s"ClassLikeSymbol: ${cls.toString}"),
                      ))
                    val clsTypeIdx = ctx.getType_!(clsBlkMemberSym)
                    val typeinfo = ctx.getTypeInfo_!(clsTypeIdx)

                    val expectedTag = typeinfo.objectTag getOrElse:
                      lastWords(s"Expected class $clsBlkMemberSym to have an object tag")

                    // TODO (https://github.com/orgs/hkust-taco/projects/14/views/1?pane=issue&itemId=174476970):
                    // replace with RTTI ancestry checks once each object carries runtime type information.
                    val matchTags = ctx.getAllRuntimeTags(clsBlkMemberSym).getOrElse(LinkedHashSet(expectedTag))

                    val scrutExpr = getScrutExpr
                    val isStructCompatible = ref.test(scrutExpr, baseObjectRefType(nullable = true))

                    val bodyExpr = returningTerm(body)
                    val armBodyExpr = lowerMatchBody(bodyExpr)

                    // Safe to cast and extract tag since ref.test passed
                    val scrutAsObject = ref.cast(scrutExpr, baseObjectRefType(nullable = false))
                    val scrutTag = struct.get(
                      FieldIdx(SymIdx(typeinfo.compType.asInstanceOf[StructType].fields(0)._2.id)),
                      scrutAsObject,
                      I32Type,
                    )
                    val tagMatches = matchTags.toList match
                      case tag :: Nil => i32.eq(scrutTag, i32.const(tag))
                      case tag :: rest =>
                        rest.foldLeft[Expr](i32.eq(scrutTag, i32.const(tag))): (acc, candidateTag) =>
                          i32.or(acc, i32.eq(scrutTag, i32.const(candidateTag)))
                      case Nil =>
                        lastWords(s"Expected class $clsBlkMemberSym to have at least one accepted runtime tag")

                    funcCtx.withLabel(LabelSymbol(N, "arm"), hasContinueLabel = false):
                      case LabelTarget(armLabel, _) =>
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
                    funcCtx.withLabel(LabelSymbol(N, "arm"), hasContinueLabel = false):
                      case LabelTarget(armLabel, _) =>
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
                      Ls(
                        msg"WatBuilder::returningTerm for Match(...) with case `${cse.toString}` not implemented yet" ->
                          N,
                      ),
                      extraInfo = S(cse.toString),
                    ))
                end match

              val defaultExpr =
                val rawDefaultExpr = dflt match
                  case S(defaultBody) => returningTerm(defaultBody)
                  case N => nop
                lowerMatchBody(rawDefaultExpr)

              // Generate the match block
              blockInstr(
                label = S(matchLabel),
                children = matchResInitExpr.toSeq ++ armExprs :+ defaultExpr,
                resultTypes = Seq.empty,
              )

        if tailMode then
          blockInstr(
            label = N,
            children = Seq(
              matchBlock,
              local.get(matchResLocal.get, RefType.anyref),
            ),
            resultTypes = Seq(Result(RefType.anyref)),
          )
        else
          val rstExpr = returningTerm(rst)
          blockInstr(
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
          Ls(msg"WatBuilder::returningTerm for ${t.getClass.getSimpleName} block not implemented yet" -> N),
          extraInfo = S(t.showAsTree),
        )
    end match
  end returningTerm

  def program(
      p: Program,
      exprt: Opt[BlockMemberSymbol],
      wd: io.Path,
      sessionImports: Seq[SessionBinding],
      preservedSessionSymbols: Set[Local],
  )(using Raise, Scope): CompiledWasmModule =
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

    val sessionExportCtx = SessionExportCtx(
      symbolsToExport = preservedSessionSymbols,
      collectedBindings = ArrayBuf.empty,
    )
    given SessionExportCtx = sessionExportCtx

    val ctx = Ctx.empty
    given Ctx = ctx

    def systemMemMinPages: Int =
      ctx.getMemoryImport(
        ExternIntrinsics.SystemModule,
        ExternIntrinsics.SystemMemoryImportName,
      ).fold(0)(_.memType.lim.min)

    def compiledModule(entryName: Str): CompiledWasmModule =
      CompiledWasmModule(ctx.toWat, entryName, systemMemMinPages, sessionExportCtx.collectedBindings.toSeq)

    // Create base Object struct with tag field that all other structs will inherit
    ctx.addType(
      sym = S(baseObjectSym),
      TypeInfo(
        id = SymIdx("Object"),
        StructType(Seq(tagFieldSym -> Field(I32Type, mutable = true, id = "$tag"))),
        objectTag = S(ctx.getFreshObjectTag() ensuring (_ == 0)),
      ),
    )

    registerSessionImports(sessionImports)

    collectSessionGlobalSymbols(
      p.main,
      sessionExportCtx,
    ).toSeq.sortBy(_.uid).foreach: sym =>
      registerSessionGlobal(sym)

    boundary[CompiledWasmModule]:
      val outerRaise = summon[Raise]

      // Early registration scheme: collect supported top-level classes from main block,
      // order by inheritance, predeclare struct types, init functions, and constructors.
      locally:
        given Raise = diag =>
          outerRaise(diag)
          diag match
            case _: ErrorReport => break(compiledModule("entry"))
            case _ => ()
        val ordered = sortTopLevelClasses(collectTopLevelClassDefns(p.main))
        ordered.foreach(predeclareClassType)
        predeclareClassTags(ordered)
        ordered.foreach(predeclareClassInit)
        ordered.foreach(predeclareClassConstructor)
        ordered.foreach(predeclareClassMethods)

      // Compile the entry function under a dedicated local scope so that any temp locals introduced
      // during codegen (e.g., via `local.tee`) are declared in the entry function.
      val (entryFnExpr, entryFnCtx) = genFuncBody(Nil, thisSym = N):
        val rawEntryFnExpr = block(p.main)
        normalizeEntryExpr(rawEntryFnExpr, p.main.isAbortive)

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
        typeUse = TypeUse(entryFnTy),
        params = Seq.empty,
        resultTypes = Seq(Result(RefType.anyref)),
        locals = entryFnCtx.locals,
        body = entryFnExpr,
        exportName = S(entryNme),
      )

      if stringLits.nonEmpty then
        stringLits.foreach: (s, lit) =>
          if lit.byteLen > 0 then
            ctx.addDataSegment(DataSegment.Active(
              id = SymIdx(scope.allocateName(TempSymbol(N, s.take(WatBuilder.StringConstantIdentMaxLength)))),
              offset = i32.const(lit.offset),
              bytes = lit.watBytes,
              memuse = N,
            ))

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
            typeUse = TypeUse(initTy),
            params = Seq.empty,
            resultTypes = Seq.empty,
            locals = Seq.empty,
            body = initBody,
            exportName = N,
          ),
        )
        ctx.setStartFunc(initFn)
      end if

      ctx.addFunc(S(entrySym), entryFnInfo)

      compiledModule(entryNme)
  end program

  def blockPreamble(ss: Iterable[Symbol])(using Ctx, FunctionCtx, Raise, Scope): Seq[Local] =
    val vars = ss.filter(sym =>
      scope.lookup(sym).toSeq.isEmpty
        && !ctx.containsGlobal(sym)
        && ctx.getFunc(sym).isEmpty,
    ).toSeq
      .toArray
      .sortBy(_.uid)
      .iterator
      .map: l =>
        scope.allocateName(l)
        l
      .toSeq
    vars.foreach: v =>
      funcCtx.addLocal(v)
    vars

  def nonNestedScoped(
      blk: Block,
  )(k: Block => Expr)(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Expr = blk match
    case Scoped(syms, body) =>
      blockPreamble(syms.view.filter(body.freeVars))
      k(body)
    case _ => k(blk)

  def block(t: Block)(using Ctx, FunctionCtx, Raise, Scope, SessionExportCtx): Expr =
    nonNestedScoped(t)(returningTerm)

  def setupFunction(
      thisParam: Opt[InnerSymbol],
      params: ParamList,
      body: Block,
  )(using Ctx, Raise, Scope, SessionExportCtx): (Expr, FunctionCtx) =
    genFuncBody(params :: Nil, thisSym = thisParam):
      block(body)

end WatBuilder
