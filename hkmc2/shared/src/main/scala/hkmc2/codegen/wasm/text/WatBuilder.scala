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

  /** Synthetic base struct symbol for shared runtime type information objects. */
  private val typeInfoBaseSym: BlockMemberSymbol = BlockMemberSymbol("TypeInfoBase", Nil)

  /** Synthetic base struct symbol for all heap-allocated class instances. */
  private val baseObjectSym: BlockMemberSymbol = BlockMemberSymbol("Object", Nil)

  /** Synthetic field symbol for the object-header pointer to a class's shared RTTI object. */
  private val typeInfoFieldSym: TermSymbol = TermSymbol(syntax.MutVal, owner = N, Ident("$typeinfo"))

  /** Synthetic field symbol for the runtime class tag stored in RTTI. */
  private val tagFieldSym: TermSymbol = TermSymbol(syntax.MutVal, owner = N, Ident("$tag"))

  /** Synthetic field symbol for the direct-parent RTTI reference used by runtime subtype checks. */
  private val parentFieldSym: TermSymbol = TermSymbol(syntax.MutVal, owner = N, Ident("$parent"))

  private case class StringLitInfo(offset: Int, byteLen: Int, watBytes: Str)
  private val stringLits: LinkedHashMap[Str, StringLitInfo] = LinkedHashMap.empty
  private val initFuncSyms: LinkedHashMap[BlockMemberSymbol, BlockMemberSymbol] = LinkedHashMap.empty
  private val typeInfoTypeIdxs: LinkedHashMap[BlockMemberSymbol, TypeIdx] = LinkedHashMap.empty
  private val typeInfoGlobals: LinkedHashMap[BlockMemberSymbol, GlobalIdx] = LinkedHashMap.empty
  private var nextStringDataOffset: Int = 0

  /** Returns the Wasm type index of the synthetic base object header struct. */
  private def baseObjectTypeIdx(using Ctx): TypeIdx =
    ctx.getType_!(baseObjectSym)

  /** Returns the Wasm type index of the synthetic base RTTI struct. */
  private def typeInfoBaseTypeIdx(using Ctx): TypeIdx =
    ctx.getType_!(typeInfoBaseSym)

  /** Resolves the field index for a field inside a previously registered struct type. */
  private def structFieldIdx(typeSym: BlockMemberSymbol, fieldSym: TermSymbol)(using Ctx): FieldIdx =
    ctx.getTypeInfo_!(typeSym).compType match
      case struct: StructType =>
        struct.fields.collectFirst:
          case (sym, field) if sym == fieldSym => FieldIdx(SymIdx(field.id))
        .getOrElse:
          lastWords(s"missing struct field $fieldSym in registered struct type $typeSym")
      case other =>
        lastWords(s"expected registered struct type for $typeSym when resolving field $fieldSym, found $other")

  /** Loads this module's RTTI singleton for `sym`, if one has been registered. */
  private def getClassTypeInfoGlobal(sym: BlockMemberSymbol)(using Ctx, Raise): Opt[Expr] =
    typeInfoGlobals.get(sym).map: globalIdx =>
      val globalTy = ctx.getGlobalType_!(globalIdx).globalType.valType
      global.get(globalIdx, globalTy)

  /** Reads the RTTI pointer stored in an object's common header. */
  private def readObjectTypeInfo(objRef: Expr)(using Ctx): Expr =
    struct.get(
      structFieldIdx(baseObjectSym, typeInfoFieldSym),
      ref.cast(objRef, baseObjectRefType(nullable = false)),
      RefType(typeInfoBaseTypeIdx, nullable = false),
    )

  /** Follows one direct-parent RTTI reference from a shared class `typeinfo` object. */
  private def readTypeInfoParent(typeInfoRef: Expr)(using Ctx): Expr =
    struct.get(
      structFieldIdx(typeInfoBaseSym, parentFieldSym),
      ref.cast(typeInfoRef, RefType(typeInfoBaseTypeIdx, nullable = false)),
      RefType(typeInfoBaseTypeIdx, nullable = true),
    )

  /** Builds the reference type for the synthetic base object header struct. */
  private def baseObjectRefType(nullable: Bool)(using Ctx): RefType =
    RefType(baseObjectTypeIdx, nullable = nullable)

  /** Casts an expression to `target` type if the result type does not match with `target`. */
  private def castConserve(expr: Expr, target: RefType): Expr =
    require(expr.resultTypes.size == 1, "expected single-result expression for cast")
    if expr.resultType.contains(target) then expr else ref.cast(expr, target)

  /** Returns the default Wasm value for one struct field when eagerly constructing an object instance. */
  private def defaultStructFieldValue(field: Field)(using Ctx, Raise): Expr = field.ty match
    case refTy: RefType if refTy.nullable => ref.`null`(refTy.heapType)
    case refTy: RefType =>
      lastWords(s"non-null ref field `${field.id}` requires an explicit initializer")
    case other =>
      lastWords(s"unsupported default field type `${other.toWat.mkString()}` for eager object construction")

  /** Returns `1` when `scrutTypeInfo` is equal to or descends from `targetTypeInfo`, else `0`. */
  private def isSubtypeByTypeInfo(
      scrutTypeInfo: Expr,
      targetTypeInfo: Expr,
  )(using Ctx, FunctionCtx, Raise): Expr =
    val currentTmp = mkTempLocal("currentTypeInfo")
    val targetTmp = mkTempLocal("targetTypeInfo")
    val resultTmp = mkTempLocal("typeInfoMatch")
    funcCtx.withLabel(LabelSymbol(N, "typeInfo"), hasContinueLabel = true):
      case LabelTarget(breakLabel, S(continueLabel)) =>
        blockInstr(
          label = N,
          children = Seq(
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
                      ifTrue = blockInstr(
                        label = N,
                        children = Seq(
                          local.set(resultTmp, ref.i31(i32.const(1))),
                          br(breakLabel),
                        ),
                        resultTypes = Seq.empty,
                      ),
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
          ),
          resultTypes = Seq(Result(I32Type)),
        )
      case LabelTarget(_, N) =>
        lastWords("unreachable: loop-based RTTI traversal expects a continue label")

  /** True if this top-level class can be declared as a Wasm struct type. */
  private def isSupportedTopLevelClass(defn: ClsLikeDefn): Bool =
    defn.owner.isEmpty
      && ((defn.k is syntax.Cls) || (defn.k is syntax.Obj))
      && (!(defn.k is syntax.Obj) || defn.parentPath.isEmpty)
      && (!(defn.k is syntax.Obj) || defn.methods.isEmpty)
      && defn.companion.isEmpty

  /** Returns singleton metadata when `sym` resolves to a registered singleton object. */
  private def singletonInfoFor(sym: ValueSymbol)(using Ctx): Opt[SingletonInfo] =
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
      auxParams = PlainParamList(Nil) :: Nil,
      parentPath = N,
      methods = Nil,
      privateFields = Nil,
      publicFields = Nil,
      preCtor = End(""),
      ctor = End(""),
      companion = N,
      bufferable = N,
    )(N, Nil)

  /** Registers the synthetic `Unit` singleton. */
  private def RegisterUnitSingleton()(using Ctx, FunctionCtx, Raise, SessionExportCtx): Unit =
    val unitDefn = syntheticUnitDefn
    val singletonOwner = unitDefn.isym match
      case mos: ModuleOrObjectSymbol => S(mos)
      case _ => N
    if ctx.containsSingleton(unitDefn.sym) then return

    if ctx.getType(unitDefn.sym).isEmpty then
      predeclareClassTypeInfoType(unitDefn)
      predeclareClassType(unitDefn)
      predeclareClassInit(unitDefn)
      predeclareClassConstructor(unitDefn)
      predeclareClassTypeInfoGlobal(unitDefn)

    returningTerm(Define(unitDefn, End("")))

    val typeInfo = ctx.getTypeInfo_!(unitDefn.sym)
    val unitRttiTypeInfo = ctx.getTypeInfo_!(typeInfoTypeIdxs(unitDefn.sym))
    val unitTypeInfoGlobalInfo = ctx.getGlobalInfo_!(typeInfoGlobals(unitDefn.sym))
    val singletonInfo = ctx.getSingletonInfo(unitDefn.sym) getOrElse:
      lastWords("Missing singleton metadata for synthetic Unit object")
    // Record session metadata for the synthetic Unit singleton.
    summon[SessionExportCtx].emit(SessionClass(
      sym = unitDefn.sym,
      wrapId = typeInfo.wrapId,
      compType = typeInfo.compType,
      objectTag = typeInfo.objectTag,
      rttiTypeInfo = unitRttiTypeInfo,
      rttiGlobalExportName = unitTypeInfoGlobalInfo.exportName.get,
      aliasSyms = singletonOwner.toSeq,
    ))
    summon[SessionExportCtx].emit(SessionSingleton(
      blockSym = unitDefn.sym,
      wrapId = N -> N,
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
  )(using Ctx, Raise): Unit =
    if ctx.containsSingleton(clsLikeDefn.sym) then return
  
    val globalSym = BlockMemberSymbol(s"${clsLikeDefn.sym.nme}$$inst", Nil, nameIsMeaningful = false)
    val globalTy = RefType(typeref, nullable = true)

    val globalInfo = GlobalInfo(
      globalType = GlobalType(globalTy, mutable = true),
      init = ref.`null`(typeref),
      exportName = S(globalSym.nme),
      sym = globalSym,
    )
    val globalIdx = ctx.addGlobal(globalInfo)

    val singletonOwner = clsLikeDefn.isym match
      case mos: ModuleOrObjectSymbol => S(mos)
      case _ => N
    val info = SingletonInfo(globalInfo.id.id, globalTy)
    ctx.registerSingleton(clsLikeDefn.sym, singletonOwner, info)

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
      case S(Value.MemberRef(sym, _)) =>
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

  /** Returns the elaborated semantic class definition for this lowered class. */
  private def semanticClassDef(defn: ClsLikeDefn)(using Raise): hkmc2.semantics.ClassLikeDef =
    defn.isym.defn match
      case S(clsDef: hkmc2.semantics.ClassLikeDef) => clsDef
      case _ =>
        lastWords(s"Expected definition of class `${defn.sym}` to be present")

  /** Returns the elaborated source methods for this class. */
  private def semanticMethodDefs(defn: ClsLikeDefn)(using Raise): List[TermDefinition] =
    semanticClassDef(defn).body.methods.filter(_.body.nonEmpty)

  /** Resolves the exact overridden parent method symbol for `methodDef`, if any. */
  private def overriddenParentMethodSym(
      defn: ClsLikeDefn,
      methodDef: TermDefinition,
  )(using Raise): Opt[BlockMemberSymbol] =
    resolveParentSym(defn).flatMap(_.asClsOrMod.flatMap(_.defn)) match
      case S(parentDef: hkmc2.semantics.ClassLikeDef) =>
        parentDef.body.members.get(methodDef.sym.nme).flatMap(_.asTrm.flatMap(_.defn)) match
          case S(parentMethodDef: TermDefinition) if parentMethodDef.k is syntax.Fun => S(parentMethodDef.sym)
          case _ => N
      case _ => N

  /** True when a method introduces a new virtual slot at its declaring class if not already inherited. */
  private def declaresVirtualSlot(methodDef: TermDefinition): Bool =
    methodDef.annotations.exists:
      case Annot.Modifier(syntax.Keyword.`virtual`) => true
      case _ => false

  /** Computes one derived virtual-table layout for one top-level class. */
  private def predeclareClassVirtualTable(defn: ClsLikeDefn)(using Ctx, Raise): Unit =
    val parentVirtualTable = resolveParentSym(defn).flatMap(ctx.getVirtualTable)
      .getOrElse(Ctx.VirtualTable(Nil, Map.empty))
    val virtualMethods = ArrayBuf.from(parentVirtualTable.virtualMethods)
    val virtualMethodSlots = LinkedHashMap.from(parentVirtualTable.virtualMethodSlots)

    // FIXME: LP: why do we need to access elaborated Term methods, here?! We should just be able to look at the IR definitions, and if that's not enough, we should put the required info there...
    semanticMethodDefs(defn).foreach: methodDef =>
      val slotIdx = overriddenParentMethodSym(defn, methodDef).flatMap(parentVirtualTable.virtualMethodSlots.get)
      slotIdx match
        case S(slot) =>
          virtualMethods(slot) = methodDef.sym
          virtualMethodSlots(methodDef.sym) = slot
        case N if declaresVirtualSlot(methodDef) =>
          val slot = virtualMethods.size
          virtualMethods += methodDef.sym
          virtualMethodSlots(methodDef.sym) = slot
        case N => ()

    ctx.registerVirtualTable(
      defn.sym,
      Ctx.VirtualTable(
        virtualMethods = virtualMethods.toList,
        virtualMethodSlots = virtualMethodSlots.toMap,
      ),
    )

  /** Declares one supported top-level class type for early wasm registration. */
  private def predeclareClassType(defn: ClsLikeDefn)(using Ctx, Raise): Unit =
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

    ctx.addType(TypeInfo(
      sym = defn.sym,
      compType = StructType(fields = allFields, parents = Seq(parentTypeIdx)),
      objectTag = S(runtimeTag),
    ))
  end predeclareClassType
  /** Declares the shared Wasm function type used by a class-associated function placeholder. */
  private def declareClassFuncType(
      defn: ClsLikeDefn,
      suffix: Str,
      params: Seq[ValueSymbol -> SymIdx],
  )(using Ctx, Raise): TypeIdx =
    ctx.addType(TypeInfo(
      sym = TempSymbol(N, defn.sym.nme),
      FunctionType(
        params = params.map(p => WasmParam(p._2, RefType.anyref)),
        results = Seq(Result(RefType.anyref)),
      ),
      objectTag = N,
      wrapId = N -> S(suffix),
    ))

  /** Returns the shared erased Wasm function signature for a virtual method arity, including `this`. */
  private def virtualMethodSignature(arity: Int): FunctionType =
    FunctionType(
      params = (0 until arity).map: idx =>
        WasmParam(SymIdx(if idx == 0 then "this" else s"arg$idx"), RefType.anyref),
      results = Seq(Result(RefType.anyref)),
    )

  /** Declares (and caches) the shared Wasm function type for a virtual method arity, including `this`. */
  private def virtualMethodFuncType(arity: Int)(using Ctx, Raise): TypeIdx =
    ctx.getOrCreateWasmIntrinsicType(WasmIntrinsicType.VirtualMethod(arity)):
      ctx.addType(TypeInfo(
        sym = TempSymbol(N, s"virtual$arity"),
        compType = virtualMethodSignature(arity),
        objectTag = N,
      ))
  end virtualMethodFuncType

  /** Returns the symbol used to predeclare and later overwrite a class init function. */
  private def initFuncSym(sym: BlockMemberSymbol): BlockMemberSymbol =
    initFuncSyms.getOrElseUpdate(sym, BlockMemberSymbol("init", Nil, nameIsMeaningful = false))

  /** Registers a placeholder class-associated function so later lowering can overwrite it. */
  private def predeclareClassFunc(
      defn: ClsLikeDefn,
      suffix: Str,
      params: Seq[ValueSymbol -> SymIdx],
      sym: BlockMemberSymbol,
      exportName: Opt[Str],
  )(using Ctx, Raise): Unit =
    val funcTy = declareClassFuncType(defn, suffix, params)
    predeclareClassFuncWithType(defn, suffix, params, sym, exportName, funcTy)

  /** Registers a placeholder class-associated function using a predeclared Wasm function type. */
  private def predeclareClassFuncWithType(
      defn: ClsLikeDefn,
      suffix: Str,
      params: Seq[ValueSymbol -> SymIdx],
      sym: BlockMemberSymbol,
      exportName: Opt[Str],
      funcTy: TypeIdx,
  )(using Ctx, Raise): Unit =
    ctx.addFunc(FuncInfo(
      sym,
      wrapId = if sym.asClsOrMod.isDefined then (N -> S("ctor")) else (S(defn.sym.nme) -> N),
      typeUse = TypeUse(funcTy),
      params = params,
      resultTypes = Seq(Result(RefType.anyref)),
      locals = Seq.empty,
      body = ref.`null`(ctx.getType_!(defn.sym)),
      exportName = exportName,
    ))
  end predeclareClassFuncWithType

  /** Returns the single flattened constructor parameter list.
    * After ClassParamFlattener, all classes have paramsOpt = N and exactly one auxParams entry. */
  private def classCtorParamList(defn: ClsLikeDefn): ParamList =
    assert(defn.paramsOpt.isEmpty,
      s"WatBuilder: expected paramsOpt to be None after flattening for class ${defn.sym.nme}")
    assert(defn.auxParams.sizeCompare(1) == 0,
      s"WatBuilder: expected exactly one auxParams entry after flattening for class ${defn.sym.nme}")
    defn.auxParams.head

  /** Declares one top-level class init function. */
  private def predeclareClassInit(defn: ClsLikeDefn)(using Ctx, Raise): Unit =
    val pl = classCtorParamList(defn)
    val initParams = (defn.isym -> SymIdx("this")) +:
      pl.params.map: p =>
        p.sym -> SymIdx(p.sym.nme)
    predeclareClassFunc(defn, "init", initParams, initFuncSym(defn.sym), N)

  /** Declares one top-level class constructor. */
  private def predeclareClassConstructor(defn: ClsLikeDefn)(using Ctx, Raise): Unit =
    val ctorParams = classCtorParamList(defn).params.map: p =>
      p.sym -> SymIdx(p.sym.nme)
    val ctorExportName = defn.sym
      .optionIf: sym =>
        !(defn.k is syntax.Obj) && sym.nameIsMeaningful
      .map(_.nme)
    predeclareClassFunc(defn, "ctor", ctorParams, defn.sym, ctorExportName)

  /** Registers all Wasm pre-declarations needed for one top-level class, in dependency order. */
  private def predeclareClass(defn: ClsLikeDefn)(using Ctx, Raise, SessionExportCtx): Unit =
    predeclareClassVirtualTable(defn)
    predeclareClassTypeInfoType(defn)
    predeclareClassType(defn)
    predeclareClassInit(defn)
    predeclareClassConstructor(defn)
    predeclareClassMethods(defn)
    predeclareClassTypeInfoGlobal(defn)

  /** Collects the symbols that should live in mutable globals so later REPL blocks can import them.
    *
    * TODO: replace this structural scan with an explicit "session-visible bindings" set from lowering once that
    * information is available directly in the IR.
    */
  private def collectSessionGlobalSymbols(
      b: Block,
      sessionExportCtx: SessionExportCtx,
  ): Set[ValueSymbol] =
    def restOf(block: Block): Opt[Block] = block match
      case Define(_, rst) => S(rst)
      case Assign(_, _, rst) => S(rst)
      case AssignField(_, _, _, rst) => S(rst)
      case AssignDynField(_, _, _, _, rst) => S(rst)
      case Match(_, _, _, rst) => S(rst)
      case TryBlock(_, _, rst) => S(rst)
      case Label(_, _, _, rst) => S(rst)
      case _ => N

    def recur(block: Block): Set[ValueSymbol] = block match
      case Scoped(_, body) =>
        recur(body)
      case Begin(sub, rst) =>
        recur(sub) ++ recur(rst)
      case Define(defn: ValDefn, rst) if sessionExportCtx.shouldExport(defn.sym) =>
        recur(rst) + defn.sym
      case Define(_, rst) =>
        recur(rst)
      case Assign(sym: ValueSymbol, _, rst) if sessionExportCtx.shouldExport(sym) =>
        recur(rst) + sym
      case _: BlockTail =>
        Set.empty
      case block =>
        restOf(block).fold(Set.empty)(recur)

    recur(b)
  end collectSessionGlobalSymbols

  /** Declares a mutable exported global for a REPL-visible binding produced by the current block. */
  private def registerSessionGlobal(
      sym: ValueSymbol,
  )(using Ctx, Raise, SessionExportCtx): Unit =
    if ctx.containsGlobal(sym) then return
    val exportName = sym.nme
    val globalInfo = GlobalInfo(
      globalType = GlobalType(RefType.anyref, mutable = true),
      init = ref.`null`(HeapType.Any),
      exportName = S(exportName),
      sym,
    )
    ctx.addGlobal(globalInfo)
    summon[SessionExportCtx].emit(SessionGlobal(
      sym = sym,
      wrapId = globalInfo.wrapId,
      moduleName = SessionBinding.ReplModuleName,
      exportName = exportName,
      globalType = GlobalType(RefType.anyref, mutable = true),
    ))
  end registerSessionGlobal

  /** Registers imported REPL bindings into the current module before codegen starts. */
  private def registerSessionImports(
      sessionImports: Seq[SessionBinding],
  )(using Ctx, Raise): Unit =
    sessionImports.foreach:
      case cls: SessionClass =>
        ctx.addType(TypeInfo(
          sym = cls.sym,
          wrapId = cls.wrapId,
          compType = cls.compType,
          objectTag = cls.objectTag,
        ))
      case _ => ()

    sessionImports.foreach:
      case func: SessionFunc =>
        // If the function symbol comes from a class or module, generate a TempSymbol to avoid symbol collision with
        // the class/module itself
        val funcTySym = TempSymbol(N, func.sym.nme)
        val typeIdx =
          ctx.addType(TypeInfo(sym = funcTySym, wrapId = func.wrapId, compType = func.funcType, objectTag = N))
        ctx.addFunctionImport(WasmImport(
          func.moduleName,
          func.exportName,
          ExternType.Func(TypeUse(typeIdx), func.sym, wrapId = func.wrapId),
        ))
      case glob: SessionGlobal =>
        ctx.addGlobalImport(WasmImport(
          glob.moduleName,
          glob.exportName,
          ExternType.Global(glob.globalType, glob.sym, glob.wrapId),
        ))
      case singleton: SessionSingleton =>
        val globalExtern =
          ExternType.Global(
            GlobalType(singleton.globalTy, mutable = true),
            singleton.blockSym,
            singleton.wrapId,
          )
        ctx.addGlobalImport(WasmImport(
          singleton.moduleName,
          singleton.exportName,
          globalExtern,
        ))
        ctx.registerSingleton(
          singleton.blockSym,
          singleton.objectSym,
          SingletonInfo(globalExtern.id.id, singleton.globalTy),
        )
      case cls: SessionClass =>
        val typeInfoTypeIdx = ctx.addType(cls.rttiTypeInfo)
        typeInfoTypeIdxs(cls.sym) = typeInfoTypeIdx
        val globalExtern = ExternType.Global(
          GlobalType(RefType(typeInfoTypeIdx, nullable = false), mutable = false),
          TempSymbol(N, cls.sym.nme),
          wrapId = N -> S("typeinfo"),
        )
        val globalIdx = ctx.addGlobalImport(WasmImport(
          SessionBinding.ReplModuleName,
          cls.rttiGlobalExportName,
          globalExtern,
        ))
        typeInfoGlobals(cls.sym) = globalIdx
  end registerSessionImports

  /** Predeclares the per-class `typeinfo` struct type for one supported top-level class. */
  private def predeclareClassTypeInfoType(defn: ClsLikeDefn)(using Ctx, Raise): Unit =
    val parentTypeInfoIdx =
      if defn.parentPath.isEmpty then ctx.getType_!(typeInfoBaseSym)
      else typeInfoTypeIdxs(resolveParentSym(defn).get)

    val inheritedFields = ctx.getTypeInfo_!(parentTypeInfoIdx).compType match
      case struct: StructType => struct.fields
      case other =>
        lastWords(
          s"expected struct RTTI parent type for ${defn.sym}, found ${other.toWat.mkString()}",
        )

    val parentVirtualMethodCount = resolveParentSym(defn).flatMap(ctx.getVirtualTable)
      .fold(0)(_.virtualMethods.size)
    val currentVirtualMethods = ctx.getVirtualTable(defn.sym).fold(Nil)(_.virtualMethods)
    val newSlotFields = currentVirtualMethods.zipWithIndex.drop(parentVirtualMethodCount).map: (methodSym, slot) =>
      val methodDefn = defn.methods.find(_.sym == methodSym).get
      val arity = 1 + methodDefn.params.headOption.fold(0)(_.params.size)
      val fieldSym = TermSymbol(syntax.MutVal, owner = N, Ident(s"slot$slot"))
      fieldSym -> Field(
        RefType(virtualMethodFuncType(arity), nullable = true),
        mutable = true,
        id = s"slot$slot",
      )

    val typeInfoType = ctx.addType(TypeInfo(
      sym = TempSymbol(N, defn.sym.nme),
      compType = StructType(fields = inheritedFields ++ newSlotFields, parents = Seq(parentTypeInfoIdx)),
      objectTag = N,
      wrapId = N -> S("typeinfo"),
    ))
    typeInfoTypeIdxs(defn.sym) = typeInfoType
  end predeclareClassTypeInfoType

  /** Predeclares the shared runtime `typeinfo` global for one supported top-level class. */
  private def predeclareClassTypeInfoGlobal(defn: ClsLikeDefn)(using Ctx, Raise, SessionExportCtx): Unit =
    val typeInfoTypeIdx = typeInfoTypeIdxs(defn.sym)
    val tagValue = ctx.getTypeInfo_!(defn.sym).objectTag.get
    val parentTypeInfo =
      if defn.parentPath.isEmpty then ref.`null`(typeInfoBaseTypeIdx)
      else getClassTypeInfoGlobal(resolveParentSym(defn).get).get
    val virtualMethods = ctx.getVirtualTable(defn.sym).fold(Nil)(_.virtualMethods)
    val initFields = Seq[Expr](
      i32.const(tagValue),
      parentTypeInfo,
    ) ++ virtualMethods.map: methodSym =>
      ref.func(
        ctx.getFunc_!(methodSym),
        RefType(ctx.getFuncTypeUse_!(methodSym).typeIdx, nullable = false),
      )
    val globalInfo = GlobalInfo(
      globalType = GlobalType(RefType(typeInfoTypeIdx, nullable = false), mutable = false),
      init = struct.`new`(typeInfoTypeIdx, initFields),
      exportName =
        if summon[SessionExportCtx].shouldExport(defn.sym) || defn.sym == syntheticUnitDefn.sym
        then S(s"${defn.sym.nme}_typeinfo")
        else N,
      sym = defn.sym,
      wrapId = N -> S("typeinfo"),
    )
    val globalIdx = ctx.addGlobal(globalInfo)
    typeInfoGlobals(defn.sym) = globalIdx

  /** Declares one top-level class method. */
  private def predeclareMethod(methodDefn: FunDefn, ownerCls: ClsLikeDefn)(using Ctx, Raise): Unit =
    val methodParams = (ownerCls.isym -> SymIdx("this")) +:
      methodDefn.params.headOption.fold(Nil): ps =>
        ps.params.map: p =>
          p.sym -> SymIdx(p.sym.nme)
    ctx.getVirtualTable(ownerCls.sym).flatMap(_.virtualMethodSlots.get(methodDefn.sym)) match
      case S(_) =>
        predeclareClassFuncWithType(
          ownerCls,
          methodDefn.sym.nme,
          methodParams,
          methodDefn.sym,
          N,
          virtualMethodFuncType(methodParams.size),
        )
      case N =>
        predeclareClassFunc(ownerCls, methodDefn.sym.nme, methodParams, methodDefn.sym, N)

  /** Declares placeholders for all methods on one top-level class. */
  private def predeclareClassMethods(defn: ClsLikeDefn)(using Ctx, Raise): Unit =
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
  private def exnTagIdx(using Ctx, Raise): TagIdx =
    val sym = TempSymbol(N, "mlx_exn")
    ctx.getOrCreateWasmIntrinsicTag(
      "mlx_exn",
      ctx.addTag(TagInfo(
        typeUse = TypeUse(ctx.addType(TypeInfo(
          sym,
          FunctionType(params = Seq(WasmParam(SymIdx("ex"), RefType.anyref)), results = Seq.empty),
          objectTag = S(ctx.getFreshObjectTag()),
        ))),
        sym = sym,
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
  private def getOrLoadStrCtorFunction(using Ctx, Raise): FuncIdx =
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
      val importTySym = TempSymbol(N, ExternIntrinsics.StringFromUtf16ImportName)
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
  private def tupleArrayType(mut: Bool)(using Ctx, Raise): TypeIdx =
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
  private def mkTempLocal(base: Str)(using Ctx, FunctionCtx, Raise): LocalIdx =
    funcCtx.addLocal(TempSymbol(N, base))

  /** Binds constructor self (`thisSym`) to the Wasm local name `this` in the current function context.
    */
  private def bindCtorThis(thisSym: ValueSymbol)(using Ctx, FunctionCtx, Raise): LocalIdx =
    funcCtx.addLocal(thisSym, S("this"))

  /** Compiles a class init body under its own Wasm-local frame with explicit `this`. */
  private def setupInitLocals(
      clsLikeDefn: ClsLikeDefn,
  )(using Ctx, Raise, SessionExportCtx): (Expr, FunctionCtx) =
    genFuncBody(classCtorParamList(clsLikeDefn) :: Nil, thisSym = S(clsLikeDefn.isym)):
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
  )(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr =
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
      case Assign(lhs, Call(Value.SimpleRef(bs: BuiltinSymbol), argss), _: End)
        if (lhs is State.noSymbol) && (bs is State.superSymbol)
      =>
        S(End("") -> argss.flatten)
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
  )(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr =
    if expr.resultTypes.isEmpty && !isAbortive then
      blockInstr(
        label = N,
        children = Seq(expr, result(State.unitBlockMemberSymbol.asMemberRef(State.unitSymbol))),
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
  private def tupleArrayGet(tupleExpr: Expr, idxBuilder: Expr => Expr)(using Ctx, FunctionCtx, Raise): Expr =
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
  )(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr => Expr =
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

  def getVar(l: ValueSymbol, loc: Opt[Loc])(using Ctx, FunctionCtx, Raise): Expr = l match
    case ts: semantics.InnerSymbol =>
      lastWords(s"ValueSymbol `$ts` (${ts.getClass.getSimpleName}) cannot be resolved as a variable")
    case l =>
      funcCtx.lookupLocal(l) match
        case S(localIdx) => local.get(localIdx, RefType.anyref)
        case N if ctx.containsGlobal(l) =>
          global.get(ctx.getGlobal_!(l), ctx.getGlobalType_!(l).globalType.valType)
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

  def argument(a: Arg)(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr =
    if a.spread.nonEmpty then
      errExpr(
        Ls(msg"WatBackend::argument for spread expression not implemented yet" -> a.value.toLoc),
        extraInfo = S(a.showAsTree),
      )
    else result(a.value)

  def operand(a: Arg)(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr =
    if a.spread.nonEmpty then die else subexpression(a.value)

  def subexpression(r: codegen.Result)(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr = r match
    case r: Lambda =>
      errExpr(
        Ls(msg"WatBuilder::subexpression for Lambda not implemented yet" -> r.toLoc),
        extraInfo = S(r.showAsTree),
      )
    case r => result(r)

  /** Returns the owning class symbol for a resolved field/member symbol, when available. */
  private def fieldOwner(sym: MemberSymbol): Opt[BlockMemberSymbol] = sym match
    case ts: TermSymbol => ts.owner.flatMap(_.asBlkMember)
    case ms: MemberSymbol => ms.asTrm.flatMap(_.owner.flatMap(_.asBlkMember))

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

  /** Lowers a class method call, using virtual dispatch only when the selected owner class has a virtual slot. */
  private def lowerClassMethodCall(
      qual: Path,
      methodSym: BlockMemberSymbol,
      args: Seq[Arg],
  )(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr =
    val ownerCls = fieldOwner(methodSym).get
    ctx.getVirtualTable(ownerCls).flatMap(_.virtualMethodSlots.get(methodSym)) match
      case S(slot) =>
        val ownerTypeInfoIdx = typeInfoTypeIdxs(ownerCls)
        val receiverTmp = mkTempLocal("receiver")
        val receiverExpr = local.set(receiverTmp, result(qual))
        val receiverRef = local.get(receiverTmp, RefType.anyref)
        val ownerTypeInfoRef = ref.cast(
          readObjectTypeInfo(receiverRef),
          RefType(ownerTypeInfoIdx, nullable = false),
        )
        val virtualArity = 1 + args.size
        val virtualMethodTypeIdx = virtualMethodFuncType(virtualArity)
        val methodRef = struct.get(
          FieldIdx(SymIdx(s"slot$slot")),
          ownerTypeInfoRef,
          RefType(virtualMethodTypeIdx, nullable = true),
        )
        val virtualCall = call_ref(
          target = methodRef,
          operands = receiverRef +: args.map(argument),
          typeIdx = virtualMethodTypeIdx,
          funcType = virtualMethodSignature(virtualArity),
        )
        blockInstr(
          label = N,
          children = Seq(receiverExpr, virtualCall),
          resultTypes = Seq(Result(RefType.anyref)),
        )
      case N =>
        call(
          funcidx = ctx.getFunc_!(methodSym),
          operands = result(qual) +: args.map(argument),
          returnTypes = Seq(Result(RefType.anyref)),
        )

  def result(r: codegen.Result)(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr = r match
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
    case Value.SimpleRef(l) =>
      singletonInfoFor(l) match
        case S(info) => singletonGlobalGet(info)
        case N =>
          ctx.getFunc(l) match
            case S(funcIdx) => ref.func(funcIdx, RefType(ctx.getFuncTypeUse_!(l).typeIdx, nullable = false))
            case N => getVar(l, r.toLoc)
    case Value.MemberRef(bms, disamb) =>
      if (bms is State.unitSymbol) || (disamb is State.unitSymbol) then
        RegisterUnitSingleton()
      singletonInfoFor(bms) match
        case S(info) => singletonGlobalGet(info)
        case N =>
          if disamb.isInstanceOf[ClassSymbol] then
            errExpr:
              Ls(msg"Plain class references are not supported in Wasm; instantiate the class instead." -> r.toLoc)
          else
            ctx.getFunc(bms) match
              case S(funcIdx) => ref.func(funcIdx, RefType(ctx.getFuncTypeUse_!(bms).typeIdx, nullable = false))
              case N => getVar(bms, r.toLoc)
    case Value.This(sym) =>
      singletonInfoFor(sym) match
        case S(info) => singletonGlobalGet(info)
        case N =>
          // TODO(Derppening): Remove `ref.cast` once erased-typed IR is implemented
          ref.cast(
            local.get(funcCtx.lookupLocal_!(sym, sym.toLoc), RefType.anyref),
            RefType(
              sym.asBlkMember.fold(baseObjectTypeIdx)(ctx.getType_!(_)),
              nullable = false,
            ),
          )

    case Call(Value.SimpleRef(l: BuiltinSymbol), lhs :: rhs :: Nil) if !l.functionLike =>
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

    case Call(sel @ Select(qual, _), argss) if sel.symbol.flatMap(predeclaredClassMethodSym).nonEmpty =>
      if argss.length > 1 then
        return errExpr(
          Ls(msg"WatBuilder::result for Call(...) with multiple argument lists is not supported yet" -> r.toLoc),
          extraInfo = S(r.toString),
        )
      val args = argss.flatten
      val methodSym = sel.symbol.flatMap(predeclaredClassMethodSym).get
      lowerClassMethodCall(qual, methodSym, args)

    case c @ Call(fun, argss) =>
      if argss.length > 1 then
        return errExpr(
          Ls(msg"WatBuilder::result for Call(...) with multiple argument lists is not supported yet" -> c.toLoc),
          extraInfo = S(c.toString),
        )
      val args = argss.flatten
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
            case Value.SimpleRef(l) =>
              val base = fun match
                case Value.SimpleRef(l) => ctx.getFunc(l)
                case Value.MemberRef(l, _) => ctx.getFunc(l)
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
            case Value.MemberRef(l, _) =>
              val base = ctx.getFunc(l)
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
              lowerClassMethodCall(qual, methodSym, Nil)
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
            ref = castConserve(qualRes, RefType(ctx.getType_!(selCls), nullable = false)),
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
      val ctorClsSymOpt = cls match
        case ref: Value.MemberRef => S(ref.disamb)
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
    case Select(Value.SimpleRef(sym), ident) if (sym eq State.wasmSymbol) && wasmIntrinsicNameSet.contains(ident.name) =>
      S(ident.name)
    case _ => N

  /** Gets (or creates) the intrinsic function implementing the wasm operator `name`.
    */
  private def getIntrinsic(name: Str)(using Ctx, Raise): FuncIdx =
    ctx.getOrCreateWasmIntrinsic(name, importIntrinsic(name))

  private def importIntrinsic(name: Str)(using Ctx, Raise): FuncIdx =
    val typeIdx = declareIntrinsicType(name)
    ctx.addFunctionImport(WasmImport(
      ExternIntrinsics.SystemModule,
      name,
      ExternType.Func(TypeUse(typeIdx), TempSymbol(N, name), wrapId = N -> N),
    ))

  /** Creates the intrinsic definition for `name`.
    */
  private def createIntrinsic(name: Str, exportName: Opt[Str])(using Ctx, Raise): FuncIdx =
    if binaryOps.contains(name) then createBinaryInt31Func(name, binaryOps(name), exportName)
    else if unaryOps.contains(name) then createUnaryInt31Func(name, unaryOps(name), exportName)
    else lastWords(s"Unsupported wasm intrinsic '$name'")

  private def intrinsicParamSuffixes(name: Str): Seq[Str] =
    if binaryOps.contains(name) then Seq("lhs", "rhs") else Seq("arg")

  private def declareIntrinsicType(name: Str)(using Ctx, Raise): TypeIdx =
    ctx.addType(TypeInfo(
      sym = TempSymbol(N, name),
      compType = FunctionType(
        params = intrinsicParamSuffixes(name).map(nme => WasmParam(SymIdx(nme), RefType.anyref)),
        results = Seq(Result(RefType.anyref)),
      ),
      objectTag = N,
    ))

  /** Creates a binary Int31 intrinsic with two parameters and body built from `op`.
    */
  private def createBinaryInt31Func(
      name: Str,
      op: (Expr, Expr) => Expr,
      exportName: Opt[Str],
  )(using Ctx, Raise): FuncIdx =
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
  )(using Ctx, Raise): FuncIdx =
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
  )(using Ctx, Raise): FuncIdx =
    val funcTy = declareIntrinsicType(name)
    val funcInfo = FuncInfo(
      sym = TempSymbol(N, name),
      typeUse = TypeUse(funcTy),
      params = params,
      locals = Seq.empty,
      body = body,
      resultTypes = Seq(Result(RefType.anyref)),
      exportName = exportName,
    )
    ctx.addFunc(funcInfo)

  def intrinsicSupportModule()(using Raise): Document =
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
  )(using Ctx): Expr =
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
  private def unaryInt31Body(paramIdx: LocalIdx, op: Expr => Expr)(using Ctx): Expr =
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

  def returningTerm(t: Block)(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr =
    t match
      case Assign(l: NoSymbol, r, rst) =>
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

      case Assign(l: ValueSymbol, r, rst) =>
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
                val objRef = castConserve(lhsExpr, RefType(ctx.getType_!(selCls), nullable = false))
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
        def mkThis(sym: InnerSymbol): Expr = result(sym.asThis)
        defn match
          case ValDefn(tsym, sym, p) =>
            // * Currently we allow `val` outside of object/module scopes,
            // * in which case it has no owner and is just a glorified local variable rather than a field
            tsym.owner match
              case N =>
                val localStorageSym = defn.sym
                val symExpr = getVar(localStorageSym, localStorageSym.toLoc)
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
            val res = boundary:
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
                      Return(Lambda(ps, block)(Nil))
                  val (bodyWat, fnCtx) = setupFunction(N, ps, result)
                  if sym.nameIsMeaningful then
                    val funcTy = ctx.addType(
                      TypeInfo(
                        sym = TempSymbol(N, sym.nme),
                        compType = FunctionType(
                          params = fnCtx.params.map(p => WasmParam(p._2, RefType.anyref)),
                          results = Seq.fill(bodyWat.resultTypes.length)(Result(RefType.anyref)),
                        ),
                        objectTag = N,
                      ),
                    )

                    val funcInfo = FuncInfo(
                      sym,
                      typeUse = TypeUse(funcTy),
                      params = ps.params.zip(fnCtx.params.map(_._2)).map((p, idx) => p.sym -> idx),
                      resultTypes = Seq.fill(bodyWat.resultTypes.length)(Result(RefType.anyref)),
                      locals = fnCtx.locals,
                      body = bodyWat,
                      exportName = sym.optionIf(_.nameIsMeaningful).map(_.nme),
                    )
                    ctx.addFunc(funcInfo)
                    if summon[SessionExportCtx].shouldExport(defn.sym) then
                      summon[SessionExportCtx].emit(SessionFunc(
                        sym = defn.sym,
                        wrapId = funcInfo.wrapId,
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
                      msg"WatBuilder::returningTerm for ClsLikeDefn(...) where `$cond` not implemented yet" ->
                        clsLikeDefn.sym.toLoc,
                    ),
                    extraInfo = S(defn.showAsTree),
                  ))
                  val isSingletonObj = clsLikeDefn.k is syntax.Obj
                  if clsLikeDefn.owner.nonEmpty then
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
                  val typeref = ctx.getType_!(clsLikeDefn.sym)
                  val typeinfo = ctx.getTypeInfo_!(typeref)

                  val (initWat, initFnCtx) = setupInitLocals(clsLikeDefn)

                  val tagValue = typeinfo.objectTag getOrElse:
                    lastWords(s"Expected class ${clsLikeDefn.sym} to have an object tag")
                  val instanceFields = typeinfo.compType match
                    case struct: StructType =>
                      struct.fields match
                        case (_, typeInfoField) +: rest =>
                          getClassTypeInfoGlobal(clsLikeDefn.sym).get +: rest.map((_, field) =>
                            defaultStructFieldValue(field),
                          )
                        case Nil =>
                          lastWords(s"Expected instance struct for ${clsLikeDefn.sym} to include $$typeinfo header")
                    case other =>
                      lastWords(s"Expected struct type for ${clsLikeDefn.sym}, found ${other.toWat.mkString()}")

                  val initFuncRef = initFuncSym(clsLikeDefn.sym)
                  val (ctorCode, ctorFnCtx) = genFuncBody(ctorParamList :: Nil, thisSym = N):
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
                        local.set(thisVar, struct.`new`(typeref, instanceFields)),
                        drop(initCall),
                        `return`(S(local.get(thisVar, RefType(typeref, nullable = false)))),
                      ),
                      resultTypes = Seq(Result(RefType.anyref)),
                    )

                  val predeclaredInit = ctx.getFuncInfo_!(initFuncRef)
                  ctx.addFunc(FuncInfo(
                    sym = initFuncRef,
                    wrapId = S(clsLikeDefn.sym.nme) -> N,
                    typeUse = predeclaredInit.typeUse,
                    params = initFnCtx.params,
                    resultTypes = initWat.resultTypes.map(ty => Result(ty.asValType_!)),
                    locals = initFnCtx.locals,
                    body = initWat,
                    exportName = predeclaredInit.exportName,
                  ))

                  val predeclaredCtor = ctx.getFuncInfo_!(clsLikeDefn.sym)
                  val ctorFuncInfo = FuncInfo(
                    sym = clsLikeDefn.sym,
                    wrapId = S(clsLikeDefn.sym.nme) -> N,
                    typeUse = predeclaredCtor.typeUse,
                    params = ctorFnCtx.params,
                    resultTypes = ctorCode.resultTypes.map(ty => Result(ty.asValType_!)),
                    locals = ctorFnCtx.locals,
                    body = ctorCode,
                    exportName = predeclaredCtor.exportName,
                  )
                  ctx.addFunc(ctorFuncInfo)

                  def overwriteMethod(
                      sym: BlockMemberSymbol,
                      ps: ParamList,
                      bod: Block,
                  ): Unit =
                    val (bodyWat, fnCtx) = setupFunction(S(clsLikeDefn.isym), ps, bod)
                    val predeclaredMethod = ctx.getFuncInfo_!(sym)
                    ctx.addFunc(FuncInfo(
                      sym,
                      wrapId = S(clsLikeDefn.sym.nme) -> N,
                      typeUse = predeclaredMethod.typeUse,
                      params = fnCtx.params,
                      resultTypes = Seq.fill(bodyWat.resultTypes.length)(Result(RefType.anyref)),
                      locals = fnCtx.locals,
                      body = bodyWat,
                      exportName = predeclaredMethod.exportName,
                    ))

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
                    val rttiTypeInfo = ctx.getTypeInfo_!(typeInfoTypeIdxs(clsLikeDefn.sym))
                    val rttiGlobalInfo = ctx.getGlobalInfo_!(typeInfoGlobals(clsLikeDefn.sym))
                    summon[SessionExportCtx].emit(SessionClass(
                      sym = clsLikeDefn.sym,
                      wrapId = typeinfo.wrapId,
                      compType = typeinfo.compType,
                      objectTag = typeinfo.objectTag,
                      rttiTypeInfo = rttiTypeInfo,
                      rttiGlobalExportName = rttiGlobalInfo.exportName.get,
                      aliasSyms = clsLikeDefn.isym match
                        case mos: ModuleOrObjectSymbol => mos :: Nil
                        case _ => Nil,
                    ))
                    if !isSingletonObj && clsLikeDefn.sym.nameIsMeaningful then
                      summon[SessionExportCtx].emit(SessionFunc(
                        sym = clsLikeDefn.sym,
                        wrapId = ctorFuncInfo.wrapId,
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
                          wrapId = typeinfo.wrapId,
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

      case Return(res) =>
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
        val scrutLocalResult = scrut match
          case _: (Value.RefLike | Value.Lit) => N
          case _ => S(mkTempLocal("scrut"))

        val scrutInitExpr = scrutLocalResult.map: scrutLocal =>
          local.set(scrutLocal, result(scrut))

        def getScrutExpr: Expr =
          scrutLocalResult.fold(result(scrut))(getLocalAnyref)

        def assignTailResult(target: LocalIdx, expr: Expr): Expr =
          if expr.isControlTransfer then expr
          else
            expr.resultType match
              case S(_) => local.set(target, expr)
              case N => blockInstr(
                  label = N,
                  children = Seq(
                    expr,
                    local.set(target, result(State.unitBlockMemberSymbol.asMemberRef(State.unitSymbol))),
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
                    val isStructCompatible = ref.test(getScrutExpr, baseObjectRefType(nullable = false))
                    val scrutRtti = readObjectTypeInfo(getScrutExpr)
                    val targetRtti = getClassTypeInfoGlobal(clsBlkMemberSym).get
                    val classMatchExpr = isSubtypeByTypeInfo(scrutRtti, targetRtti)

                    val bodyExpr = returningTerm(body)
                    val armBodyExpr = lowerMatchBody(bodyExpr)

                    funcCtx.withLabel(LabelSymbol(N, "arm"), hasContinueLabel = false):
                      case LabelTarget(armLabel, _) =>
                        S(`if`(
                          condition = isStructCompatible,
                          ifTrue = `if`(
                            condition = classMatchExpr,
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
                children = scrutInitExpr.toSeq ++ matchResInitExpr.toSeq ++ armExprs :+ defaultExpr,
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
      preservedSessionSymbols: Set[BoundSymbol],
  )(using Raise): CompiledWasmModule =
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

    // Create the two Wasm intrinsic struct types shared across class lowering:
    // the base RTTI layout (`TypeInfoBase`) and the base object layout (`Object`).
    ctx.addType(TypeInfo(
      sym = typeInfoBaseSym,
      compType = StructType(Seq(
        tagFieldSym -> Field(I32Type, mutable = false, id = "$tag"),
        parentFieldSym -> Field(
          RefType(TypeIdx(SymIdx("TypeInfoBase")), nullable = true),
          mutable = false,
          id = "$parent",
        ),
      )),
      objectTag = N,
    ))

    ctx.addType(TypeInfo(
      sym = baseObjectSym,
      compType = StructType(Seq(
        typeInfoFieldSym -> Field(RefType(typeInfoBaseTypeIdx, nullable = false), mutable = true, id = "$typeinfo"),
      )),
      objectTag = S(ctx.getFreshObjectTag() ensuring (_ == 0)),
    ))

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
        ordered.foreach(predeclareClass)

      // Compile the entry function under a dedicated local scope so that any temp locals introduced
      // during codegen (e.g., via `local.tee`) are declared in the entry function.
      val (entryFnExpr, entryFnCtx) = genFuncBody(Nil, thisSym = N):
        val rawEntryFnExpr = block(p.main)
        normalizeEntryExpr(rawEntryFnExpr, p.main.isAbortive)

      val entrySym = BlockMemberSymbol("entry", Nil)

      val entryFnTy = ctx.addType(TypeInfo(
        sym = TempSymbol(N, entrySym.nme),
        FunctionType(params = Seq.empty, results = Seq(Result(RefType.anyref))),
        objectTag = N,
      ))
      val entryFnInfo = FuncInfo(
        sym = entrySym,
        typeUse = TypeUse(entryFnTy),
        params = Seq.empty,
        resultTypes = Seq(Result(RefType.anyref)),
        locals = entryFnCtx.locals,
        body = entryFnExpr,
        exportName = S(entrySym.nme),
      )

      if stringLits.nonEmpty then
        stringLits.foreach: (s, lit) =>
          if lit.byteLen > 0 then
            ctx.addDataSegment(DataSegment.Active(
              offset = i32.const(lit.offset),
              bytes = Seq(lit.watBytes),
              memuse = N,
              sym = TempSymbol(N, s.take(WatBuilder.StringConstantIdentMaxLength)),
            ))

      val initActions = ctx.getSingletonInitActions
      if initActions.nonEmpty then
        val initTy = ctx.addType(TypeInfo(
          sym = TempSymbol(N, "start"),
          compType = FunctionType(params = Seq.empty, results = Seq.empty),
          objectTag = N,
        ))
        val initBody = blockInstr(
          label = N,
          children = initActions,
          resultTypes = Seq.empty,
        )
        val initFn = ctx.addFunc(FuncInfo(
          sym = TempSymbol(N, "start"),
          typeUse = TypeUse(initTy),
          params = Seq.empty,
          resultTypes = Seq.empty,
          locals = Seq.empty,
          body = initBody,
          exportName = N,
        ))
        ctx.setStartFunc(initFn)
      end if

      ctx.addFunc(entryFnInfo)

      compiledModule(entrySym.nme)
  end program

  def blockPreamble(ss: Iterable[ValueSymbol])(using Ctx, FunctionCtx, Raise): Unit =
    ss.toArray.sortBy(_.uid).toSeq.filter: sym =>
      !ctx.containsGlobal(sym) && ctx.getFunc(sym).isEmpty
    .foreach: sym =>
      funcCtx.addLocal(sym)

  def nonNestedScoped(
      blk: Block,
  )(k: Block => Expr)(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr = blk match
    case Scoped(syms, body) =>
      blockPreamble(syms.view.filter(body.freeVars))
      k(body)
    case _ => k(blk)

  def block(t: Block)(using Ctx, FunctionCtx, Raise, SessionExportCtx): Expr =
    nonNestedScoped(t)(returningTerm)

  def setupFunction(
      thisParam: Opt[InnerSymbol],
      params: ParamList,
      body: Block,
  )(using Ctx, Raise, SessionExportCtx): (Expr, FunctionCtx) =
    genFuncBody(params :: Nil, thisSym = thisParam):
      block(body)

end WatBuilder
