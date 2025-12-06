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
import syntax.Tree.{BoolLit, IntLit, Ident}
import text.Param as WasmParam
import Message.MessageContext
import Scope.scope

import scala.collection.mutable.{ArrayBuffer as ArrayBuf}
import scala.util.boundary, boundary.break
import sourcecode.Line

extension (instr: FoldedInstr)
  /**
   * Returns the mneomic prefix of this instruction.
   *
   * For example, for `local.get` it returns `Some("local")`, and for `nop` it returns `None`.
   */
  private def mnemonicPrefix: Opt[Str] =
    instr.mnemonic.split('.').optionUnless(_.size == 1).map(_.head)

class WatBuilder(using TraceLogger, State) extends CodeBuilder:
  import Ctx.ctx
  import Ctx.{binaryOps, unaryOps, wasmIntrinsicArities, wasmIntrinsicNameSet}
  import Instructions.*

  type Context = Ctx

  private val baseObjectSym: BlockMemberSymbol = BlockMemberSymbol("Object", Nil)
  private val tagFieldSym: TermSymbol = TermSymbol(syntax.MutVal, owner = N, Ident("$tag"))

  private def baseObjectTypeIdx(using Ctx): TypeIdx =
    ctx.getType_!(baseObjectSym)

  private def baseObjectStruct(using Ctx): StructType =
    ctx.getTypeInfo_!(baseObjectSym).compType match
      case struct: StructType => struct
      case other => lastWords(s"Base Object type must be a struct, found ${other.toWat.mkString()}")

  private def baseObjectRefType(nullable: Bool)(using Ctx): RefType =
    RefType(baseObjectTypeIdx, nullable = nullable)

  /**
   * Raises a [[WarningReport]] with the given `warnMsgs` and `extraInfo`, and emits an
   * `unreachable` instruction.
   */
  def warnExpr(warnMsgs: Ls[Message -> Opt[Loc]], extraInfo: Opt[Any] = N)(using
      Ctx,
      Raise
  )(using Line): Expr =
    raise(WarningReport(warnMsgs, source = Diagnostic.Source.Compilation, extraInfo = extraInfo))
    unreachable

  /**
   * Raises an [[ErrorReport]] with the given `warnMsgs` and `extraInfo`, and emits an `unreachable`
   * instruction.
   */
  def errExpr(errMsgs: Ls[Message -> Opt[Loc]], extraInfo: => Opt[Any] = N)(using
      Ctx,
      Raise
  )(using Line): Expr =
    raise(ErrorReport(errMsgs, source = Diagnostic.Source.Compilation, extraInfo = extraInfo))
    unreachable

  def getVar(l: Local, loc: Opt[Loc])(using Ctx, Raise, Scope): Expr = l match
    case ts: semantics.TermSymbol =>
      errExpr(
        Ls(msg"WatBuilder::getVar for TermSymbol not implemented yet" -> l.toLoc),
        extraInfo = S(ts.toString)
      )
    case ts: semantics.ModuleOrObjectSymbol if ts.asMod.isDefined =>
      errExpr(
        Ls(
          msg"WatBuilder::getVar for ModuleOrObjectSymbol (`ts.asMod.isDefined`) not implemented yet" -> l.toLoc
        ),
        extraInfo = S(ts.toString)
      )
    case ts: semantics.InnerSymbol =>
      if !ctx.containsLocal(l) then
        return errExpr(
          Ls(
            msg"WatBuilder::getVar for InnerSymbol (symbol not in top-level scope) not implemented yet" -> ts.toLoc
          ),
          extraInfo = S(
            s"Block IR: `${ts.toString}`\nScope: ${scope.toString}\nWasm Locals: ${ctx.getAllWasmLocals.toString}"
          )
        )
      local.get(LocalIdx(SymIdx(scope.findThis_!(ts))), RefType.anyref)
    case l =>
      if ctx.containsLocal(l) then
        local.get(LocalIdx(SymIdx(scope.lookup_!(l, l.toLoc))), RefType.anyref)
      else if ctx.containsGlobal(l) then
        global.get(GlobalIdx(SymIdx(scope.lookup_!(l, l.toLoc))), RefType.anyref)
      else
        errExpr(
          Ls(
            msg"WatBuilder::getVar for ${l.getClass.getSimpleName} (symbol not in top-level scope) not implemented yet" -> l.toLoc
          ),
          extraInfo = S(
            s"Block IR: `${l.toString}`\nScope: ${scope.toString}\nWasm Locals: ${ctx.getAllWasmLocals.toString}"
          )
        )
  end getVar

  def argument(a: Arg)(using Ctx, Raise, Scope): Expr =
    if a.spread.nonEmpty then
      errExpr(
        Ls(msg"WatBackend::argument for spread expression not implemented yet" -> a.value.toLoc),
        extraInfo = S(a.showAsTree)
      )
    else result(a.value)

  def operand(a: Arg)(using Ctx, Raise, Scope): Expr =
    if a.spread.nonEmpty then die else subexpression(a.value)

  def subexpression(r: codegen.Result)(using Ctx, Raise, Scope): Expr = r match
    case r: Lambda =>
      errExpr(
        Ls(msg"WatBuilder::subexpression for Lambda not implemented yet" -> r.toLoc),
        extraInfo = S(r.showAsTree)
      )
    case r => result(r)

  def fieldSelect(thisSym: BlockMemberSymbol, sym: DefinitionSymbol[?])(using Ctx, Raise): FieldIdx =
    val structInfo = ctx.getTypeInfo_!(thisSym)
    val symToField = structInfo.compType match
      case ty: StructType => ty.fields
      case _ => lastWords(s"Cannot select field from non-struct type: ${structInfo.compType.toWat}")
    val fieldIdx = symToField.get(sym)
      .orElse:
        // Workaround: TermSymbols are not correctly resolved, so match the fields by name instead
        sym match
          case trmSym: TermSymbol if trmSym.owner.flatMap(_.asBlkMember).exists(_ == thisSym) =>
            symToField.find((fieldSym, _) => fieldSym.nme == sym.nme).map((_, v) => v)
          case _ => N
      .map((fieldidx, _) => fieldidx)
    FieldIdx(
      fieldIdx getOrElse:
        lastWords(
          s"Missing field `${sym.toString}` in struct `${thisSym.toString}` with type `${structInfo.toWat.mkString()}`"
        )
    )
  end fieldSelect

  def result(r: codegen.Result)(using Ctx, Raise, Scope): Expr = r match
    case Value.This(sym) =>
      // TODO(Derppening): Add type tracking and refinement for locals, remove the `ref.cast`
      ref.cast(
        local.get(LocalIdx(SymIdx(scope.findThis_!(sym))), RefType.anyref),
        RefType(
          ctx.getType_!(sym.asBlkMember.get),
          nullable = false
        )
      )
    case Value.Lit(BoolLit(value)) =>
      ref.i31(i32.const(if value then 1 else 0))
    case Value.Lit(IntLit(value)) =>
      ref.i31(i32.const(value.toInt))
    case Value.Ref(l, _) =>
      ctx.getFunc(l) match
        case S(funcIdx) =>
          ref.func(funcIdx, RefType(ctx.getFuncInfo_!(l).typeIdx, nullable = false))
        case N => getVar(l, r.toLoc)

    case Call(Value.Ref(l: BuiltinSymbol, _), lhs :: rhs :: Nil) if !l.functionLike =>
      if l.binary then
        l.nme match
          case "+" =>
            errExpr(
              Ls(
                msg"WatBuilder::result encountered builtin '+' which should be lowered to wasm.plus_impl" -> r.toLoc
              ),
              extraInfo = S(r.toString)
            )
          case lNme =>
            errExpr(
              Ls(
                msg"WatBuilder::result for binary builtin symbol '${lNme.toString}' not implemented yet" -> r.toLoc
              ),
              extraInfo = S(r.toString)
            )
      else
        errExpr(Ls(
          msg"Cannot call non-binary builtin symbol '${l.nme}'" -> r.toLoc
        ))

    case c @ Call(fun, args) =>
      wasmIntrinsicName(fun) match
        case S(intrName) =>
          val expectedArity = wasmIntrinsicArities(intrName)
          if expectedArity =/= args.length then
            return errExpr(
              Ls(
                msg"Wasm intrinsic '$intrName' called with incorrect arity (${args.length})" -> c.toLoc
              ),
              extraInfo = S(c.toString)
            )
          val funcIdx = getIntrinsic(intrName)
          call(
            funcidx = funcIdx,
            operands = args.map(argument),
            returnTypes = Seq(Result(RefType.anyref))
          )
        case N =>
          val base = subexpression(fun)
          if base.resultTypes.exists(_ is UnreachableType) then return base
          val wasmArgs = args.map(argument)

          val baseTypeIdx = base.resultType match
            case S(RefType(idx: TypeIdx, _)) => idx
            case ty =>
              return errExpr(
                Ls(
                  msg"Expected WAT of `fun` expression in Call(...) to have a `(ref <typeidx>)` type" -> r.toLoc
                ),
                extraInfo = S(
                  s"Block IR: `${fun.toString}`\nCompiled WAT: `${base.toWat.toString}`\n... which has type `${ty.fold("(none)")(_.toWat.toString)}`"
                )
              )
          val baseTypeInfo = ctx.getTypeInfo_!(baseTypeIdx)

          call_ref(
            target = base,
            operands = wasmArgs.toSeq,
            typeIdx = baseTypeIdx,
            funcType = baseTypeInfo.compType.asInstanceOf[FunctionType]
          )

    case sel @ Select(qual, id) =>
      val qualRes = result(qual)
      val selSym = sel.symbol getOrElse:
        lastWords(s"Symbol for Select(...) expression must be resolved")
      val selTrmSym = selSym match
        case termSym: TermSymbol => termSym
        case sym => lastWords(
            s"Expected resolved Select(...) expression to be a TermSymbol, but got $sym (${sym.getClass.getName})"
          )
      val selOwner = selTrmSym.owner getOrElse:
        lastWords(s"Expected resolved Select(...) expression `$selTrmSym` to have an owner")
      val selCls = selOwner.asBlkMember getOrElse:
        lastWords(
          s"Expected resolved class for Select(...) expression to be a BlockMemberSymbol, but got $selOwner (${selOwner.getClass.getName})"
        )
      val fieldidx = fieldSelect(selCls, selSym)
      struct.get(
        fieldidx,
        ref = ref.cast(qualRes, RefType(ctx.getType_!(selCls), nullable = false)),
        ty = RefType.anyref
      )

    case Instantiate(_, cls, as) =>
      val ctorClsSymOpt = cls match
        case ref: Value.Ref => ref.disamb
        case sel: Select => sel.symbol
        case cls => return errExpr(
            Ls(
              msg"WatBuilder::result for Instantiate(...) where `cls` is not a Ref(...) or Select(...) path not implemented yet " -> cls.toLoc
            ),
            extraInfo = S(s"Block IR of `cls` expression: ${cls.toString}")
          )
      val ctorClsSym = ctorClsSymOpt match
        case S(sym) => sym
        case N => return errExpr(
            Ls(
              msg"Class path for an Instantiate(...) expression must be resolved" -> cls.toLoc
            ),
            extraInfo = S(s"Block IR of `cls` expression: ${cls.toString}")
          )
      val ctorClsBlkSym = ctorClsSym.asBlkMember match
        case S(sym) => sym
        case N => lastWords(
            s"Expected resolved class for an Instantiate(...) expression to be a BlockMemberSymbol, but got ${ctorClsSym.getClass.getName}"
          )
      val ctorFuncIdx = ctx.getFunc(ctorClsBlkSym) match
        case S(idx) => idx
        case N => lastWords(s"Missing constructor definition for class ${ctorClsBlkSym.toString}")

      val objType = ctx.getFuncInfo_!(ctorFuncIdx).body.resultType_!
      call(funcidx = ctorFuncIdx, as.map(argument), Seq(Result(objType.asValType_!)))

    case r =>
      errExpr(
        Ls(msg"WatBackend::result for expression not implemented yet" -> r.toLoc),
        extraInfo = S(s"Block IR: `${r.toString}`")
      )
  end result

  /**
   * Returns the intrinsic name if `path` refers to a builtin under `wasm`, or `N` otherwise.
   */
  private def wasmIntrinsicName(path: Path): Opt[Str] = path match
    case Select(Value.Ref(sym, _), ident) if (sym eq State.wasmSymbol) && wasmIntrinsicNameSet.contains(ident.name) =>
      S(ident.name)
    case _ => N

  /**
   * Gets (or creates) the intrinsic function implementing the wasm operator `name`.
   */
  private def getIntrinsic(name: Str)(using Ctx, Scope): FuncIdx =
    ctx.getOrCreateWasmIntrinsic(name, createIntrinsic(name))

  /**
   * Creates the intrinsic definition for `name`.
   */
  private def createIntrinsic(name: Str)(using Ctx, Scope): FuncIdx =
    if binaryOps.contains(name) then createBinaryInt31Func(name, binaryOps(name))
    else if unaryOps.contains(name) then createUnaryInt31Func(name, unaryOps(name))
    else lastWords(s"Unsupported wasm intrinsic '$name'")

  /**
   * Creates a binary Int31 intrinsic with two parameters and body built from `op`.
   */
  private def createBinaryInt31Func(name: Str, op: (Expr, Expr) => Expr)(using Ctx, Scope): FuncIdx =
    val params = mkIntrinsicParams(name, Seq("lhs", "rhs"))
    val lhsName = params.head._2
    val rhsName = params(1)._2
    val body = binaryInt31Body(lhsName, rhsName, op)
    createIntrinsicFunc(name, params, body)

  /**
   * Creates a unary Int31 intrinsic with a single parameter and body built from `op`.
   */
  private def createUnaryInt31Func(name: Str, op: Expr => Expr)(using Ctx, Scope): FuncIdx =
    val params = mkIntrinsicParams(name, Seq("arg"))
    val argName = params.head._2
    val body = unaryInt31Body(argName, op)
    createIntrinsicFunc(name, params, body)

  /**
   * Allocates the Wasm type and function definition for an intrinsic with the given signature.
   */
  private def createIntrinsicFunc(name: Str, params: Seq[(TempSymbol, Str)], body: Expr)(using Ctx): FuncIdx =
    val funcTy = ctx.addType(
      sym = N,
      TypeInfo(
        id = N,
        FunctionType(
          params = params.map((_, nme) => WasmParam(S(nme), RefType.anyref)),
          results = Seq(Result(RefType.anyref))
        )
      )
    )
    val funcInfo = FuncInfo(
      id = N,
      typeIdx = funcTy,
      params = params,
      nResults = 1,
      locals = Seq.empty,
      body = body
    )
    ctx.addFunc(N, funcInfo)

  /**
   * Builds the body for an Int31 binary operator.
   */
  private def binaryInt31Body(lhsName: Str, rhsName: Str, op: (Expr, Expr) => Expr)(using Ctx, Scope): Expr =
    val cond = i32.and(
      ref.test(getLocalAnyref(lhsName), RefType.i31ref),
      ref.test(getLocalAnyref(rhsName), RefType.i31ref)
    )
    val i31Op = ref.i31(op(getI32FromAnyref(lhsName), getI32FromAnyref(rhsName)))
    `if`(
      condition = cond,
      ifTrue = i31Op,
      ifFalse = S(unreachable),
      resultTypes = Seq(Result(RefType.anyref))
    )

  /**
   * Builds the body for an Int31 unary operator.
   */
  private def unaryInt31Body(paramName: Str, op: Expr => Expr)(using Ctx, Scope): Expr =
    val cond = ref.test(getLocalAnyref(paramName), RefType.i31ref)
    val i31Op = ref.i31(op(getI32FromAnyref(paramName)))
    `if`(
      condition = cond,
      ifTrue = i31Op,
      ifFalse = S(unreachable),
      resultTypes = Seq(Result(RefType.anyref))
    )

  /**
   * Creates parameters for an intrinsic.
   */
  private def mkIntrinsicParams(name: Str, suffixes: Seq[Str]): Seq[(TempSymbol, Str)] =
    suffixes.map: suffix =>
      val sym = TempSymbol(N, suffix)
      sym -> suffix

  /**
   * Loads the local `name` as an `anyref`.
   */
  private def getLocalAnyref(name: Str): Expr =
    local.get(LocalIdx(SymIdx(name)), RefType.anyref)

  /**
   * Extracts the signed i32 value from the Int31 stored in the local `name`.
   */
  private def getI32FromAnyref(name: Str): Expr =
    i31.get(ref.cast(getLocalAnyref(name), RefType.i31ref), true)

  def returningTerm(t: Block)(using Ctx, Raise, Scope): Expr = t match
    case _: HandleBlock =>
      errExpr(
        Ls(msg"This code requires effect handler instrumentation but was compiled without it." -> N)
      )
    case Assign(l, r, rst) =>
      val lExpr = getVar(l, l.toLoc)
      val rExpr = result(r)
      val idx = lExpr.instrargs(0).asInstanceOf[LocalIdx]
      val assignExpr = lExpr.mnemonicPrefix match
        case S("global") =>
          errExpr(
            Ls(
              msg"WatBuilder::returningTerm for Assign(...) to global variable not implemented yet" -> l.toLoc
            ),
            extraInfo = S(s"Block IR: ${t.showAsTree}")
          )
        case S("local") => local.set(idx, rExpr)
        case _ =>
          lastWords(
            s"Expected `global.*` or `local.*` when compiling instruction for `$l`, but got ${lExpr.mnemonic}"
          )
      val rstBlk = returningTerm(rst)

      Instructions.block(
        label = N,
        children = Seq(assignExpr, rstBlk),
        resultTypes = rstBlk.resultTypes.map: ty =>
          Result(if ty is UnreachableType then RefType.anyref else ty.asValType_!)
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
                  msg"WatBuilder::returningTerm for ValDefn(...) where `tsym.owner.isEmpty` not implemented yet" -> sym.toLoc
                ),
                extraInfo = S(
                  s"Block IR of `defn`: ${defn.toString}\nBlock IR of `defn.tsym`: ${tsym.toString}"
                )
              )
            case S(owner) =>
              val ownerBlkMem = owner.asBlkMember.get
              val rstWat = returningTerm(rst)
              Instructions.block(
                label = N,
                children = Seq(
                  struct.set(
                    index = fieldSelect(ownerBlkMem, tsym),
                    ref = mkThis(owner),
                    value = result(p)
                  ),
                  rstWat
                ),
                resultTypes = rstWat.resultTypes.map(r => Result(r.asValType_!))
              )

        case defn: (FunDefn | ClsLikeDefn) =>
          val outerScope = scope
          val (thisProxy, res) = scope.nestRebindThis(
            // * Either this is an InnerSymbol or this is a Fun,
            // * and we need to rebind `this` to None to shadow it.
            defn.innerSym.collectFirst:
              case s: InnerSymbol => s
          ):
            boundary:
              defn match
                case FunDefn(params = Nil) =>
                  lastWords("cannot generate function with no parameter list")
                case FunDefn(own, sym, dSym, ps :: pss, bod) =>
                  if own.nonEmpty then
                    break(errExpr(
                      Ls(
                        msg"WatBuilder::returningTerm for Define(...) with `owner.nonEmpty` not implemented yet" -> defn.sym.toLoc
                      ),
                      extraInfo = S(defn.showAsTree)
                    ))

                  val result = pss.foldRight(bod):
                    case (ps, block) =>
                      Return(Lambda(ps, block), false)
                  val name = if sym.nameIsMeaningful then S(sym.nme) else N
                  val (params, bodyWat, locals) = setupFunction(name, ps, result)
                  if sym.nameIsMeaningful then
                    val funcTy = ctx.addType(
                      sym = N,
                      TypeInfo(
                        id = N,
                        FunctionType(
                          params = params.map(_._1),
                          results = Seq.fill(bodyWat.resultTypes.length)(Result(RefType.anyref))
                        )
                      )
                    )

                    val funcInfo =
                      FuncInfo(
                        sym,
                        typeIdx = funcTy,
                        params = ps.params.zip(params.map(_._2)).map((p, nme) => p.sym -> nme),
                        nResults = bodyWat.resultTypes.length,
                        locals = locals,
                        body = bodyWat
                      )
                    val func = ctx.addFunc(S(defn.sym), funcInfo)

                    nop
                  else
                    errExpr(
                      Ls(
                        msg"WatBuilder::returningTerm for FunDefn(...) where `!sym.nameIsMeaningful` not implemented yet" -> defn.sym.toLoc
                      ),
                      extraInfo = S(defn.showAsTree)
                    )
                case clsLikeDefn: ClsLikeDefn =>
                  // Guard against unsupported features
                  def errUnimplExpr(cond: Str): Nothing = break(errExpr(
                    Ls(
                      msg"WatBackend::returningTerm for ClsLikeDefn(...) where `$cond` not implemented yet" -> clsLikeDefn.sym.toLoc
                    ),
                    extraInfo = S(defn.showAsTree)
                  ))
                  if clsLikeDefn.owner.nonEmpty then
                    break(errUnimplExpr("owner.nonEmpty"))
                  if !(clsLikeDefn.k is syntax.Cls) then
                    break(errUnimplExpr("!(k is Cls)"))
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

                  val clsParams = clsLikeDefn.paramsOpt.fold(Nil)(_.paramSyms)
                  val ctorParams = clsParams.map: p =>
                    ctx.addLocal(p)
                    p -> scope.allocateName(p)
                  val ctorAuxParams = clsLikeDefn.auxParams.map: ps =>
                    ps.params.map: p =>
                      ctx.addLocal(p.sym)
                      p -> scope.allocateName(p.sym)

                  val inheritedFields = baseObjectStruct.fields.toMap
                  val inheritedSize = inheritedFields.size

                  val classFields: Map[DefinitionSymbol[?], NumIdx -> Field] = (clsLikeDefn.publicFields.map(
                    _._2
                  ) ++ clsLikeDefn.privateFields).zipWithIndex.map: (f, index) =>
                    f -> (NumIdx(index + inheritedSize) -> Field(
                      RefType.anyref,
                      mutable = true,
                      id = S(f.nme)
                    ))
                  .toMap

                  val allFields: Map[DefinitionSymbol[?], NumIdx -> Field] = inheritedFields ++ classFields

                  // Only parent is base Object for now. For general inheritance add other parents.
                  val typeref = ctx.addType(
                    sym = S(clsLikeDefn.sym),
                    typeInfo =
                      TypeInfo(
                        sym = clsLikeDefn.sym,
                        compType = StructType(
                          fields = allFields,
                          parents = Seq(baseObjectTypeIdx),
                          isSubtype = true
                        )
                      )
                  )

                  // * If there are no ctor params, pop one param list off the aux params
                  val (newCtorAuxParams, initialCtorParams) = clsLikeDefn.paramsOpt match
                    case None => ctorAuxParams match
                        case head :: next => (next, head)
                        case Nil => (ctorAuxParams, Nil)
                    case Some(_) => (ctorAuxParams, ctorParams)

                  ctx.addLocal(clsLikeDefn.isym)
                  val thisVar = getVar(clsLikeDefn.isym, N).instrargs(0).asInstanceOf[LocalIdx]
                  val (ctorWat, ctorLocals) = block(clsLikeDefn.ctor)
                  
                  val classTypeIdx = ctx.getType_!(clsLikeDefn.sym, resolveSymIdx = true)
                  val tagValue = classTypeIdx match
                    case TypeIdx(NumIdx(idx)) => idx
                    case _ => lastWords(s"Expected numeric type index for class ${clsLikeDefn.sym}")
                  
                  val ctorCode = Instructions.block(
                    label = N,
                    Seq(
                      local.set(thisVar, struct.new_default(typeref)),
                      struct.set(
                        FieldIdx(NumIdx(0)),
                        ref.cast(local.get(thisVar, RefType.anyref), RefType(typeref, nullable = false)),
                        i32.const(tagValue)
                      ),
                      ctorWat,
                      `return`(S(local.get(thisVar, RefType(typeref, nullable = false))))
                    ),
                    resultTypes = Seq(Result(RefType.anyref))
                  )

                  val ctorAux = if newCtorAuxParams.isEmpty then
                    ctorCode
                  else
                    break(errUnimplExpr("newCtorAuxParams.nonEmpty"))

                  val funcTy = ctx.addType(
                    sym = N,
                    TypeInfo(
                      id = N,
                      FunctionType(
                        params = ctorParams.map(p => WasmParam(S(p._2), RefType.anyref)),
                        results = Seq(Result(RefType.anyref))
                      )
                    )
                  )

                  ctx.addFunc(
                    S(clsLikeDefn.sym),
                    FuncInfo(
                      sym = clsLikeDefn.sym,
                      typeIdx = funcTy,
                      params = ctorParams,
                      nResults = ctorCode.resultTypes.length,
                      locals =
                        (clsLikeDefn.isym -> scope.findThis_!(clsLikeDefn.isym)) +: ctorLocals.map:
                          l =>
                            l -> scope.lookup_!(l, l.toLoc)
                      ,
                      body = ctorAux
                    )
                  )

                  nop

                case defn =>
                  errExpr(
                    Ls(
                      msg"WatBuilder::returningTerm for Define(...) not implemented yet" -> defn.sym.toLoc
                    ),
                    extraInfo = S(defn.showAsTree)
                  )
          end val

          val rstBlk = returningTerm(rst)
          thisProxy match
            case S(proxy) if !scope.thisProxyDefined =>
              scope.thisProxyDefined = true
              errExpr(
                Ls(
                  msg"WatBuilder::returningTerm for Define(...) where `!scope.thisProxyDefined` not implemented yet" -> defn.sym.toLoc
                ),
                extraInfo = S(defn.showAsTree)
              )
            case _ => Instructions.block(
                label = N,
                children = Seq(res, rstBlk),
                resultTypes = rstBlk.resultTypes.map(ty => Result(ty.asValType_!))
              )

    case Return(res, true) =>
      val resWat = result(res)
      resWat.resultType match
        case S(RefType(heapType, _)) => heapType match
            case HeapType.Func =>
              errExpr(Ls(msg"Returning function instances is not supported" -> res.toLoc))
            case typeidx: TypeIdx
                if ctx.getTypeInfo_!(typeidx).compType.isInstanceOf[FunctionType] =>
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
            case typeidx: TypeIdx
                if ctx.getTypeInfo_!(typeidx).compType.isInstanceOf[FunctionType] =>
              errExpr(Ls(msg"Returning function instances is not supported" -> res.toLoc))
            case _ => ()
        case _ => ()

      `return`(S(resWat))

    case Match(scrut, arms, dflt, rst) =>
      val matchLabelSym = TempSymbol(N, "match")
      val matchLabel = scope.allocateName(matchLabelSym)
      
      def getScrutExpr: Expr = result(scrut)
      
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
                  i32.eq(scrutValue, i32.const(value.toInt))
                case _ =>
                  break(errExpr(Ls(msg"Pattern matching for unit literals not implemented yet" -> lit.toLoc)))

              val bodyExpr = returningTerm(body)
              val armLabelSym = TempSymbol(N, "arm")
              val armLabel = scope.allocateName(armLabelSym)
              S(Instructions.`if`(
                condition = testExpr,
                ifTrue = Instructions.block(
                  label = S(armLabel),
                  children = Seq(bodyExpr, br(matchLabel)),
                  resultTypes = Seq.empty
                ),
                ifFalse = N,
                resultTypes = Seq.empty
              ))

            case Case.Cls(cls, _) =>
              val clsBlkMemberSym = cls.asBlkMember.getOrElse:
                break(errExpr(
                  Ls(msg"Could not resolve BlockMemberSymbol for class pattern" -> cls.toLoc),
                  extraInfo = S(s"ClassLikeSymbol: ${cls.toString}")
                ))
              val clsTypeIdx = ctx.getType_!(clsBlkMemberSym, resolveSymIdx = true)
              
              val expectedTag = clsTypeIdx match
                case TypeIdx(NumIdx(idx)) => idx
                case _ => break(errExpr(
                  Ls(msg"Expected numeric type index for class pattern" -> cls.toLoc),
                  extraInfo = S(s"TypeIdx: ${clsTypeIdx}")
                ))

              val scrutExpr = getScrutExpr
              val isStructCompatible = ref.test(scrutExpr, baseObjectRefType(nullable = true))
              
              val bodyExpr = returningTerm(body)
              val armLabelSym = TempSymbol(N, "arm")
              val armLabel = scope.allocateName(armLabelSym)
              
              // Safe to cast and extract tag since ref.test passed
              val scrutAsObject = ref.cast(getScrutExpr, baseObjectRefType(nullable = false))
              val scrutTag = struct.get(FieldIdx(NumIdx(0)), scrutAsObject, I32Type)
              val tagMatches = i32.eq(scrutTag, i32.const(expectedTag))
              
              S(Instructions.`if`(
                condition = isStructCompatible,
                ifTrue = Instructions.`if`(
                  condition = tagMatches,
                  ifTrue = Instructions.block(
                    label = S(armLabel),
                    children = Seq(bodyExpr, br(matchLabel)),
                    resultTypes = Seq.empty
                  ),
                  ifFalse = N,
                  resultTypes = Seq.empty
                ),
                ifFalse = N,
                resultTypes = Seq.empty
              ))
            case _ =>
              break(errExpr(
                Ls(
                  msg"WatBuilder::returningTerm for Match(...) with case `${cse.toString}` not implemented yet" -> N
                ),
                extraInfo = S(cse.toString)
              ))
        

        val defaultExpr = dflt match
          case S(defaultBody) => returningTerm(defaultBody)
          case N => unreachable
        
        val rstExpr = returningTerm(rst)
        val matchResultTypes = Seq(Result(RefType.anyref))
        
        // Generate the match block
        val matchBlock = Instructions.block(
          label = S(matchLabel),
          children = armExprs :+ defaultExpr,
          resultTypes = matchResultTypes
        )
        
        // If rst is End (produces no value), the match block is the final result
        rst match
          case End(_) =>
            matchBlock
          case _ =>
            Instructions.block(
              label = N,
              children = Seq(matchBlock, rstExpr),
              resultTypes = rstExpr.resultTypes.map(ty => Result(ty.asValType_!))
            )

    // TODO: Implement proper WASM exception throwing
    case Throw(res) => unreachable

    case End(_) => nop

    case t =>
      errExpr(
        Ls(msg"WatBuilder::returningTerm for expression not implemented yet" -> N),
        extraInfo = S(t.showAsTree)
      )
  end returningTerm

  def program(p: Program, exprt: Opt[BlockMemberSymbol], wd: os.Path)(using
      Raise,
      Scope
  ): (Document, Str) =
    for imprt <- p.imports do
      raise(
        ErrorReport(
          msg"Import of symbol `${imprt._2}` not implemented yet" -> imprt._1.toLoc :: Nil,
          extraInfo = S(imprt),
          source = Diagnostic.Source.Compilation
        )
      )
    exprt.foreach: exprt =>
      raise(
        ErrorReport(
          msg"Export of symbol `${exprt.nme}` not implemented yet" -> exprt.toLoc :: Nil,
          extraInfo = S(exprt),
          source = Diagnostic.Source.Compilation
        )
      )

    val ctx = Ctx.empty
    
    // Create base Object struct with tag field that all other structs will inherit
    ctx.addType(
      sym = S(baseObjectSym),
      TypeInfo(
        id = S(SymIdx("Object")),
        StructType(
          Map(
            tagFieldSym -> (NumIdx(0) -> Field(I32Type, mutable = true, id = S("$tag")))
          ),
          isSubtype = true
        )
      )
    )
    
    val (entryFnExpr, entryFnLocals) =
      block(p.main)(using ctx, summon[Raise], summon[Scope])

    val entrySym = BlockMemberSymbol("entry", Nil)
    val entryNme = scope.allocateName(entrySym)

    val entryFnTy = ctx.addType(
      sym = N,
      TypeInfo(id = N, FunctionType(params = Seq.empty, results = Seq(Result(RefType.anyref))))
    )
    val entryFnInfo = FuncInfo(
      id = S(SymIdx(entryNme)),
      typeIdx = entryFnTy,
      params = Seq.empty,
      nResults = 1,
      // TODO(Derppening): Should we place top-level scope variables in the global section?
      locals = entryFnLocals.map(l => l -> scope.lookup_!(l, l.toLoc)),
      body = entryFnExpr
    )
    ctx.addFunc(S(entrySym), entryFnInfo)

    (ctx.toWat, entryNme)
  end program

  def blockPreamble(ss: Iterable[Symbol])(using Ctx, Raise, Scope): Seq[Local] =
    val vars = ss.filter(
      scope.lookup(_).toSeq.isEmpty
    ).toSeq.toArray.sortBy(_.uid).iterator.map: l =>
      scope.allocateName(l)
      l
    .toSeq
    ctx.addLocals(vars)
    vars

  def block(t: Block)(using Ctx, Raise, Scope): (Expr, Seq[Local]) =
    val locals = blockPreamble(t.definedVars)
    (returningTerm(t), locals)

  def body(t: Block)(using Ctx, Raise, Scope): (Expr, Seq[Local]) =
    scope.nest givenIn:
      block(t)

  def setupFunction(name: Option[Str], params: ParamList, body: Block)(using
      Ctx,
      Raise,
      Scope
  ): (Seq[WasmParam -> Str], Expr, Seq[(Local, Str)]) =
    // Add a frame for `ctx.locals`
    ctx.pushLocal()

    val result = scope.nest givenIn:
      val wasmParams = params.params.map: p =>
        val paramNme = scope.allocateName(p.sym)
        val param = WasmParam(S(paramNme), RefType.anyref)
        ctx.addLocal(p.sym)
        param -> paramNme
      val (wasmBody, locals) = block(body)
      val localsWithNames = locals.map(l => l -> scope.lookup_!(l, l.toLoc))
      (wasmParams.toSeq, wasmBody, localsWithNames)

    // Restore `ctx.locals`
    ctx.popLocal()

    result
  end setupFunction

end WatBuilder
