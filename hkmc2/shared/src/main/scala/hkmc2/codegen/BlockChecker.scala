package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import sourcecode.Line

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.Message.MessageContext

import semantics.*
import semantics.Elaborator.{Ctx, State}
import syntax.Tree


/** An invariant of the IR is that each symbol should be bound at most once
  * (this simplifies various analyses and transformations).
  * Erased representations must also agree at the boundaries that move values into
  * slots. An absent value or slot type denotes Unknown, which requires a cast when
  * narrowed to a more specific reference type and cannot hold an unboxed primitive.
  */
class BlockChecker()(using DebugPrinter, State, Ctx, Raise) extends BlockTraverser:
  
  val definedSyms = MutSet.empty[ScopedSymbol]
  // N here means no enclosing return contract, unlike an unannotated storage slot.
  private var resultType: Opt[ErasedValueType] = N
  
  override def applyProgram(prog: Program): Unit =
    // Result.erasedType assumes initialized symbol metadata and memoizes its answer.
    // Report missing metadata before attempting those queries, so an invalid copied
    // field produces a diagnostic instead of aborting validation with an assertion.
    val uninitialized = MutSet.empty[Symbol]
    new BlockTraverser:
      override def applySymbol(sym: Symbol): Unit =
        val initialized = sym match
          case sym: TermSymbol => sym.isErased
          case sym: HasDelayedErasedType[?] => sym.isErased
          case _ => true
        if !initialized && uninitialized.add(sym) then
          raise:
            InternalError(
              msg"Invalid IR: missing type information for '${sym.nme}'" -> sym.toLoc :: Nil,
              extraInfo = S(sym),
            )
      this.applyProgram(prog)
    if uninitialized.isEmpty then super.applyProgram(prog)

  private def checkSymbol(sym: ScopedSymbol, info: => Any): Unit =
    if !definedSyms.add(sym) then
      raise:
        InternalError(
          msg"Invalid IR: binding '${sym.nme}' is introduced more than once" -> sym.toLoc
            :: Nil,
          extraInfo = S(info)
        )
  
  // Undefined does not constrain a slot's representation, including an unboxed one.
  // Follow casts too: their target cannot change this property of the literal.
  private def isUndefined(value: Result): Bool = value match
    case Value.Lit(Tree.UnitLit(false)) => true
    case Cast(inner, _, _) => isUndefined(inner)
    case _ => false

  private def checkTypes(actual: ErasedValueType, expected: ErasedValueType,
      boundary: Message, loc: Opt[Loc], allowNarrowing: Bool): Unit =
    val from = actual.canonicalize
    val to = expected.canonicalize
    val compatible = ErasedType.needsCast(from, to)
    if compatible.isEmpty || (compatible.contains(true) && !allowNarrowing) then
      val problem = if compatible.isEmpty then msg"incompatible representations" else msg"a missing cast"
      // An incomplete parent chain also requires a conservative cast, just as in
      // Result.coerceTo. It does not prove that the two types are unrelated.
      val explanation = (from, to) match
        case (ErasedType.AnyRef(_, a), ErasedType.AnyRef(_, b)) if (a isnt b) && a.nme == b.nme =>
          msg"The value and its destination refer to different copies of type '${a.nme}'"
        case _ => msg"The value has type '${from.describe}', but its destination requires '${to.describe}'"
      raise:
        InternalError(
          (msg"Invalid IR: $problem at $boundary" -> loc) ::
            (explanation -> loc) :: Nil,
          extraInfo = S((from, to)),
        )

  private def checkValue(value: Result, expected: Opt[ErasedValueType], boundary: Message, loc: Opt[Loc]): Unit =
    if !isUndefined(value) then
      // Erasure initializes unannotated slots to N; dynamic reads also yield N.
      // Both denote Unknown, so neither may bypass the same cast rules as coerceTo.
      checkTypes(value.erasedType_!, expected.getOrElse(ErasedType.Unknown), boundary, loc, allowNarrowing = false)

  private def withResultType(tpe: Opt[ErasedValueType])(body: => Unit): Unit =
    val saved = resultType
    resultType = tpe
    try body finally resultType = saved

  override def applyBlock(b: Block): Unit =
    b match
    case Scoped(syms, body) =>
      syms.foreach(checkSymbol(_, b))
    case Assign(sym: LocalVarSymbol, value, _) =>
      checkValue(value, sym.erasedType, msg"assignment to '${sym.nme}'", sym.toLoc)
    case Return(value) => resultType.foreach: expected =>
      checkValue(value, S(expected), msg"a function return", value.toLoc)
    case assign: AssignField => assign.symbol.foreach:
      case sym: TermSymbol => checkValue(assign.rhs, sym.erasedType, msg"assignment to '${sym.nme}'", sym.toLoc)
      case _ => ()
    case AssignDynField(_, _, DynSelectKind.Member(sym), value, _) =>
      checkValue(value, sym.erasedType, msg"assignment to '${sym.nme}'", sym.toLoc)
    case _ => ()
    super.applyBlock(b)
  
  override def applyValDefn(defn: ValDefn): Unit =
    checkValue(defn.rhs, defn.tsym.erasedType, msg"initialization of '${defn.sym.nme}'", defn.tsym.toLoc)
    super.applyValDefn(defn)

  private def fixedParamTypes(fun: FunDefn): Ls[Ls[Opt[ErasedValueType]]] =
    fun.params.map(_.params.map(_.sym.erasedType))

  override def applyFunDefn(fun: FunDefn): Unit =
    val signatureParams = fun.dSym.erasure.collect:
      case sig: ErasedFuncSignature => sig.paramLists
      case _: ErasedGetterSignature => Nil
    signatureParams.foreach: expectedParams =>
      val actual = fixedParamTypes(fun)
      if actual.map(_.length) != expectedParams.map(_.length) then
        raise:
          InternalError(
            msg"Invalid IR: parameter lists of '${fun.sym.nme}' disagree with its erased signature" -> fun.dSym.toLoc :: Nil,
            extraInfo = S(fun),
          )
      else
        actual.zip(expectedParams).zipWithIndex.foreach: (lists, listIdx) =>
          lists._1.zip(lists._2).zipWithIndex.foreach: (types, paramIdx) =>
            for actual <- types._1; expected <- types._2 do
              val boundary = msg"parameter ${paramIdx + 1} in list ${listIdx + 1} of '${fun.sym.nme}'"
              checkTypes(actual, expected, boundary, fun.dSym.toLoc, allowNarrowing = false)
              checkTypes(expected, actual, boundary, fun.dSym.toLoc, allowNarrowing = false)
    // A generator body returns its payload, while its caller receives an Iterator.
    // Lowered async helpers and forwarding wrappers each carry their own descriptor,
    // so the current definition's body type is the return contract in every case.
    withResultType(fun.dSym.erasedResult.bodyType):
      super.applyFunDefn(fun)

  override def applyLam(lam: Lambda): Unit = withResultType(N)(super.applyLam(lam))
  override def applyClsLikeDefn(cls: ClsLikeDefn): Unit = withResultType(N)(super.applyClsLikeDefn(cls))
  override def applyCompanionModule(body: ClsLikeBody): Unit = withResultType(N)(super.applyCompanionModule(body))
  override def applyHandler(handler: Handler): Unit = withResultType(N)(super.applyHandler(handler))

  private def checkCall(call: Call): Unit =
    val paramTypes = call.fun match
      case Value.SimpleRef(sym: BuiltinSymbol) => sym.erasedSignature.map(_.paramLists)
      case _ => call.fun.targetSymbol.flatMap:
        case sym: TermSymbol => sym.irDefn.collect:
          case fun: FunDefn => fixedParamTypes(fun)
        case _ => N
    // A source signature alone does not identify physical slots: lowering may move
    // optional and trailing parameters into a rest tuple. Only the current MIR
    // definition (or a builtin's fixed signature) establishes a positional prefix.
    paramTypes.foreach: lists =>
      call.argss.zip(lists).foreach: (args, params) =>
        // A spread makes subsequent positional indices unknown; the preceding
        // fixed arguments still have a well-defined destination.
        args.takeWhile(_.spread.isEmpty).zip(params).foreach: (arg, expected) =>
          checkValue(arg.value, expected, msg"a call argument", arg.value.toLoc)

  private def checkCast(cast: Cast): Unit =
    if !isUndefined(cast.value) then
      checkTypes(cast.value.erasedType_!, cast.target, msg"a cast", cast.toLoc, allowNarrowing = true)

  override def applyResult(result: Result): Unit =
    result match
      case call: Call => checkCall(call)
      case cast: Cast => checkCast(cast)
      case _ => ()
    super.applyResult(result)

  override def applyPath(path: Path): Unit =
    path match
      case cast: Cast => checkCast(cast)
      case _ => ()
    super.applyPath(path)

  override def applyParamList(pl: LoweredParamList): Unit =
    pl.paramSyms.foreach(checkSymbol(_, pl))
    super.applyParamList(pl)
  
end BlockChecker

