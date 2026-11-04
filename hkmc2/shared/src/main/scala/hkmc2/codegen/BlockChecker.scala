package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import sourcecode.Line

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.Message.MessageContext

import semantics.*
import semantics.Elaborator.{Ctx, State}


/** An invariant of the IR is that each symbol should be bound at most once
  * (this simplifies various analyses and transformations).
  * This class checks this invariant, which does not depend on erased type metadata. */
class BindingChecker()(using DebugPrinter, State, Raise) extends BlockTraverser:
  
  val definedSyms = MutSet.empty[ScopedSymbol]
  
  private def checkSymbol(sym: ScopedSymbol, info: => Any): Unit =
    if !definedSyms.add(sym) then
      raise:
        InternalError(
          msg"Invalid IR: binding '${sym.nme}' is introduced more than once" -> sym.toLoc
            :: Nil,
          extraInfo = S(info)
        )
  
  override def applyBlock(b: Block): Unit =
    b match
    case Scoped(syms, body) =>
      syms.foreach(checkSymbol(_, b))
    case _ => ()
    super.applyBlock(b)
  
  override def applyParamList(pl: LoweredParamList): Unit =
    pl.paramSyms.foreach(checkSymbol(_, pl))
    super.applyParamList(pl)
  
end BindingChecker


/** Checks the binding invariant of [[BindingChecker]], and that erased representations agree
  * at the boundaries that move values into slots. An absent value or slot type denotes Unknown,
  * which requires a cast when narrowed to a more specific reference type and cannot hold an
  * unboxed primitive.
  */
class BlockChecker()(using DebugPrinter, State, Ctx, Raise) extends BindingChecker:
  
  // N here means no enclosing return contract, unlike an unannotated storage slot.
  private var resultType: Opt[ErasedValueType] = N
  
  override def applyProgram(prog: Program): Unit =
    // Result.erasedType assumes initialized symbol metadata and memoizes its answer.
    // Report missing metadata before attempting those queries, so an invalid copied
    // field produces a diagnostic instead of aborting validation with an assertion.
    // This pre-pass must reach every symbol whose metadata the checks below read.
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
      // The traversal does not visit a value definition's TermSymbol, whose type
      // applyValDefn reads as the declared type of the initialized slot.
      override def applyValDefn(defn: ValDefn): Unit =
        applySymbol(defn.tsym)
        super.applyValDefn(defn)
      this.applyProgram(prog)
    if uninitialized.isEmpty then super.applyProgram(prog)
    // The representation checks would query the missing metadata, but binding
    // uniqueness does not depend on it, so that invariant is still checked.
    else BindingChecker().applyProgram(prog)
  
  /** Distinct type symbols with the same name typically come from a copied class
    * whose references were not all renamed, which printing the two types would hide. */
  private def explainMismatch(from: CanonicalErasedValueType, to: CanonicalErasedValueType,
      source: Str, target: Str): Message = (from, to) match
    case (ErasedType.AnyRef(_, a), ErasedType.AnyRef(_, b)) if (a isnt b) && a.nme == b.nme =>
      msg"The $source and $target refer to different copies of type '${a.nme}'"
    case _ => msg"The $source has type '${from.describe}', but $target requires '${to.describe}'"
  
  private def checkTypes(from: CanonicalErasedValueType, to: CanonicalErasedValueType,
      boundary: Message, loc: Opt[Loc], allowNarrowing: Bool): Unit =
    val compatible = ErasedType.needsCast(from, to)
    if compatible.isEmpty || (compatible.contains(true) && !allowNarrowing) then
      // An incomplete parent chain also requires a conservative cast, just as in
      // Result.coerceTo. It does not prove that the two types are unrelated.
      val problem = if compatible.isEmpty then msg"incompatible representations" else msg"a missing cast"
      raise:
        InternalError(
          (msg"Invalid IR: $problem at $boundary" -> loc) ::
            (explainMismatch(from, to, "value", "its destination") -> loc) :: Nil,
          extraInfo = S((from, to)),
        )
  
  private def checkValue(value: Result, expected: Opt[ErasedValueType], boundary: Message, loc: Opt[Loc]): Unit =
    // Erasure initializes unannotated slots to N; dynamic reads also yield N.
    // Both denote Unknown, so neither may bypass the same cast rules as coerceTo.
    // An undefined value has type Nothing, which fits every representable slot.
    checkTypes(value.erasedType_!.canonicalize, expected.getOrElse(ErasedType.Unknown).canonicalize,
      boundary, loc, allowNarrowing = false)
  
  private def withResultType(tpe: Opt[ErasedValueType])(body: => Unit): Unit =
    val saved = resultType
    resultType = tpe
    try body finally resultType = saved
  
  override def applyBlock(b: Block): Unit =
    b match
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
    val expectedParams = fun.signature.erasure match
      case sig: ErasedFuncSignature => sig.paramLists
      case _: ErasedGetterSignature => Nil
    val actualParams = fixedParamTypes(fun)
    if actualParams.map(_.length) != expectedParams.map(_.length) then
      raise:
        InternalError(
          msg"Invalid IR: parameter lists of '${fun.sym.nme}' disagree with its erased signature" -> fun.dSym.toLoc :: Nil,
          extraInfo = S(fun),
        )
    else
      // A binding and its signature entry describe the same slot, as established by
      // FunDefn.Signature.fromLowering, so their canonical types must be equal. needsCast
      // would also reject equal types with no representation, such as `Int32 | Str`:
      // declaring such a parameter is legal, and only moving a value into it is an error.
      // The lengths of both lists of lists are equal here, so zipping drops nothing.
      for
        ((actualList, expectedList), listIdx) <- actualParams.iterator.zip(expectedParams).zipWithIndex
        ((actual, expected), paramIdx) <- actualList.iterator.zip(expectedList).zipWithIndex
        binding = actual.getOrElse(ErasedType.Unknown).canonicalize
        declared = expected.getOrElse(ErasedType.Unknown).canonicalize
        if binding != declared
      do
        raise:
          InternalError(
            (msg"Invalid IR: parameter ${paramIdx + 1} in list ${listIdx + 1} of '${fun.sym.nme}' disagrees with its erased signature" -> fun.dSym.toLoc) ::
              (explainMismatch(binding, declared, "binding", "its signature") -> fun.dSym.toLoc) :: Nil,
            extraInfo = S((binding, declared)),
          )
    // A generator body returns its payload, while its caller receives an Iterator.
    // Lowered async helpers and forwarding wrappers each carry their own descriptor,
    // so the current definition's body type is the return contract in every case.
    withResultType(fun.signature.result.bodyType):
      super.applyFunDefn(fun)
  
  override def applyLam(lam: Lambda): Unit = withResultType(N)(super.applyLam(lam))
  override def applyClsLikeDefn(cls: ClsLikeDefn): Unit = withResultType(N)(super.applyClsLikeDefn(cls))
  override def applyCompanionModule(body: ClsLikeBody): Unit = withResultType(N)(super.applyCompanionModule(body))
  
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
      // Argument lists beyond the definition's apply to its result, and missing ones
      // leave a closure, so only the parameter lists present on both sides are checked.
      call.argss.lazyZip(lists).foreach: (args, params) =>
        // A spread makes subsequent positional indices unknown; the preceding fixed
        // arguments still have a well-defined destination. Additional arguments fill a
        // rest parameter and omitted ones leave optional parameters unset, so only the
        // common prefix of arguments and fixed parameters is checked.
        args.iterator.takeWhile(_.spread.isEmpty).zip(params).foreach: (arg, expected) =>
          checkValue(arg.value, expected, msg"a call argument", arg.value.toLoc)
  
  private def checkCast(cast: Cast): Unit =
    (cast.value.erasedType_!.canonicalize, cast.target.canonicalize) match
      // Substitution can move a value of a more precise type into an existing cast:
      // inlining `asWrapper(fortyTwo)` yields `42 as! Wrapper`. A cast between unrelated
      // reference types fails at run time, but backends can still emit it. Only a type
      // without a representation shared with the operand makes a cast invalid.
      case (_: ErasedType.AnyRef, _: ErasedType.AnyRef) => ()
      case (from, to) => checkTypes(from, to, msg"a cast", cast.toLoc, allowNarrowing = true)
  
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
  
end BlockChecker

