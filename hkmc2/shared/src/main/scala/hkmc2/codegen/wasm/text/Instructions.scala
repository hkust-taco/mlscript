package hkmc2
package codegen.wasm.text

import hkmc2.utils.*, shorthands.*

import document.*

object Instructions:
  /** Creates a `block` instruction. */
  def block(
      label: Opt[Str],
      children: Seq[Expr],
      resultTypes: Seq[Result],
  ): FoldedInstr =
    val labelWat = label.map(lbl => doc"$$$lbl")

    FoldedInstr(
      mnemonic = "block",
      instrargs = labelWat.toSeq ++ resultTypes,
      stackargs = children,
      resultTypes = resultTypes.map(_.valtype),
    )

  /** Creates a `loop` instruction. */
  def loop(
      label: Opt[Str],
      children: Seq[Expr],
      resultTypes: Seq[Result],
  ): FoldedInstr =
    val labelWat = label.map(lbl => doc"$$$lbl")

    FoldedInstr(
      mnemonic = "loop",
      instrargs = labelWat.toSeq ++ resultTypes,
      stackargs = children,
      resultTypes = resultTypes.map(_.valtype),
    )

  /** Creates an `if` instruction. */
  def `if`(
      condition: Expr,
      ifTrue: Expr,
      ifFalse: Opt[Expr],
      resultTypes: Seq[Result],
  ): FoldedInstr =
    val thenInstr = FoldedInstr(
      mnemonic = "then",
      instrargs = Seq.empty,
      stackargs = Seq(ifTrue),
      resultTypes = ifTrue.resultTypes,
    )
    val elseInstr = ifFalse.map: elseExpr =>
      FoldedInstr(
        mnemonic = "else",
        instrargs = Seq.empty,
        stackargs = Seq(elseExpr),
        resultTypes = elseExpr.resultTypes,
      )

    FoldedInstr(
      mnemonic = "if",
      instrargs = resultTypes,
      stackargs = Seq(condition, thenInstr) ++ elseInstr.toSeq,
      resultTypes = resultTypes.map(_.valtype),
    )
  end `if`

  /** Creates a `call` instruction. */
  def call(
      funcidx: FuncIdx,
      operands: Seq[Expr],
      returnTypes: Seq[Result],
  ): FoldedInstr = FoldedInstr(
    mnemonic = "call",
    instrargs = Seq(funcidx.toWat),
    stackargs = operands,
    resultTypes = returnTypes.map(_.valtype),
  )

  /** Creates a `call_ref` instruction. */
  def call_ref(
      target: Expr,
      operands: Seq[Expr],
      typeIdx: TypeIdx,
      funcType: FunctionType,
  ): FoldedInstr = FoldedInstr(
    mnemonic = "call_ref",
    instrargs = Seq(typeIdx.toWat),
    stackargs = operands :+ target,
    resultTypes = funcType.sigType.results.map(_.valtype),
  )

  /** Creates a `nop` instruction. */
  def nop: FoldedInstr = FoldedInstr(
    mnemonic = "nop",
    instrargs = Seq.empty,
    stackargs = Seq.empty,
    resultType = N,
  )

  /** Creates a `drop` instruction. */
  def drop(value: Expr): FoldedInstr = FoldedInstr(
    mnemonic = "drop",
    instrargs = Seq.empty,
    stackargs = Seq(value),
    resultTypes = value.resultTypes.init,
  )

  /** Creates a `return` instruction with an optional return value. */
  def `return`(value: Opt[Expr]): FoldedInstr = FoldedInstr(
    mnemonic = "return",
    instrargs = Seq.empty,
    stackargs = value.toSeq,
    resultTypes = value.fold(Seq.empty)(_.resultTypes),
  )

  /** Creates a `throw` instruction. */
  def `throw`(tag: TagIdx, operands: Seq[Expr]): FoldedInstr = FoldedInstr(
    mnemonic = "throw",
    instrargs = Seq(tag.toWat),
    stackargs = operands,
    resultType = S(UnreachableType),
  )

  /** Creates an `unreachable` instruction. */
  def unreachable: FoldedInstr = FoldedInstr(
    mnemonic = "unreachable",
    instrargs = Seq.empty,
    stackargs = Seq.empty,
    resultType = S(UnreachableType),
  )

  /** Creates a `br` (branch) instruction. */
  def br(label: Str): FoldedInstr = FoldedInstr(
    mnemonic = "br",
    instrargs = Seq(doc"$$$label"),
    stackargs = Seq.empty,
    resultType = S(UnreachableType),
  )

  /** The instructions shared by every Wasm numeric type family (`i32`, `i64`, `f32` and `f64`).
    *
    * All four families have the same instruction shape: the mnemonic is the type's own prefix followed by the
    * operation name, the operands are the stack arguments, and the result is a value of either the family's own type
    * (arithmetic) or `i32` (comparisons and tests). Deriving the families from a common base keeps them from drifting
    * apart as instructions are added, and leaves only the genuinely per-family parts spelled out: the `const`
    * immediate, and the operations one of the integer and floating-point types has and the other does not.
    *
    * Each instruction below is created by the method of the same name, on the object of the family it belongs to:
    * `i32.add(l, r)` creates an `i32.add`, `f64.add(l, r)` an `f64.add`, and so on.
    */
  sealed abstract class NumInstrs(valType: NumType):

    /** The mnemonic prefix shared by this family's instructions, e.g. `i32`. */
    private val prefix: Str = valType.toWat.mkString()

    /** The result type of an instruction that nominally yields a `nominal`-typed value from `operands`.
      *
      * An operand that never yields a value makes the whole instruction unreachable, so `nominal` would misdescribe
      * what this instruction leaves on the stack.
      */
    private def resultTypeOf(nominal: ValType, operands: Seq[Expr]): Type =
      if operands.exists(_.resultTypes.exists(_ is UnreachableType)) then UnreachableType else nominal

    /** Creates a unary instruction of this family nominally yielding a `nominal`-typed value. */
    private def unary(op: Str, nominal: ValType)(value: Expr): FoldedInstr = FoldedInstr(
      mnemonic = s"$prefix.$op",
      instrargs = Seq.empty,
      stackargs = Seq(value),
      resultType = S(resultTypeOf(nominal, Seq(value))),
    )

    /** Creates a binary instruction of this family nominally yielding a `nominal`-typed value. */
    private def binary(op: Str, nominal: ValType)(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = s"$prefix.$op",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(resultTypeOf(nominal, Seq(lhs, rhs))),
    )

    /** Creates this family's `const` instruction, carrying the already-rendered immediate `imm`. */
    protected def constInstr(imm: Str): FoldedInstr = FoldedInstr(
      mnemonic = s"$prefix.const",
      instrargs = Seq(doc"$imm"),
      stackargs = Seq.empty,
      resultType = S(valType),
    )

    /** Creates a unary arithmetic instruction, which yields a value of this family's own type. */
    protected def unaryArith(op: Str): Expr => FoldedInstr = unary(op, valType)

    /** Creates a binary arithmetic instruction, which yields a value of this family's own type. */
    protected def binaryArith(op: Str): (Expr, Expr) => FoldedInstr = binary(op, valType)

    /** Creates a test instruction, which yields the `i32` `0`/`1` the test evaluates to. */
    protected def test(op: Str): Expr => FoldedInstr = unary(op, I32Type)

    /** Creates a comparison instruction, which yields the `i32` `0`/`1` the comparison evaluates to. */
    protected def comparison(op: Str): (Expr, Expr) => FoldedInstr = binary(op, I32Type)

    def add(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("add")(lhs, rhs)
    def sub(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("sub")(lhs, rhs)
    def mul(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("mul")(lhs, rhs)

    def eq(lhs: Expr, rhs: Expr): FoldedInstr = comparison("eq")(lhs, rhs)
    def ne(lhs: Expr, rhs: Expr): FoldedInstr = comparison("ne")(lhs, rhs)
  end NumInstrs

  /** The instructions of an integer type family (`i32` and `i64`).
    *
    * Integer division, remainder, right shift and ordering come in a signed and an unsigned flavor; only the ones
    * the backend currently emits are exposed.
    */
  sealed abstract class IntInstrs(valType: NumType) extends NumInstrs(valType):

    def div_s(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("div_s")(lhs, rhs)
    def rem_s(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("rem_s")(lhs, rhs)

    def and(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("and")(lhs, rhs)
    def or(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("or")(lhs, rhs)
    def shl(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("shl")(lhs, rhs)
    def shr_s(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("shr_s")(lhs, rhs)
    def shr_u(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("shr_u")(lhs, rhs)

    def lt_s(lhs: Expr, rhs: Expr): FoldedInstr = comparison("lt_s")(lhs, rhs)
    def le_s(lhs: Expr, rhs: Expr): FoldedInstr = comparison("le_s")(lhs, rhs)
    def gt_s(lhs: Expr, rhs: Expr): FoldedInstr = comparison("gt_s")(lhs, rhs)
    def ge_s(lhs: Expr, rhs: Expr): FoldedInstr = comparison("ge_s")(lhs, rhs)

    /** Creates this family's `ge_u` instruction (greater than or equal, unsigned). */
    def ge_u(lhs: Expr, rhs: Expr): FoldedInstr = comparison("ge_u")(lhs, rhs)

    /** Creates this family's `eqz` instruction, which tests its operand against zero. */
    def eqz(value: Expr): FoldedInstr = test("eqz")(value)
  end IntInstrs

  /** The instructions of a floating-point type family (`f32` and `f64`).
    *
    * Floats have no remainder or `eqz` instruction, and their comparisons carry no signedness; in exchange they have
    * the unary operations below, which have no integer counterpart - an integer negation is written as a subtraction
    * from zero instead.
    */
  sealed abstract class FloatInstrs(valType: NumType) extends NumInstrs(valType):

    def div(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("div")(lhs, rhs)
    def min(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("min")(lhs, rhs)
    def max(lhs: Expr, rhs: Expr): FoldedInstr = binaryArith("max")(lhs, rhs)

    def abs(value: Expr): FoldedInstr = unaryArith("abs")(value)
    def neg(value: Expr): FoldedInstr = unaryArith("neg")(value)
    def sqrt(value: Expr): FoldedInstr = unaryArith("sqrt")(value)

    def lt(lhs: Expr, rhs: Expr): FoldedInstr = comparison("lt")(lhs, rhs)
    def le(lhs: Expr, rhs: Expr): FoldedInstr = comparison("le")(lhs, rhs)
    def gt(lhs: Expr, rhs: Expr): FoldedInstr = comparison("gt")(lhs, rhs)
    def ge(lhs: Expr, rhs: Expr): FoldedInstr = comparison("ge")(lhs, rhs)
  end FloatInstrs

  object FloatInstrs:
    /** Renders `value` as a WAT floating-point literal.
      *
      * Scala's own rendering is WAT-compatible for every finite value - the two agree on decimal and exponent syntax
      * - but not for the three values that have no decimal spelling at all, which WAT writes as `inf`, `-inf` and
      * `nan`.
      */
    def litWat(value: Float | Double): Str =
      val widened = value match
        case f: Float => f.toDouble
        case d: Double => d
      if widened.isNaN then "nan"
      else if widened.isPosInfinity then "inf"
      else if widened.isNegInfinity then "-inf"
      // * Rendered from the operand itself rather than from `widened`, so that an `f32` is spelled in the shortest
      // * form that round-trips at *its* precision, e.g. `0.1` rather than the widened `0.10000000149011612`.
      else value.toString

  object i32 extends IntInstrs(I32Type):
    /** Creates an `i32.const` instruction. */
    def const(value: Int): FoldedInstr = constInstr(value.toString)
  end i32

  object i64 extends IntInstrs(I64Type):
    /** Creates an `i64.const` instruction. */
    def const(value: Long): FoldedInstr = constInstr(value.toString)
  end i64

  object f32 extends FloatInstrs(F32Type):
    /** Creates an `f32.const` instruction. */
    def const(value: Float): FoldedInstr = constInstr(FloatInstrs.litWat(value))
  end f32

  object f64 extends FloatInstrs(F64Type):
    /** Creates an `f64.const` instruction. */
    def const(value: Double): FoldedInstr = constInstr(FloatInstrs.litWat(value))
  end f64

  object array:
    /** Creates an `array.len` instruction. */
    def len(arrayRef: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "array.len",
      instrargs = Seq.empty,
      stackargs = Seq(arrayRef),
      resultType = S(I32Type),
    )

    /** Creates an `array.new_fixed` instruction. */
    def new_fixed(arrayType: TypeIdx, items: Seq[Expr]): FoldedInstr = FoldedInstr(
      mnemonic = "array.new_fixed",
      instrargs = Seq(arrayType.toWat, doc"${items.length}"),
      stackargs = items,
      resultType = S(RefType(arrayType, nullable = false)),
    )

    /** Creates an `array.get` instruction. */
    def get(arrayType: TypeIdx, arrayRef: Expr, index: Expr, elemType: Type): FoldedInstr = FoldedInstr(
      mnemonic = "array.get",
      instrargs = Seq(arrayType.toWat),
      stackargs = Seq(arrayRef, index),
      resultType = S(elemType),
    )

    /** Creates an `array.set` instruction. */
    def set(arrayType: TypeIdx, arrayRef: Expr, index: Expr, value: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "array.set",
      instrargs = Seq(arrayType.toWat),
      stackargs = Seq(arrayRef, index, value),
      resultType = N,
    )
  end array

  object ref:
    /** Creates a `ref.null` instruction. */
    def `null`(heapType: HeapType): FoldedInstr = FoldedInstr(
      mnemonic = "ref.null",
      instrargs = Seq(heapType.toWat),
      stackargs = Seq.empty,
      resultType = S(RefType(heapType, nullable = true)),
    )

    /** Creates a `ref.is_null` instruction. */
    def is_null(value: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "ref.is_null",
      instrargs = Seq.empty,
      stackargs = Seq(value),
      resultType = S(I32Type),
    )

    /** Creates a `ref.eq` instruction. */
    def eq(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "ref.eq",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates a `ref.func` instruction. */
    def func(idx: FuncIdx, ty: RefType): FoldedInstr = FoldedInstr(
      mnemonic = "ref.func",
      instrargs = Seq(idx.toWat),
      stackargs = Seq.empty,
      resultType = S(ty),
    )

    /** Creates a `ref.i31` instruction. */
    def i31(value: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "ref.i31",
      instrargs = Seq.empty,
      stackargs = Seq(value),
      resultType = S(RefType.i31ref),
    )

    /** Creates a `ref.test` instruction. */
    def test(value: Expr, castType: RefType): FoldedInstr = FoldedInstr(
      mnemonic = "ref.test",
      instrargs = Seq(castType.toWat),
      stackargs = Seq(value),
      resultType = S(I32Type),
    )

    /** Creates a `ref.cast` instruction. */
    def cast(value: Expr, castType: RefType): FoldedInstr = FoldedInstr(
      mnemonic = "ref.cast",
      instrargs = Seq(castType.toWat),
      stackargs = Seq(value),
      resultType = S(castType),
    )
  end ref

  object i31:
    def get(i31: Expr, signed: Bool): FoldedInstr = FoldedInstr(
      mnemonic = s"i31.get_${if signed then 's' else 'u'}",
      instrargs = Seq.empty,
      stackargs = Seq(i31),
      resultType = S(I32Type),
    )

    /** Creates an `i31.get_s` instruction. */
    def get_s(i31: Expr): FoldedInstr = get(i31, true)

    /** Creates an `i31.get_u` instruction. */
    def get_u(i31: Expr): FoldedInstr = get(i31, false)
  end i31

  object local:
    /** Creates a `local.get` instruction. */
    def get(index: LocalIdx, ty: Type): FoldedInstr = FoldedInstr(
      mnemonic = "local.get",
      instrargs = Seq(index),
      stackargs = Seq.empty,
      resultType = S(ty),
    )

    /** Creates a `local.tee` instruction. */
    def tee(index: LocalIdx, value: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "local.tee",
      instrargs = Seq(index),
      stackargs = Seq(value),
      resultTypes = value.resultTypes,
    )

    /** Creates a `local.set` instruction. */
    def set(index: LocalIdx, value: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "local.set",
      instrargs = Seq(index),
      stackargs = Seq(value),
      resultType = N,
    )
  end local

  object global:
    /** Creates a `global.get` instruction. */
    def get(index: GlobalIdx, ty: Type): FoldedInstr = FoldedInstr(
      mnemonic = "global.get",
      instrargs = Seq(index),
      stackargs = Seq.empty,
      resultType = S(ty),
    )

    /** Creates a `global.set` instruction. */
    def set(index: GlobalIdx, value: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "global.set",
      instrargs = Seq(index),
      stackargs = Seq(value),
      resultType = N,
    )
  end global

  object struct:
    /** Creates a `struct.new` instruction. */
    def `new`(ty: TypeIdx, fields: Seq[Expr]): FoldedInstr = FoldedInstr(
      mnemonic = "struct.new",
      instrargs = Seq(ty.toWat),
      stackargs = fields,
      resultType = S(RefType(ty, nullable = false)),
    )

    /** Creates a `struct.new_default` instruction. */
    def new_default(ty: TypeIdx): FoldedInstr = FoldedInstr(
      mnemonic = "struct.new_default",
      instrargs = Seq(ty.toWat),
      stackargs = Seq.empty,
      resultType = S(RefType(ty, nullable = false)),
    )

    /** Creates a `struct.set` instruction. */
    def set(index: FieldIdx, ref: Expr, value: FoldedInstr): FoldedInstr = FoldedInstr(
      mnemonic = "struct.set",
      instrargs = Seq(ref.resultType.map(_.asInstanceOf[RefType].heapType).get, index),
      stackargs = Seq(ref, value),
      resultType = N,
    )

    /** Creates a `struct.get` instruction. */
    def get(index: FieldIdx, ref: Expr, ty: Type): FoldedInstr = FoldedInstr(
      mnemonic = "struct.get",
      instrargs = Seq(ref.resultType.map(_.asInstanceOf[RefType].heapType).get, index),
      stackargs = Seq(ref),
      resultType = S(ty),
    )

  end struct

end Instructions
