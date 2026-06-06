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
    resultType = N,
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

  object i32:
    /** Creates an `i32.const` instruction. */
    def const(value: Int): FoldedInstr = FoldedInstr(
      mnemonic = "i32.const",
      instrargs = Seq(doc"$value"),
      stackargs = Seq.empty,
      resultType = S(I32Type),
    )

    /** Creates an `i32.add` instruction. */
    def add(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.add",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.add` instruction. */
    def eq(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.eq",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(
        (lhs.resultType, rhs.resultType) match
          case (UnreachableType, _) | (_, UnreachableType) => UnreachableType
          case _ => I32Type,
      ),
    )

    /** Creates an `i32.ge_u` instruction (greater than or equal, unsigned). */
    def ge_u(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.ge_u",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.and` instruction. */
    def and(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.and",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.or` instruction. */
    def or(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.or",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.sub` instruction. */
    def sub(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.sub",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.mul` instruction. */
    def mul(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.mul",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.div_s` instruction. */
    def div_s(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.div_s",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.rem_s` instruction. */
    def rem_s(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.rem_s",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.ne` instruction. */
    def ne(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.ne",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.lt_s` instruction. */
    def lt_s(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.lt_s",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.le_s` instruction. */
    def le_s(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.le_s",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.gt_s` instruction. */
    def gt_s(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.gt_s",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.ge_s` instruction. */
    def ge_s(lhs: Expr, rhs: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.ge_s",
      instrargs = Seq.empty,
      stackargs = Seq(lhs, rhs),
      resultType = S(I32Type),
    )

    /** Creates an `i32.eqz` instruction. */
    def eqz(value: Expr): FoldedInstr = FoldedInstr(
      mnemonic = "i32.eqz",
      instrargs = Seq.empty,
      stackargs = Seq(value),
      resultType = S(I32Type),
    )
  end i32

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
      instrargs = Seq(ref.resultType_!.asInstanceOf[RefType].heapType, index),
      stackargs = Seq(ref, value),
      resultType = N,
    )

    /** Creates a `struct.get` instruction. */
    def get(index: FieldIdx, ref: Expr, ty: Type): FoldedInstr = FoldedInstr(
      mnemonic = "struct.get",
      instrargs = Seq(ref.resultType_!.asInstanceOf[RefType].heapType, index),
      stackargs = Seq(ref),
      resultType = S(ty),
    )

  end struct

end Instructions
