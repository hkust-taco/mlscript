package hkmc2
package codegen.wasm
package text

import mlscript.utils.*, shorthands.*

import document.*
import semantics.DefinitionSymbol

import scala.collection.Map

extension (doc: Document)
  /** Surrounds a document by the given `prefix` and `suffix`, unless the document is empty. */
  private def surroundUnlessEmpty(
      prefix: Document = Document.empty,
      postfix: Document = Document.empty
  ): Document =
    doc.optionUnless(_.isEmpty).fold(doc):
      prefix :: _ :: postfix

/** Trait indicating a WAT representation is available. */
trait ToWat:
  /** Converts this object into a WAT representation. */
  def toWat: Document

/** Abstract base class for all Wasm types. */
abstract sealed class Type extends ToWat:

  /** Attempts to convert this type to a [[[ValType]]]. */
  def asValType: Opt[ValType] = this match
    case ty: ValType => S(ty)
    case _ => N

  /** Same as [[[asValType]]], except throws an exception if this type is not a `ValType`. */
  def asValType_! : ValType = asValType.getOrElse:
    lastWords(s"asValType_! called on non-ValType: `$toWat` (${getClass.getName})")

private case object I32Type extends Type:
  def toWat: Document = doc"i32"
private case object I64Type extends Type:
  def toWat: Document = doc"i64"
private case object F32Type extends Type:
  def toWat: Document = doc"f32"
private case object F64Type extends Type:
  def toWat: Document = doc"f64"
private case object V128Type extends Type:
  def toWat: Document = doc"v128"
private case object UnreachableType extends Type:
  def toWat: Document = throw UnsupportedOperationException(
    s"${toString} is a compiler-internal type and cannot be converted to WAT"
  )

type NumType = I32Type.type | I64Type.type | F32Type.type | F64Type.type
type VecType = V128Type.type

object RefType:
  def anyref: RefType = RefType(HeapType.Any, nullable = true)
  def i31ref: RefType = RefType(HeapType.I31, nullable = true)
  def funcref: RefType = RefType(HeapType.Func, nullable = true)

/** Wasm type representing a reference to a [[HeapType]]. */
case class RefType(heapType: HeapType, nullable: Bool) extends Type:
  def toWat: Document =
    doc"(ref${if nullable then " null" else ""} ${heapType.toWat})"

object HeapType:
  case object Func extends ToWat:
    def toWat: Document = doc"func"
  case object Ext extends ToWat:
    def toWat: Document = doc"extern"
  case object Any extends ToWat:
    def toWat: Document = doc"any"
  case object Eq extends ToWat:
    def toWat: Document = doc"eq"
  case object I31 extends ToWat:
    def toWat: Document = doc"i31"
  case object Struct extends ToWat:
    def toWat: Document = doc"struct"
  case object Array extends ToWat:
    def toWat: Document = doc"array"
  case object None extends ToWat:
    def toWat: Document = doc"none"
  case object NoExt extends ToWat:
    def toWat: Document = doc"noextern"
  case object NoFunc extends ToWat:
    def toWat: Document = doc"nofunc"
type ValType = NumType | VecType | RefType

/** A Wasm parameter clause. Appears in function signatures. */
case class Param(id: Opt[Str], valtype: ValType) extends ToWat:
  def toWat: Document =
    doc"(param${id.fold(doc"")(id => doc" $$$id")} ${valtype.toWat})"

/** A Wasm result clause. Appears in function signatures and some instructions. */
case class Result(valtype: ValType) extends ToWat:
  def toWat: Document = doc"(result ${valtype.toWat})"

/**
 * A type representing a function signature.
 *
 * Function signatures differ from [[FunctionType]] in that they do not include the `func` keyword.
 */
case class SignatureType(params: Seq[Param], results: Seq[Result]) extends ToWat:
  def toWat: Document = (params.map(_.toWat) ++ results.map(_.toWat)).mkDocument(doc" ")

object FunctionType:
  def apply(params: Seq[Param], results: Seq[Result]): FunctionType =
    new FunctionType(SignatureType(params, results))

/** A type representing a function type. */
case class FunctionType(sigType: SignatureType) extends ToWat:
  def toWat: Document =
    doc"(func${sigType.toWat.surroundUnlessEmpty(doc" ")})"

/** A type representing a struct field. */
case class Field(
    ty: Type,
    mutable: Bool,
    id: Opt[Str]
) extends ToWat:
  def toWat: Document =
    doc"(field ${id.fold(doc"")(id => doc"$$$id ")}${
        if mutable then doc"(mut ${ty.toWat})" else ty.toWat
      })"

/** A type representing a structure type. */
case class StructType(fields: Map[DefinitionSymbol[?], NumIdx -> Field]) extends ToWat:

  def fieldSeq: Seq[Field] = fields.values.toSeq.sortBy(_._1.index).map(_._2)

  def toWat: Document =
    doc"(struct${fieldSeq.map(_.toWat).mkDocument(doc" ").surroundUnlessEmpty(doc" ")})"

/** A composite type. */
type CompType = StructType | FunctionType

type AbsHeapType =
  HeapType.Func.type
    | HeapType.Ext.type
    | HeapType.Any.type
    | HeapType.Eq.type
    | HeapType.I31.type
    | HeapType.Struct.type
    | HeapType.Array.type
    | HeapType.None.type
    | HeapType.NoExt.type
    | HeapType.NoFunc.type
type HeapType = AbsHeapType | TypeIdx

abstract sealed class Index extends ToWat

/** A numeric index. */
case class NumIdx(val index: Int) extends Index:
  def toWat: Document = doc"${index.toString}"

/** A symbolic identifier. */
case class SymIdx(val id: Str) extends Index:
  def toWat: Document = doc"$$$id"

/** An index that is bound to an index space. */
abstract sealed class CtxIdx(idx: Index) extends ToWat:
  def toWat: Document = idx.toWat

/** An index bound to the ''types'' index space. */
case class TypeIdx(idx: Index) extends CtxIdx(idx)

/** An index bound to the ''global'' index space. */
case class GlobalIdx(idx: Index) extends CtxIdx(idx)

/** An index bound to the ''funcs'' index space. */
case class FuncIdx(idx: Index) extends CtxIdx(idx)

/** An index bound to the ''locals'' index space. */
case class LocalIdx(idx: Index) extends CtxIdx(idx)

/** An index bound to the ''fields'' index space. */
case class FieldIdx(idx: Index) extends CtxIdx(idx)

/**
 * An abstraction over a generic WebAssembly instructions.
 */
abstract sealed class Instruction extends ToWat:
  /** The mnemonic of the instruction, e.g. "i32.add". */
  val mnemonic: String

  /**
   * The arguments to the instruction. Note that this only includes arguments that are directly part
   * of the instruction, not the stack arguments.
   *
   * For example, for `i32.add` this would be empty, but for `i32.const 42`, this would be
   * `Seq(doc"42")`.
   */
  val instrargs: Seq[ToWat | Document]

object FoldedInstr:
  def apply(
      mnemonic: Str,
      instrargs: Seq[ToWat | Document],
      stackargs: Seq[FoldedInstr],
      resultType: Opt[Type]
  ): FoldedInstr =
    new FoldedInstr(mnemonic, instrargs, stackargs, resultType.toSeq)

/**
 * A WebAssembly folded instruction.
 *
 * @param stackargs
 *   The stack arguments of the instruction.
 */
case class FoldedInstr(
    mnemonic: Str,
    instrargs: Seq[ToWat | Document],
    stackargs: Seq[Expr],
    resultTypes: Seq[Type]
) extends Instruction:

  /** Returns the result type of this instruction if this instruction only has 0-1 result values. */
  def resultType: Opt[Type] = resultTypes match
    case Seq() => N
    case ty :: Seq() => S(ty)
    case _ => lastWords(s"resultType_! called on instruction with multi-value result type: $this")

    /** Returns the singular result type of this instruction, otherwise throws an exception. */
  def resultType_! : Type = resultType.getOrElse:
    lastWords(s"resultType_! called on instruction with a non-unique result type: $this")

  def toWat: Document = doc"($mnemonic${
      instrargs.map: a =>
        a match
          case a: ToWat => a.toWat
          case a: Document => a
      .mkDocument(doc" ").surroundUnlessEmpty(doc" ")
    }${
      stackargs.map(_.toWat).optionIf(_.nonEmpty).map(_.mkDocument(doc" # ")).fold(doc""): args =>
        doc" #{  # $args #} "
    })"
end FoldedInstr

/**
 * A WebAssembly expression, comprised of one or more instructions that generate a result value.
 */
type Expr = FoldedInstr
