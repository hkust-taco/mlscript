package hkmc2
package codegen
package wasm
package text

import mlscript.utils.*, shorthands.*

import document.*
import semantics.{DefinitionSymbol, Elaborator, TempSymbol}, Elaborator.State
import utils.Scope

import scala.collection.Map

extension (doc: Document)
  /** Surrounds a document by the given `prefix` and `suffix`, unless the document is empty. */
  private def surroundUnlessEmpty(
      prefix: => Document = Document.empty,
      postfix: => Document = Document.empty,
  ): Document =
    doc.optionUnless(_.isEmpty).fold(doc): doc =>
      doc"$prefix$doc$postfix"

extension (scp: Scope)
  /** Convenience function for [[Scope.allocateOrGetName]] with an optional prefix and suffix. */
  private[text] def allocateOrGetNameWrapped(sym: ValueSymbol, wrapId: Opt[Str] -> Opt[Str])(using Raise): Str =
    val prefix = wrapId._1.fold("")(prefix => s"${prefix}_")
    wrapId._2 match
      case S(suffix) =>
        scp.lookup(sym).getOrElse:
          scp.addToBindings(sym, s"$prefix${sym.nme}_$suffix", shadow = false)
      case N => scp.allocateOrGetName(sym, prefix)

/** Trait indicating a WAT representation is available. */
trait ToWat:
  /** Converts this object into a WAT representation. */
  def toWat: Document

/** Abstract base class for all Wasm types. */
sealed abstract class Type extends ToWat:

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
    s"${toString} is a compiler-internal type and cannot be converted to WAT",
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
end HeapType
type ValType = NumType | VecType | RefType

/** A Wasm parameter clause. Appears in function signatures. */
case class Param(id: SymIdx, valtype: ValType) extends ToWat:
  def toWat: Document =
    doc"(param ${id.toWat} ${valtype.toWat})"

/** A Wasm result clause. Appears in function signatures and some instructions. */
case class Result(valtype: ValType) extends ToWat:
  def toWat: Document = doc"(result ${valtype.toWat})"

/** A type representing a function signature.
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
case class Field(ty: ValType, mutable: Bool, id: Str) extends ToWat:
  def toWat: Document =
    doc"(field $$$id ${if mutable then doc"(mut ${ty.toWat})" else ty.toWat})"

/** A type representing a structure type. */
case class StructType(
    fields: Seq[DefinitionSymbol[?] -> Field],
    parents: Seq[TypeIdx] = Seq.empty,
    isFinal: Bool = false,
) extends ToWat:

  lazy val fieldsBySym: Map[DefinitionSymbol[?], Field] = fields.toMap

  def toWat: Document =
    val structWat = doc"(struct${fields.map(_._2.toWat).mkDocument(doc" ").surroundUnlessEmpty(doc" ")})"
    if parents.isEmpty && isFinal then
      structWat
    else
      doc"(sub${
          if isFinal then doc" final" else doc""
        }${
          parents.map(_.toWat).mkDocument(doc" ").surroundUnlessEmpty(doc" ")
        } $structWat)"

/** A type representing an array type. */
case class ArrayType(elemType: ValType, mutable: Bool) extends ToWat:
  def toWat: Document =
    val elemDoc = if mutable then doc"(mut ${elemType.toWat})" else elemType.toWat
    doc"(array ${elemDoc})"

/** A composite type. */
type CompType = StructType | FunctionType | ArrayType

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

case class TypeUse(typeIdx: TypeIdx) extends ToWat:
  def toWat: Document = doc"(type ${typeIdx.toWat})"

sealed abstract class Index extends ToWat

/** A symbolic identifier. */
case class SymIdx(val id: Str) extends Index:
  def toWat: Document = doc"$$$id"

/** An index that is bound to an index space. */
sealed abstract class CtxIdx(idx: Index) extends ToWat:
  def toWat: Document = idx.toWat

/** An index bound to the ''types'' index space. */
case class TypeIdx(idx: Index) extends CtxIdx(idx)

/** An index bound to the ''global'' index space. */
case class GlobalIdx(idx: Index) extends CtxIdx(idx)

/** An index bound to the ''memory'' index space. */
case class MemIdx(idx: Index) extends CtxIdx(idx)

/** An index bound to the ''funcs'' index space. */
case class FuncIdx(idx: Index) extends CtxIdx(idx)

/** An index bound to the ''locals'' index space. */
case class LocalIdx(idx: Index) extends CtxIdx(idx)

/** An index bound to the ''fields'' index space. */
case class FieldIdx(idx: Index) extends CtxIdx(idx)

/** An index bound to the ''tags'' index space. */
case class TagIdx(idx: Index) extends CtxIdx(idx)

/** An import entry. */
case class Import[ET <: ExternType](module: Str, name: Str, externType: ET) extends ToWat:
  def toWat: Document =
    doc"""(import "$module" "$name" ${externType.toWat})"""

/** The address type of a memory type. */
enum AddrType extends ToWat:
  case i32
  case i64

  def toWat: Document = this match
    case AddrType.i32 => doc"i32"
    case AddrType.i64 => doc"i64"

/** The size range of resizeable storage. */
case class Limits(min: Int, max: Opt[Int] = N) extends ToWat:
  def toWat: Document = doc"$min${max.fold(doc"")(max => doc" $max")}"

/** A linear memory entry. */
case class MemType(lim: Limits, addrType: AddrType = AddrType.i32) extends ToWat:
  def toWat: Document =
    doc"${addrType.optionIf(_ != AddrType.i32).fold(doc"")(at => doc"${at.toWat} ")}${lim.toWat}"

/** A global type. */
case class GlobalType(valType: ValType, mutable: Bool) extends ToWat:
  def toWat: Document =
    if mutable then doc"(mut ${valType.toWat})"
    else valType.toWat

object ExternType:
  /** An linear memory entry that is externally addressable. */
  case class Mem(memType: MemType, override val sym: ValueSymbol, wrapId: Opt[Str] -> Opt[Str] = N -> N)(using Ctx, Raise)
      extends ExternType(sym):

    val id: SymIdx = SymIdx(summon[Ctx].memoryScp.allocateOrGetNameWrapped(sym, wrapId))

    def toWat: Document = doc"""(memory ${id.toWat} ${memType.toWat})"""

  /** An function entry that is externally addressable. */
  case class Func(typeUse: TypeUse, override val sym: ValueSymbol, wrapId: Opt[Str] -> Opt[Str] = N -> N)(using Ctx, Raise)
      extends ExternType(sym):

    val id: SymIdx = SymIdx(summon[Ctx].funcScp.allocateOrGetNameWrapped(sym, wrapId))

    def toWat: Document = doc"""(func ${id.toWat} ${typeUse.toWat})"""

  /** A global entry that is externally addressable. */
  case class Global(
      globalType: GlobalType,
      override val sym: ValueSymbol,
      wrapId: Opt[Str] -> Opt[Str] = N -> N,
  )(using Ctx, Raise) extends ExternType(sym):

    val id: SymIdx = SymIdx(summon[Ctx].globalScp.allocateOrGetNameWrapped(sym, wrapId))

    def toWat: Document = doc"""(global ${id.toWat} ${globalType.toWat})"""
end ExternType

sealed abstract class ExternType(val sym: ValueSymbol) extends ToWat:

  /** Symbolic identifier for the extern declaration. */
  val id: SymIdx

/** A memory import entry. */
@deprecated("Use `Import` with `ExternType.Mem` instead.")
case class MemoryImport(module: Str, name: Str, id: SymIdx, minPages: Int) extends ToWat:
  def toWat: Document =
    doc"""(import "$module" "$name" (memory ${id.toWat} $minPages))"""

/** A function import entry. */
@deprecated("Use `Import` with `ExternType.Func` instead.")
case class FuncImport(module: Str, name: Str, id: SymIdx, typeIdx: TypeIdx) extends ToWat:
  def toWat: Document =
    doc"""(import "$module" "$name" (func ${id.toWat} (type ${typeIdx.toWat})))"""

/** A memory use entry. */
case class MemUse(memidx: MemIdx) extends ToWat:
  def toWat: Document = doc"(memory ${memidx.toWat})"

object DataSegment:
  /** A passive data segment, which is not associated with any memory and must be explicitly loaded with `memory.init`.
    */
  case class Passive(bytes: Seq[Str], override val sym: ValueSymbol, wrapId: Opt[Str] -> Opt[Str] = N -> N)(using Ctx, Raise)
      extends DataSegment(bytes, sym, wrapId):
    
    def toWat: Document =
      doc"(data ${id.toWat}${bytes.map(s => s"\"$s\"").mkDocument(doc" ").surroundUnlessEmpty(doc" ")})"

  /** An active data segment, which is automatically copied into a memory given by `memuse` and `offset`.
    */
  case class Active(
      offset: Expr,
      bytes: Seq[Str],
      memuse: Opt[MemUse],
      override val sym: ValueSymbol,
      wrapId: Opt[Str] -> Opt[Str] = N -> N,
  )(using Ctx, Raise) extends DataSegment(bytes, sym, wrapId):

    def toWat: Document =
      doc"(data ${id.toWat}${
          memuse.fold(doc"")(memuse => doc" ${memuse.toWat}")
        } ${offset.toWat}${
          bytes.map(s => s"\"$s\"").mkDocument(doc" ").surroundUnlessEmpty(doc" ")
        })"
end DataSegment

/** A data segment entry. */
sealed abstract class DataSegment(bytes: Seq[Str], val sym: ValueSymbol, wrapId: Opt[Str] -> Opt[Str])(using Ctx, Raise)
    extends ToWat:

  /** Symbolic identifier for the data segment. */
  val id = SymIdx(summon[Ctx].dataSegmentScp.allocateOrGetNameWrapped(sym, wrapId))

object ElemSegment:
  /** A passive element segment, which is not associated with any table and must be explicitly initialized with
    * `table.init`.
    */
  case class Passive(
      override val elemlist: RefType -> Seq[Expr],
      override val sym: ValueSymbol,
      wrapId: Opt[Str] -> Opt[Str] = N -> N,
  )(using Ctx, Raise) extends ElemSegment(elemlist, sym, wrapId):
  
    def toWat: Document = doc"(elem ${id.toWat} ${abbrevElemList})"

  /** An active element segment, which is automatically copied into a table given by `offset. */
  case class Active(
      offset: Expr,
      override val elemlist: RefType -> Seq[Expr],
      // TODO(Derppening): Add `tableuse` here if/when we support multiple tables.
      override val sym: ValueSymbol,
      wrapId: Opt[Str] -> Opt[Str] = N -> N,
  )(using Ctx, Raise) extends ElemSegment(elemlist, sym, wrapId):
  
    def toWat: Document = doc"(elem ${id.toWat} ${offset.toWat} ${abbrevElemList})"

  /** A declarative element segment, which is used to forward declare references present in the code (such as using
    * `ref.func`).
    */
  case class Declare(
      override val elemlist: RefType -> Seq[Expr],
      override val sym: ValueSymbol,
      wrapId: Opt[Str] -> Opt[Str] = N -> N,
  )(using Ctx, Raise) extends ElemSegment(elemlist, sym, wrapId):
  
    def toWat: Document = doc"(elem ${id.toWat} declare ${abbrevElemList})"
end ElemSegment

/** An element segment entry. */
sealed abstract class ElemSegment(
    val elemlist: RefType -> Seq[Expr],
    val sym: ValueSymbol,
    wrapId: Opt[Str] -> Opt[Str],
)(using Ctx, Raise) extends ToWat:

  /** Symbolic identifier for the element segment. */
  val id = SymIdx(summon[Ctx].elemSegmentScp.allocateOrGetNameWrapped(sym, wrapId))

  /** Applies abbreviations on the `elemlist` if a simpler replacement is available. */
  protected def abbrevElemList: Document =
    if elemlist._2.forall(_.mnemonic == "ref.func") then
      doc"func${
          elemlist._2.map: e =>
            e.instrargs.head match
              case a: ToWat => a.toWat
              case a: Document => a
          .mkDocument(doc" ").surroundUnlessEmpty(doc" ")
        }"
    else
      doc"${elemlist._1.toWat}${elemlist._2.map(_.toWat).mkDocument(doc" ").surroundUnlessEmpty(doc" ")}"
end ElemSegment

/** An abstraction over a generic WebAssembly instructions.
  */
sealed abstract class Instruction extends ToWat:
  /** The mnemonic of the instruction, e.g. "i32.add". */
  val mnemonic: String

  /** The arguments to the instruction. Note that this only includes arguments that are directly part of the
    * instruction, not the stack arguments.
    *
    * For example, for `i32.add` this would be empty, but for `i32.const 42`, this would be `Seq(doc"42")`.
    */
  val instrargs: Seq[ToWat | Document]

object FoldedInstr:
  def apply(
      mnemonic: Str,
      instrargs: Seq[ToWat | Document],
      stackargs: Seq[FoldedInstr],
      resultType: Opt[Type],
  ): FoldedInstr =
    new FoldedInstr(mnemonic, instrargs, stackargs, resultType.toSeq)

/** A WebAssembly folded instruction.
  *
  * @param stackargs
  *   The stack arguments of the instruction.
  */
case class FoldedInstr(
    mnemonic: Str,
    instrargs: Seq[ToWat | Document],
    stackargs: Seq[Expr],
    resultTypes: Seq[Type],
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
    } #{ ${
      stackargs.map(_.toWat).mkDocument(doc" # ").surroundUnlessEmpty(doc" # ")
    } #} )"
end FoldedInstr

/** A WebAssembly expression, comprised of one or more instructions that generate a result value.
  */
type Expr = FoldedInstr
