package hkmc2
package codegen
package wasm
package text

import hkmc2.utils.*, shorthands.*
import semantics.*, Elaborator.State
import scala.collection.mutable

/** A snapshot uses module-local indices only as graph edges, never as destination identifiers.
  * Original symbols are its session-wide identities; relocation allocates every destination name
  * before rebuilding any edge. No backend context or mutable IR definition is retained. */
final case class AbiType(
    index: TypeIdx,
    sym: ExternSymbol,
    wrap: Opt[Str] -> Opt[Str],
    body: CompType,
    tag: Opt[Int],
)
final case class AbiFunction(sym: ExternSymbol, wrap: Opt[Str] -> Opt[Str], name: Str, ty: TypeIdx)
final case class AbiGlobal(index: GlobalIdx, sym: ScopedSymbol, wrap: Opt[Str] -> Opt[Str], name: Str, ty: GlobalType)
final case class AbiClass(
    sym: BlockMemberSymbol,
    rttiType: TypeIdx,
    rttiGlobal: GlobalIdx,
    initializer: BlockMemberSymbol,
    virtualTable: Ctx.VirtualTable,
    singleton: Opt[(Opt[ModuleOrObjectSymbol], GlobalIdx, RefType)],
)
final case class AbiNamespace(sym: BlockMemberSymbol, owner: InnerSymbol, members: Map[Str, BlockMemberSymbol], storage: Map[TermSymbol, ScopedSymbol])
final case class FileInterface(
    types: Vector[AbiType],
    typeGroups: Vector[Vector[TypeIdx]],
    functions: Vector[AbiFunction],
    globals: Vector[AbiGlobal],
    classes: Vector[AbiClass],
    namespaces: Vector[AbiNamespace],
    defaultExport: Opt[BlockMemberSymbol],
)

final case class CompiledWasmFile(module: CompiledWasmModule, interface: FileInterface)
final case class FileImport(name: Str, interface: FileInterface)
final case class FileCompilation(imports: Vector[FileImport], aliases: Map[ScopedSymbol, ScopedSymbol], runtime: Bool)

/** One export namespace, independent of internal WAT scopes and state-local UIDs. */
final class FileExportNames(using State):
  private val scope = utils.Scope.empty(utils.Scope.Cfg.default)
  private val names = mutable.Map.empty[(ValueSymbol, Str, Opt[Str] -> Opt[Str]), Str]
  def apply(sym: ScopedSymbol | ClassSymbol, kind: Str, wrap: Opt[Str] -> Opt[Str])(using Raise): Str =
    names.getOrElseUpdate((sym, kind, wrap),
      scope.allocateName(TempSymbol(N, erasedType = N, wrap._1.fold("")(_ + "_") + sym.nme + wrap._2.fold("")("_" + _))))

/** Relocation is deliberately exhaustive over the WASM type algebra. New ABI-bearing type
  * forms must extend this traversal rather than accidentally retaining an exporting index. */
final class TypeRelocation(resolve: TypeIdx => TypeIdx):
  def index(idx: TypeIdx): TypeIdx = resolve(idx)
  def value(ty: ValType): ValType = ty match
    case RefType(idx: TypeIdx, nullable) => RefType(index(idx), nullable)
    case other => other
  def reference(ty: RefType): RefType = ty.heapType match
    case idx: TypeIdx => RefType(index(idx), ty.nullable)
    case _ => ty
  def global(ty: GlobalType): GlobalType = ty.copy(valType = value(ty.valType))
  def body(ty: CompType): CompType = ty match
    case StructType(fields, parents, isFinal) =>
      StructType(fields.map((sym, field) => sym -> field.copy(ty = value(field.ty))), parents.map(index), isFinal)
    case ArrayType(elem, mutable) => ArrayType(value(elem), mutable)
    case FunctionType(SignatureType(params, results)) =>
      FunctionType(params.map(p => p.copy(valtype = value(p.valtype))), results.map(r => r.copy(valtype = value(r.valtype))))
