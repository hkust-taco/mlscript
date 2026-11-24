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
/** Optional slot indices retain source omission semantics after parameter types are erased. */
final case class AbiFunction(sym: ExternSymbol, wrap: Opt[Str] -> Opt[Str], name: Str, ty: TypeIdx, optionalParams: Set[Int])
final case class AbiGlobal(index: GlobalIdx, sym: ScopedSymbol, wrap: Opt[Str] -> Opt[Str], name: Str, ty: GlobalType)
/** A class or object exported with its layout, RTTI, initializer, and virtual table.
  * Only an object has a `singleton`: the global that holds its instance and that global's type. */
final case class AbiClass(
    sym: BaseTypeSymbol,
    rttiType: TypeIdx,
    rttiGlobal: GlobalIdx,
    initializer: BlockMemberSymbol,
    virtualTable: Ctx.VirtualTable,
    singleton: Opt[(GlobalIdx, RefType)],
)
/** A standalone module, whose members are static.
  *
  * @param sym
  *   The module's binding, which a default export names.
  * @param members
  *   The bindings of the public fields and of the methods by source name, which the module's JavaScript facade exports.
  * @param storage
  *   The global that holds each field: a public field's binding, or a backend slot for a private field.
  * @param methods
  *   The binding that identifies the function of each method.
  */
final case class AbiNamespace(
    sym: BlockMemberSymbol,
    module: ModuleOrObjectSymbol,
    members: Map[Str, BlockMemberSymbol],
    storage: Map[TermSymbol, ScopedSymbol],
    methods: Map[TermSymbol, BlockMemberSymbol],
)
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
/** @param sourceImports
  *   The symbols bound by the program's `.mls` imports. Each is the imported file's default export itself, even under
  *   an alias (see `Importer`), so the interfaces in `imports` already define it and these imports emit no code.
  */
final case class FileCompilation(imports: Vector[FileImport], sourceImports: Set[ImportSymbol])

/** One export namespace, independent of internal WAT scopes and state-local UIDs. */
final class FileExportNames(using State):
  private val scope = utils.Scope.empty(utils.Scope.Cfg.default)
  private val names = mutable.Map.empty[(ValueSymbol, Str, Opt[Str] -> Opt[Str]), Str]
  def apply(sym: WasmSymbol, kind: Str, wrap: Opt[Str] -> Opt[Str])(using Raise): Str =
    names.getOrElseUpdate((sym, kind, wrap),
      scope.allocateName(TempSymbol(N, initErasedType = N, wrap._1.fold("")(_ + "_") + sym.nme + wrap._2.fold("")("_" + _))))

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
