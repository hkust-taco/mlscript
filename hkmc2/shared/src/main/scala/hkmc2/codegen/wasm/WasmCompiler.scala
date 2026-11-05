package hkmc2
package codegen
package wasm

import hkmc2.utils.*, shorthands.*
import hkmc2.Message.MessageContext
import semantics.*, Elaborator.State
import CompilerCache.Artifact
import text.*
import js.JSBuilder.makeStringLiteral
import scala.collection.mutable

final case class WasmRuntime(path: io.Path, watPath: io.Path, compiled: CompiledWasmFile)
final case class WasmGraph(runtime: WasmRuntime, files: Vector[(Artifact, io.Path, CompiledWasmFile)])

object WasmCompiler:
  /** Native ES-module operations and raw foreign-call results are the host boundary.
    * Boxing prevents MLscript's ordinary foreign-call conversion from replacing undefined with Unit. */
  val nativeBridge: Str =
    "{ importModule: url => import(url), apply: (fn, receiver, args) => ({ value: Reflect.apply(fn, receiver, args) }) }"

/** Materializes a graph of cached frontend artifacts. Backend memoization and output writing
  * are separate: a valid memoized artifact must still restore missing output files. */
final class WasmCompiler(using cctx: CompilerCtx, tl: TraceLogger):
  private def output(source: io.Path, extension: Str): io.Path = source.up / (source.baseName + extension)

  private def specifier(path: io.Path, from: io.Path): Str =
    val relative = path.relativeTo(from).getOrElse:
      lastWords(s"Cannot form a relative WASM module URL from $from to $path")
    // URL escaping is separate from JavaScript string escaping. In particular, # and % in
    // actual filenames must not turn into a fragment or an already-encoded URL component.
    val encoded = relative.toString.replace('\\', '/').getBytes("UTF-8").iterator.map: byte =>
      val n = byte & 255
      if n >= 65 && n <= 90 || n >= 97 && n <= 122 || n >= 48 && n <= 57 || "-._~/".contains(n.toChar)
      then n.toChar.toString else f"%%$n%02X"
    .mkString
    if encoded.startsWith(".") then encoded else "./" + encoded

  def runtime()(using Raise): WasmRuntime =
    val source = cctx.paths.runtimeSourceFile
    val prelude = cctx.getPrelude(cctx.paths.preludeFile).ctx
    val artifact = cctx.getElaboratedBlock(source, prelude)
    val path = source.up / "RuntimeWasm.mjs"
    val wat = source.up / "RuntimeWasm.wat"
    val compiled = artifact.compiledWasm(runtime = true):
      given State = artifact.state
      given Elaborator.Ctx = artifact.ctx
      WatBuilder.fresh.fileModule(Program(Nil, End()), N, source.up,
        FileCompilation(Vector.empty, Set.empty, runtime = true))
    // Compile the host library through the ordinary JavaScript backend, including on
    // cache hits so a missing or overwritten output is restored from its source artifact.
    new MLsCompiler(_ => summon[Raise]).compileModule(source.up / "RuntimeWasm.mls")
    artifact.materialize(Ls(wat -> compiled.module.wat.mkString(100)))
    WasmRuntime(path, wat, compiled)

  def compile(file: io.Path, artifact: Artifact, report: io.Path => Raise): WasmGraph =
    def reporting(path: io.Path): Raise = d =>
      report(path)(d)
      d match
        case _: ErrorReport => throw d
        case _ => ()
    given Raise = reporting(file)
    val support = this.runtime()
    val runtimePath = support.path
    val runtime = support.compiled
    val done = mutable.LinkedHashMap.empty[Artifact, (io.Path, CompiledWasmFile)]
    def emit(path: io.Path, art: Artifact): CompiledWasmFile =
      done.get(art) match
        case S((_, result)) => result
        case N =>
          given Raise = reporting(path)
          if output(path, ".mjs") == runtimePath then
            raise(ErrorReport(msg"The output path '${runtimePath.toString}' is reserved for WASM runtime support" -> N :: Nil,
              source = Diagnostic.Source.Compilation))
          art.sourceImports.foreach(dep => emit(dep.path, dep.artifact))
          val dependencies = mutable.LinkedHashMap.empty[Artifact, (io.Path, CompiledWasmFile)]
          def include(a: Artifact): Unit = a.sourceImports.foreach: dep =>
            if !dependencies.contains(dep.artifact) then
              include(dep.artifact)
              dependencies(dep.artifact) = done(dep.artifact)
          include(art)
          val imported = dependencies.values.toVector
          val bindings = FileImport("system", runtime.interface) +:
            imported.zipWithIndex.map { case ((_, compiled), i) => FileImport(s"module$i", compiled.interface) }
          val compiled = art.compiledWasm(runtime = false):
            given State = art.state
            given Elaborator.Ctx = art.ctx
            val sourceSymbols = art.sourceImports.map(_.sym).toSet
            art.ir.imports.foreach: (sym, importedPath) =>
              if !sourceSymbols(sym) && sym != State.runtimeSymbol then
                raise(ErrorReport(msg"JavaScript import '$importedPath' is not supported in WASM source" -> sym.toLoc :: Nil,
                  source = Diagnostic.Source.Compilation))
            WatBuilder.fresh.fileModule(art.ir.copy(imports = art.ir.imports.filterNot(_._1 == State.runtimeSymbol)), art.compilationUnit.defaultExport, path.up,
              FileCompilation(bindings, sourceSymbols, runtime = false))
          val out = output(path, ".mjs")
          val watPath = output(path, ".wat")
          val dependencyPaths = imported.iterator.map { case (source, _) =>
            makeStringLiteral(specifier(output(source, ".mjs"), path.up))
          }.mkString("[", ", ", "]")
          val metadata = s"""{ runtime: { path: ${makeStringLiteral(specifier(support.watPath, path.up))}, entry: ${makeStringLiteral(runtime.module.entryName)} },
  wat: ${makeStringLiteral(specifier(watPath, path.up))}, entry: ${makeStringLiteral(compiled.module.entryName)}, pages: ${compiled.module.systemMemMinPages},
  dependencies: $dependencyPaths, export: ${facade(compiled.interface)} }"""
          // RuntimeWasm owns loading, initialization, and host wrappers. Only ESM syntax
          // and the ABI data extracted from this compilation unit are emitted here.
          val loader = s"""import RuntimeWasm from ${makeStringLiteral(specifier(runtimePath, path.up))};
const loaded = await RuntimeWasm.loadModule(import.meta.url, $metadata, ${WasmCompiler.nativeBridge});
export const wasmExports = loaded.wasmExports;
export default loaded.defaultExport;
"""
          art.materialize(Ls(watPath -> compiled.module.wat.mkString(100), out -> loader))
          done(art) = path -> compiled
          compiled
    end emit

    emit(file, artifact)
    WasmGraph(support, done.iterator.map { case (art, (path, compiled)) => (art, path, compiled) }.toVector)

  private def facade(abi: FileInterface): Str =
    def constructor(sym: ValueSymbol): Opt[AbiFunction] =
      sym.asCls.flatMap(cls => abi.functions.find(_.sym == cls))
    def function(sym: ValueSymbol): Opt[AbiFunction] =
      abi.functions.find(_.sym == sym).orElse(constructor(sym))
    def callable(f: AbiFunction, ctor: Opt[AbiFunction]): Str =
      val optional = f.optionalParams.toVector.sorted.mkString("[", ", ", "]")
      s"""{ kind: "function", name: ${makeStringLiteral(f.name)}, optionalParams: $optional, constructor: ${ctor.fold("null")(callable(_, N))} }"""
    def global(name: Str): Str = s"""{ kind: "global", name: ${makeStringLiteral(name)} }"""
    def value(sym: ValueSymbol): Str =
      // The default export is a binding; exported classes are identified by their definitions.
      val singleton = abi.classes.find(_.sym.bms.contains(sym)).flatMap(_.singleton).flatMap { case (idx, _) =>
        abi.globals.find(_.index == idx).map(g => global(g.name))
      }
      singleton.getOrElse:
        function(sym) match
          case S(f) => callable(f, constructor(sym).filter(_.sym != f.sym))
          case N =>
            abi.globals.find(_.sym == sym).map(g => global(g.name))
              .getOrElse(lastWords(s"Missing WASM default export binding for $sym"))
    abi.defaultExport.fold("""{ kind: "undefined" }"""): sym =>
      abi.namespaces.find(_.sym == sym) match
        case S(ns) =>
          ns.members.toVector.sortBy(_._1).iterator.map: (name, member) =>
            s"""{ name: ${makeStringLiteral(name)}, getter: ${function(member).isEmpty}, value: ${value(member)} }"""
          .mkString("""{ kind: "namespace", members: [""", ", ", "] }")
        case N => value(sym)
