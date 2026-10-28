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

final case class WasmRuntime(path: io.Path, compiled: CompiledWasmFile)
final case class WasmGraph(runtime: WasmRuntime, files: Vector[(Artifact, io.Path, CompiledWasmFile)])

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
        FileCompilation(Vector.empty, Map.empty, runtime = true))
    artifact.materializeWasm(Ls(wat -> compiled.module.wat.mkString(100),
      path -> runtimeLoader(specifier(wat, path.up), compiled.module.entryName)))
    WasmRuntime(path, compiled)

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
          val aliases = (art +: dependencies.keys.toVector).flatMap(_.sourceImports).flatMap: dep =>
            dep.artifact.compilationUnit.defaultExport.map(sym => (dep.sym: ScopedSymbol) -> (sym: ScopedSymbol))
          .toMap
          val compiled = art.compiledWasm(runtime = false):
            given State = art.state
            given Elaborator.Ctx = art.ctx
            val sourceSymbols = art.sourceImports.map(_.sym).toSet
            art.ir.imports.foreach: (sym, importedPath) =>
              if !sourceSymbols(sym) && sym != State.runtimeSymbol then
                raise(ErrorReport(msg"JavaScript import '$importedPath' is not supported in WASM source" -> sym.toLoc :: Nil,
                  source = Diagnostic.Source.Compilation))
            WatBuilder.fresh.fileModule(art.ir.copy(imports = art.ir.imports.filterNot(_._1 == State.runtimeSymbol)), art.compilationUnit.defaultExport, path.up,
              FileCompilation(bindings, aliases, runtime = false))
          val out = output(path, ".mjs")
          val watPath = output(path, ".wat")
          val imports = imported.zipWithIndex.map:
            case ((source, _), i) =>
              // Static sibling imports with top-level await can initialize concurrently.
              // Await dependencies in source order to preserve observable side effects.
              s"const { wasmExports: module$i } = await import(${makeStringLiteral(specifier(output(source, ".mjs"), path.up))});"
          val importObject = imported.indices.map(i => s"module$i").mkString(", ")
          val default = facade(compiled.interface)
          val loader = s"""import { instantiate, system, invoke } from ${makeStringLiteral(specifier(runtimePath, path.up))};
${imports.mkString("\n")}
const instance = await instantiate(new URL(${makeStringLiteral(specifier(watPath, path.up))}, import.meta.url), { system, $importObject }, ${compiled.module.systemMemMinPages});
export const wasmExports = instance.exports;
invoke(wasmExports[${makeStringLiteral(compiled.module.entryName)}]);
export default $default;
"""
          art.materializeWasm(Ls(watPath -> compiled.module.wat.mkString(100), out -> loader))
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
    def callable(f: AbiFunction): Str =
      val invoke = s"invoke(wasmExports[${makeStringLiteral(f.name)}], ...args)"
      if f.optionalParams.isEmpty then s"((...args) => $invoke)"
      else
        // WebAssembly's JS boundary supplies undefined for missing arguments. Only absent
        // optional slots become null; explicit undefined and required slots keep their values.
        val padding = f.optionalParams.toVector.sorted.map(i => s"if (args.length <= $i) args[$i] = null;").mkString(" ")
        s"((...args) => { $padding return $invoke; })"
    def value(sym: ValueSymbol): Str =
      val singleton = abi.classes.find(_.sym == sym).flatMap(_.singleton).flatMap { case (_, idx, _) =>
        abi.globals.find(_.index == idx).map(g => s"wasmExports[${makeStringLiteral(g.name)}].value")
      }
      singleton.getOrElse:
        function(sym) match
          case S(f) =>
            // A function companion and its class have separate ABI identities. Keep the
            // function callable and expose the constructor through the companion's `.class`.
            constructor(sym).filter(_.sym != f.sym).fold(callable(f)): ctor =>
              s"Object.assign(${callable(f)}, { class: ${callable(ctor)} })"
          case N =>
            abi.globals.find(_.sym == sym).map(g => s"wasmExports[${makeStringLiteral(g.name)}].value")
              .getOrElse(lastWords(s"Missing WASM default export binding for $sym"))
    abi.defaultExport.fold("undefined"): sym =>
      abi.namespaces.find(_.sym == sym) match
        case S(ns) =>
          ns.members.toVector.sortBy(_._1).map: (name, member) =>
            if function(member).nonEmpty then s"[${makeStringLiteral(name)}]: ${value(member)}"
            else s"get [${makeStringLiteral(name)}]() { return ${value(member)}; }"
          .mkString("{ ", ", ", " }")
        case N => value(sym)

  private def runtimeLoader(wat: Str, entry: Str): Str = s"""import binaryen from "binaryen";
import { readFile } from "node:fs/promises";

export async function instantiate(url, imports, pages) {
  const memory = new WebAssembly.Memory({ initial: pages });
  const decoder = new TextDecoder("utf-16le");
  const localSystem = {
    ...imports.system,
    mem: memory,
    mlx_str_from_utf16: (ptr, length) => decoder.decode(new Uint8Array(memory.buffer, ptr, length)),
  };
  const module = binaryen.parseText(await readFile(url, "utf8"), binaryen.Features.All);
  let binary;
  try {
    if (!module.validate()) throw new Error("Invalid generated WASM module: " + url);
    binary = module.emitBinary();
  } finally {
    module.dispose();
  }
  return new WebAssembly.Instance(new WebAssembly.Module(binary), { ...imports, system: localSystem });
}

const runtime = await instantiate(new URL(${makeStringLiteral(wat)}, import.meta.url), {}, 0);
export const system = runtime.exports;
system[${makeStringLiteral(entry)}]();
export function invoke(fn, ...args) {
  try { return fn(...args); }
  catch (error) {
    if (error instanceof WebAssembly.Exception && error.is(system.mlx_exn))
      throw error.getArg(system.mlx_exn, 0);
    throw error;
  }
}
"""
