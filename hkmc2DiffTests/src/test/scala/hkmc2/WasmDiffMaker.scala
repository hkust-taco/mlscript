package hkmc2

import hkmc2.utils.*, shorthands.*

import codegen.*
import codegen.js.JSBuilder
import codegen.wasm.*
import document.*
import semantics.*
import semantics.Elaborator
import semantics.Term.Blk
import text.{WatBuilder, FileImport, FileCompilation, CompiledWasmFile, FileInterface}
import Diagnostic.Source
import Message.MessageContext

import scala.collection.mutable

abstract class WasmDiffMaker extends InvalMLDiffMaker:

  /** Outputs the compiled module as [[WasmGenerator]] implementation-defined text.
    */
  val wat = NullaryCommand("wat")

  /** Outputs the compiled module as stack-based text. */
  val swat = NullaryCommand("swat")

  /** Outputs the compiled module as folded text (i.e. S-expression). */
  val fwat = NullaryCommand("fwat")

  private val baseScp: utils.Scope =
    utils.Scope.empty(utils.Scope.Cfg.default)
  private val wasmReplImportsNme = s"${wasmSuppNme}ReplImports"
  private val wasmReplImportsRef = s"globalThis.$wasmReplImportsNme"
  private val worksheetInterfaces = mutable.ArrayBuffer.empty[FileInterface]
  private var wasmSessionInitialized = false
  private val linkedFiles = mutable.LinkedHashMap.empty[CompilerCache.Artifact, (io.Path, CompiledWasmFile)]
  private val fileAliases = mutable.Map.empty[ScopedSymbol, ScopedSymbol]
  private val wasmFileRuntimeNme = s"${wasmSuppNme}FileRuntime"
  private var initializingPrelude = false

  override def init(): Unit =
    // The harness imports the JS predef for name resolution. It is not a user WASM
    // dependency, even when :wasm precedes the first block in the worksheet.
    initializingPrelude = true
    try super.init()
    finally initializingPrelude = false

  override def processTerm(blk: Blk, inImport: Bool)(using Config, Raise): Unit =
    if wasm.isSet && config.target == CompilationTarget.Wasm && !inImport && !initializingPrelude then
      val compiler = new WasmCompiler(using cctx, ltl)
      val report = summon[Raise]
      val throwingRaise: Raise = diagnostic =>
        report(diagnostic)
        diagnostic match
          case _: ErrorReport => throw diagnostic
          case _ => ()
      def collect(statement: semantics.Statement)(using Raise): Unit =
        statement match
          case imp: semantics.Import if imp.file.ext == "mls" =>
            val artifact = cctx.getElaboratedBlock(imp.file, prelude)(using ltl, summon[Raise])
            if artifact.config.target != CompilationTarget.Wasm then
              raise(ErrorReport(msg"Cannot import JavaScript source into a WASM worksheet" -> imp.sym.toLoc :: Nil,
                source = Source.Compilation))
            else
              val graph = compiler.compile(imp.file, artifact, _ => summon[Raise])
              graph.files.foreach: (art, path, compiled) =>
                linkedFiles(art) = path -> compiled
                art.sourceImports.foreach: dep =>
                  dep.artifact.compilationUnit.defaultExport.foreach(sym => fileAliases(dep.sym) = sym)
              artifact.compilationUnit.defaultExport.foreach(sym => fileAliases(imp.sym) = sym)
          case _ => ()
        statement.subStatements.foreach(collect)
      try collect(blk)(using throwingRaise)
      catch case _: Diagnostic => return // The emitter has already reported this diagnostic.
    super.processTerm(blk, inImport)


  final lazy val wasmSuppFile: io.Path = predefFile.up / "wasm" / "Wasm.mjs"
  final lazy val wasmSuppNme = baseScp.allocateName(Elaborator.State.wasmSymbol)(using throw _)
  final lazy val loadWasm: Unit =
    host.execute(
      s"const $wasmSuppNme = (await import(\"${wasmSuppFile}\")).default;",
    ) match
      case ReplHost.Result(msg) =>
        if msg.startsWith(ReplHost.uncaughtErrorHead) then
          output(s"Failed to load wasm support library: $msg")
      case r => output(s"Failed to load wasm support library: $r")
    ()

  /** Prettifies a JSON-stringified Binaryen-formatted Wat. */
  lazy val prettifyBinaryenWat = (content: Str) =>
    content.substring(2, content.length() - 2).replace("\\\\n", "\n").replace("\\\\\"", "\"")

  override def processTrees(trees: Ls[syntax.Tree])(using Config, Raise): Unit =
    if trees.nonEmpty && js.isSet && wasm.isSet && config.target == CompilationTarget.Wasm then
      raise(WarningReport(
        msg"Enabling both :js and :wasm is not currently supported; disable one before compiling this block." -> N :: Nil))
    super.processTrees(trees)

  override def processIRBlock(
      pgrm: Program,
      definedValues: ComputeDefinedValues,
      symbolsToPreserve: Set[ScopedSymbol],
  )(using Config, Raise, Elaborator.Ctx): Unit =
    
    super.processIRBlock(pgrm, definedValues, symbolsToPreserve)
    
    val outerRaise: Raise = summon

    if wasm.isSet && config.target == CompilationTarget.Wasm && !initializingPrelude then

      val reportedMessages = mutable.Set.empty[Str]

      loadWasm

      var errored = false
      given Raise =
        case d @ ErrorReport(source = Source.Compilation) =>
          errored = true
          outerRaise(d)
        case d => outerRaise(d)
      val compiled = ltl.givenIn:
        val runtime = new WasmCompiler(using cctx, ltl).runtime()
        val fileImports = Vector(FileImport("system", runtime.compiled.interface)) ++
          linkedFiles.values.toVector.zipWithIndex.map { case ((_, compiled), i) => FileImport(s"module$i", compiled.interface) } ++
          worksheetInterfaces.toVector.zipWithIndex.map((abi, i) => FileImport(s"repl$i", abi))
        WatBuilder.fresh.worksheetModule(pgrm, wd, symbolsToPreserve,
          FileCompilation(fileImports, fileAliases.toMap, runtime = false))
      val modWat = compiled.module.wat
      val mainFnNme = compiled.module.entryName
      val systemMemMinPages = compiled.module.systemMemMinPages
      val modWatJsLit = JSBuilder.makeStringLiteral(modWat.mkString(output.ColWidth))

      if wat.isSet then
        output("Wat:")
        output(modWat.mkString(output.ColWidth))

      // A program with errors may have a WAT that is worth inspecting, but anything that involves
      // using Binaryen requires a valid WAT
      if errored then return

      if fwat.isSet then
        output("Formatted Wat (Folded):")
        doc"JSON.stringify(wasm.binaryenFmtWat($modWatJsLit, true));"
          .stripBreaks
          .mkString(output.ColWidth)
          .replace('\n', ' ') |> host.execute match
          case ReplHost.Result(content) =>
            output(prettifyBinaryenWat(content))
          case err =>
            output(s"Error: $err")
            return
      if swat.isSet then
        output("Formatted Wat (Stack):")
        doc"JSON.stringify(wasm.binaryenFmtWat($modWatJsLit, false));"
          .stripBreaks
          .mkString(output.ColWidth)
          .replace('\n', ' ') |> host.execute match
          case ReplHost.Result(content) =>
            output(prettifyBinaryenWat(content))
          case err =>
            output(s"Error: $err")
            return

      def mkQuery(preStr: Str, jsStr: Str)(k: Str => Unit) =
        val queryStr = jsStr.replaceAll("\n", " ")
        val (reply, stderr) = host.query(
          preStr,
          queryStr,
          !expectRuntimeOrCodeGenErrors && !expectErrors,
        )
        reply match
          case ReplHost.Result(content) => k(content)
          case ReplHost.Empty =>
          case ReplHost.Unexecuted(message) => ???
          case ReplHost.Error(isSyntaxError, message, otherOutputs) =>
            if otherOutputs.nonEmpty then
              otherOutputs.splitSane('\n').foreach: line =>
                output(s"> ${line}")
            if isSyntaxError then
              // If there is a syntax error in the generated code,
              // it should be a code generation error.
              raise(ErrorReport(
                msg"[Uncaught SyntaxError] ${message}" -> N :: Nil,
                source = Diagnostic.Source.Compilation,
              ))
            else
              // Otherwise, it is considered a simple runtime error.
              raise(ErrorReport(
                msg"${message}" -> N :: Nil,
                source = Diagnostic.Source.Runtime,
              ))
        end match
        if stderr.nonEmpty then output(s"// Standard Error:\n${stderr}")
      end mkQuery

      def executeSetup(script: Str): Bool = host.execute(script) match
        case ReplHost.Result(content) if !content.startsWith(ReplHost.uncaughtErrorHead) => true
        case other =>
          raise(ErrorReport(msg"Failed to initialize WASM imports: ${other.toString}" -> N :: Nil,
            source = Source.Runtime))
          false

      if !wasmSessionInitialized then
        val runtime = new WasmCompiler(using cctx, ltl).runtime()
        val runtimeUrl = JSBuilder.makeStringLiteral(new java.io.File(runtime.path.toString).toURI.toASCIIString)
        if !executeSetup(s"const $wasmFileRuntimeNme = await import($runtimeUrl); $wasmReplImportsRef = Object.create(null);") then return
        wasmSessionInitialized = true
      var loaded = true
      linkedFiles.values.toVector.zipWithIndex.foreach:
        case ((source, _), i) =>
          val out = source.up / (source.baseName + ".mjs")
          val url = JSBuilder.makeStringLiteral(new java.io.File(out.toString).toURI.toASCIIString)
          if loaded then loaded = executeSetup(s"$wasmReplImportsRef.module$i = (await import($url)).wasmExports;")
      if !loaded then return
      // Each instance retains its own decoder closure and literal memory. Replacing the
      // import object's system property must never overwrite an earlier block's string pool.
      if !executeSetup(s"""(() => {
        const mem = new WebAssembly.Memory({ initial: $systemMemMinPages });
        const decode = new TextDecoder("utf-16le");
        $wasmReplImportsRef.system = {
          ...$wasmFileRuntimeNme.system, mem,
          mlx_str_from_utf16: (ptr, length) => decode.decode(new Uint8Array(mem.buffer, ptr, length)),
        };
      })();""") then return
      val blockIndex = worksheetInterfaces.size
      val jsBody =
        s"""const result = exports["$mainFnNme"](); $wasmReplImportsRef.repl$blockIndex = exports; return result;"""
      val jsStr =
        s"""wasm.binaryenPrintFuncRes($modWatJsLit, $wasmReplImportsRef, exports => { $jsBody });"""
      output("Wasm result:")
      mkQuery("", jsStr): out =>
        // Omit the last line which is always "undefined" or the unit.
        val result = out.lastIndexOf('\n') match
          case n if n >= 0 => out.substring(0, n)
          case _ => ""
        worksheetInterfaces += compiled.interface
        expect.get match
          case S(expected) if result =/= expected => raise:
            ErrorReport(msg"Expected: '$expected', got: '$result'" -> N :: Nil,
              source = Source.Runtime)
          case _ => ()
        output(s"= $result")
    end if

  end processIRBlock

end WasmDiffMaker
