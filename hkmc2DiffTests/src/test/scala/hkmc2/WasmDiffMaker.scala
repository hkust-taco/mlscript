package hkmc2

import mlscript.utils.*, shorthands.*

import codegen.Local
import codegen.wasm.*
import document.*
import semantics.Elaborator
import semantics.Term.Blk
import text.{WasmSessionBinding, WatBuilder}
import Diagnostic.Source
import Message.MessageContext

import scala.collection.mutable

abstract class WasmDiffMaker extends LlirDiffMaker:

  /**
   * Outputs the compiled module as [[WasmGenerator]] implementation-defined text.
   */
  val wat = NullaryCommand("wat")

  /** Outputs the compiled module as stack-based text. */
  val swat = NullaryCommand("swat")

  /** Outputs the compiled module as folded text (i.e. S-expression). */
  val fwat = NullaryCommand("fwat")

  private val baseScp: utils.Scope =
    utils.Scope.empty
  private val wasmReplImportsNme = s"${wasmSuppNme}ReplImports"
  private val wasmReplImportsRef = s"globalThis.$wasmReplImportsNme"
  private val sessionImportsBySymbol = mutable.Map.empty[Local, Vector[WasmSessionBinding]]
  private var wasmSessionInitialized = false

  final lazy val wasmSuppFile: io.Path = predefFile.up / "Wasm.mjs"
  final lazy val wasmSuppNme = baseScp.allocateName(Elaborator.State.wasmSymbol)(using throw _)
  final lazy val loadWasm: Unit =
    host.execute(
      s"const $wasmSuppNme = (await import(\"${wasmSuppFile}\")).default;"
    ) match
      case ReplHost.Result(msg) =>
        if msg.startsWith(ReplHost.uncaughtErrorHead) then
          output(s"Failed to load wasm support library: $msg")
      case r => output(s"Failed to load wasm support library: $r")
    ()

  /** Prettifies a JSON-stringified Binaryen-formatted Wat. */
  lazy val prettifyBinaryenWat = (content: Str) =>
    content.substring(2, content.length() - 2).replace("\\\\n", "\n").replace("\\\\\"", "\"")

  /** Resets Wasm REPL session state for a fresh diff run. */
  override def init(): Unit =
    super.init()
    sessionImportsBySymbol.clear()
    wasmSessionInitialized = false

  override def processTerm(trm: Blk, inImport: Bool)(using
      Config,
      Raise
  ): Unit =
    super.processTerm(trm, inImport)

    val outerRaise: Raise = summon

    if wasm.isSet then
      loadWasm

      var errored = false
      given Raise =
        case d @ ErrorReport(source = Source.Compilation) =>
          errored = true
          outerRaise(d)
        case d => outerRaise(d)
      val low = ltl.givenIn:
        codegen.Lowering()
      val le = low.program(trm)
      val sessionImports =
        le.main.freeVars.iterator
          .flatMap(sym => sessionImportsBySymbol.getOrElse(sym, Vector.empty))
          .toSeq
          .distinctBy(_.bindingKey)
      val compiled = ltl.givenIn:
        baseScp.nest.givenIn:
          WatBuilder().program(le, N, wd, sessionImports = sessionImports)
      val modWat = compiled.wat
      val mainFnNme = compiled.entryName

      if wat.isSet then
        output("Wat:")
        output(modWat.mkString())

      // A program with errors may have a WAT that is worth inspecting, but anything that involves
      // using Binaryen requires a valid WAT
      if errored then return

      if fwat.isSet then
        output("Formatted Wat (Folded):")
        doc"JSON.stringify(wasm.binaryenFmtWat(`$modWat`, true));"
          .stripBreaks
          .mkString(100)
          .replace('\n', ' ') |> host.execute match
          case ReplHost.Result(content) =>
            output(prettifyBinaryenWat(content))
          case err =>
            output(s"Error: $err")
            return
      if swat.isSet then
        output("Formatted Wat (Stack):")
        doc"JSON.stringify(wasm.binaryenFmtWat(`$modWat`, false));"
          .stripBreaks
          .mkString(100)
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
          !expectRuntimeOrCodeGenErrors && fixme.isUnset && todo.isUnset
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
                source = Diagnostic.Source.Compilation
              ))
            else
              // Otherwise, it is considered a simple runtime error.
              raise(ErrorReport(
                msg"${message}" -> N :: Nil,
                source = Diagnostic.Source.Runtime
              ))
        if stderr.nonEmpty then output(s"// Standard Error:\n${stderr}")
      end mkQuery

      if !wasmSessionInitialized then
        host.execute(
          s"""$wasmReplImportsRef = { repl: Object.create(null), system: { mem: new WebAssembly.Memory({initial: 100}) } };"""
        ) match
          case ReplHost.Result(_) =>
            wasmSessionInitialized = true
          case r =>
            output(s"Failed to initialize wasm REPL session object: $r")
      val exportAssignments = compiled.sessionExports.flatMap(_.exportNameOpt.toSeq).map: exportName =>
        doc"""$wasmReplImportsRef.repl["$exportName"] = exports["$exportName"];"""
      val jsStr =
        doc"""await wasm.binaryenPrintFuncRes( #  #{ `$modWat # `, # $wasmReplImportsRef, # exports => { # ${
            if exportAssignments.nonEmpty then
              doc"""const result = exports["$mainFnNme"](); # ${
                  exportAssignments.mkDocument(doc" # ")
                } # return result;"""
            else
              doc"""return exports["$mainFnNme"]();"""
          } # }, #}  # );"""
          .stripBreaks
          .mkString(100)
      output("Wasm result:")
      mkQuery("", jsStr): out =>
        // Omit the last line which is always "undefined" or the unit.
        val result = out.lastIndexOf('\n') match
          case n if n >= 0 => out.substring(0, n)
          case _ => ""
        compiled.sessionExports.foreach: binding =>
          binding.bindingSyms.foreach: sym =>
            sessionImportsBySymbol.update(sym, sessionImportsBySymbol.getOrElse(sym, Vector.empty) :+ binding)
        output(s"= $result")
    end if
  end processTerm
end WasmDiffMaker
