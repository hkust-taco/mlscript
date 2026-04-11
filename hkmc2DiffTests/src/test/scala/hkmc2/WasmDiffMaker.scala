package hkmc2

import mlscript.utils.*, shorthands.*

import codegen.*
import codegen.js.JSBuilder
import codegen.wasm.*
import document.*
import semantics.Elaborator
import semantics.Term.Blk
import text.WatBuilder
import Diagnostic.Source
import Message.MessageContext

import scala.collection.mutable

abstract class WasmDiffMaker extends LlirDiffMaker:

  /** Outputs the compiled module as [[WasmGenerator]] implementation-defined text.
    */
  val wat = NullaryCommand("wat")

  /** Outputs the compiled module as stack-based text. */
  val swat = NullaryCommand("swat")

  /** Outputs the compiled module as folded text (i.e. S-expression). */
  val fwat = NullaryCommand("fwat")

  private val baseScp: utils.Scope =
    utils.Scope.empty(utils.Scope.Cfg.default)

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

  
  override def processIRBlock(pgrm: Program, definedValues: ComputeDefinedValues)(using Config, Raise, Elaborator.Ctx): Unit =
    
    super.processIRBlock(pgrm, definedValues)

    val outerRaise: Raise = summon

    if wasm.isSet then
      
      val reportedMessages = mutable.Set.empty[Str]
      
      loadWasm

      var errored = false
      given Raise =
        case d @ ErrorReport(source = Source.Compilation) =>
          errored = true
          reportedMessages += d.mainMsg
          outerRaise(d)
        case d => outerRaise(d)
      val (modWat, mainFnNme, systemMemMinPages) = ltl.givenIn:
        baseScp.nest.givenIn:
          WatBuilder().program(pgrm, N, wd)
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

      val importObj =
        doc"""
          {
            "system": {
              "mem": mem,
              "mlx_str_from_utf16": (ptr, byteLen) =>
                decodeUtf16.decode(new Uint8Array(mem.buffer, ptr, byteLen))
            }
          }
        """
          .stripBreaks
          .mkString(output.ColWidth)
      val jsStr =
        doc"""
          await (() => {
            # const watSrc = $modWatJsLit;
            # const mem = new WebAssembly.Memory({ initial: $systemMemMinPages });
            # const decodeUtf16 = new TextDecoder("utf-16le");
            # const importObj = $importObj;
            # return wasm.binaryenPrintFuncRes(watSrc, importObj, exports => exports.${mainFnNme}());
            # })();
        """
          .stripBreaks
          .mkString(output.ColWidth)
      output("Wasm result:")
      mkQuery("", jsStr): out =>
        // Omit the last line which is always "undefined" or the unit.
        val result = out.lastIndexOf('\n') match
          case n if n >= 0 => out.substring(0, n)
          case _ => ""
        output(s"= $result")
    end if
  
  end processIRBlock
  
end WasmDiffMaker
