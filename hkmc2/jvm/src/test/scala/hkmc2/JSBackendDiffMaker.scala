package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*


abstract class JSBackendDiffMaker extends MLsDiffMaker:
  
  val js = NullaryCommand("js")
  val showRepl = NullaryCommand("showRepl")
  
  lazy val host =
    hostCreated = true
    val h = ReplHost()
    h.execute("let res")
    h
  
  private var hostCreated = false
  override def run(): Unit =
    try super.run() finally if hostCreated then host.terminate()
  
  override def processTerm(trm: semantics.Term, inImport: Bool)(using Raise): Unit =
    super.processTerm(trm, inImport)
    if js.isSet then
      val low = codegen.Lowering()
      val le = low.topLevel(trm)
      if showLoweredTree.isSet then
        output(s"Lowered:")
        output(le.showAsTree)
      val jsb = codegen.js.JSBuilder()
      given codegen.js.Scope = codegen.js.Scope.empty
      val je = jsb.body(le)
      output(s"JS:")
      val jsStr = je.stripBreaks.mkString(100)
      output(jsStr)
      val queryStr =
        s"${jsStr.replaceAll("\n", " ")}; globalThis[\"res\"] = res; undefined"
      val (reply, stderr) = host.query("", queryStr, "res")
      reply match
        case ReplHost.Result(content, intermediate) =>
          val stdout = intermediate.map(_.stripSuffix("undefined").stripSuffix("\n"))
          stdout match
            case None | Some("") =>
            case Some(str) =>
              output(s"// Standard Output:\n${str}")
          output(s"= ${content}")
        case ReplHost.Empty =>
        // case ReplHost.Unexecuted(message) => ???
        case ReplHost.Error(isSyntaxError, message) =>
          import hkmc2.Message.MessageContext
          if (isSyntaxError) then
            // If there is a syntax error in the generated code,
            // it should be a code generation error.
            raise(ErrorReport(msg"[Uncaught SyntaxError] ${message}" -> N :: Nil,
              source = Diagnostic.Source.Compilation))
          else
            // Otherwise, it is considered a simple runtime error.
            raise(ErrorReport(msg"${message}" -> N :: Nil,
              source = Diagnostic.Source.Runtime))
      if stderr.nonEmpty then output(s"// Standard Error:\n${stderr}")
      
      
      



