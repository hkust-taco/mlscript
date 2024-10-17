package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*


abstract class JSBackendDiffMaker extends MLsDiffMaker:
  
  val js = NullaryCommand("js")
  val sjs = NullaryCommand("sjs")
  val showRepl = NullaryCommand("showRepl")
  
  given codegen.js.Scope = codegen.js.Scope.empty
  
  val replTL = new TraceLogger:
    override def doTrace = showRepl.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  lazy val host =
    hostCreated = true
    given TL = replTL
    val h = ReplHost()
    h.execute("let res")
    h
  
  private var hostCreated = false
  override def run(): Unit =
    try super.run() finally if hostCreated then host.terminate()
  
  override def processTerm(blk: semantics.Term.Blk, inImport: Bool)(using Raise): Unit =
    super.processTerm(blk, inImport)
    if js.isSet then
      val low = codegen.Lowering()
      val jsb = codegen.js.JSBuilder()
      import semantics.*
      import codegen.*
      val le = low.topLevel(blk)
      if showLoweredTree.isSet then
        output(s"Lowered:")
        output(le.showAsTree)
      val je = jsb.block(le)
      val jsStr = je.stripBreaks.mkString(100)
      if sjs.isSet then
        output(s"JS:")
        output(jsStr)
      def mkQuery(prefix: Str, jsStr: Str) =
        val queryStr = jsStr.replaceAll("\n", " ")
        val (reply, stderr) = host.query(queryStr)
        reply match
          case ReplHost.Result(content, stdout) =>
            stdout match
              case None | Some("") =>
              case Some(str) =>
                str.splitSane('\n').foreach: line =>
                  output(s"> ${line}")
            content match
            case "undefined" =>
            case _ => output(s"$prefix= ${content}")
          case ReplHost.Empty =>
          case ReplHost.Unexecuted(message) => ???
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
      
      mkQuery("", jsStr)
      
      curCtx.locals.foreach: (nme, sym) =>
        val le = codegen.Return(codegen.Value.Ref(sym), implct = true)
        val je = jsb.block(le)
        val jsStr = je.stripBreaks.mkString(100)
        mkQuery(s"$nme ", jsStr)
      
      
      
      



