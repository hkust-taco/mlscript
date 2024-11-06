package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*


abstract class JSBackendDiffMaker extends MLsDiffMaker:
  
  val debugLowering = NullaryCommand("dl")
  val js = NullaryCommand("js")
  val sjs = NullaryCommand("sjs")
  val showRepl = NullaryCommand("showRepl")
  val silent = NullaryCommand("silent")
  
  private val baseScp: codegen.js.Scope =
    codegen.js.Scope.empty
  
  val ltl = new TraceLogger:
    override def doTrace = debugLowering.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  val replTL = new TraceLogger:
    override def doTrace = showRepl.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  lazy val host =
    hostCreated = true
    given TL = replTL
    val h = ReplHost()
    h
  
  private var hostCreated = false
  override def run(): Unit =
    try super.run() finally if hostCreated then host.terminate()
  
  override def processTerm(blk: semantics.Term.Blk, inImport: Bool)(using Raise): Unit =
    super.processTerm(blk, inImport)
    if js.isSet then
      val low = ltl.givenIn:
        codegen.Lowering()
      val jsb = codegen.js.JSBuilder()
      import semantics.*
      import codegen.*
      val le = low.program(blk)
      if showLoweredTree.isSet then
        output(s"Lowered:")
        output(le.showAsTree)
      
      // * Note that the codegen scope is not in sync with curCtx in terms of its `this` symbol.
      // * We do not nest TopLevelSymbol in codegen `Scope`s
      // * to avoid needlessly generating new variable names in separate blocks.
      val nestedScp = baseScp.nest
      // val nestedScp = codegen.js.Scope(S(baseScp), curCtx.outer, collection.mutable.Map.empty) // * not needed
      
      val je = nestedScp.givenIn:
        jsb.program(le, N)
      val jsStr = je.stripBreaks.mkString(100)
      if sjs.isSet then
        output(s"JS:")
        output(jsStr)
      def mkQuery(prefix: Str, jsStr: Str) =
        val queryStr = jsStr.replaceAll("\n", " ")
        val (reply, stderr) = host.query(queryStr, expectRuntimeErrors.isUnset && fixme.isUnset && todo.isUnset)
        reply match
          case ReplHost.Result(content, stdout) =>
            if silent.isUnset then
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
      
      val definedValues = (curCtx.locals ++ curCtx.members).iterator.collect:
        case (nme, sym: TermSymbol) if sym.k.isInstanceOf[syntax.ValLike] => (nme, sym)
      
      definedValues.toSeq.sortBy(_._2.uid).foreach: (nme, sym) =>
        val le = codegen.Return(codegen.Value.Ref(sym), implct = true)
        val je = nestedScp.givenIn:
          jsb.block(le)
        val jsStr = je.stripBreaks.mkString(100)
        mkQuery(s"$nme ", jsStr)
      
      

