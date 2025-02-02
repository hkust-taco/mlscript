package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import semantics.*
import codegen.*
import codegen.js.{JSBuilder, JSBuilderArgNumSanityChecks}
import document.*
import codegen.Block
import utils.Scope
import hkmc2.syntax.Tree.Ident
import hkmc2.codegen.Path
import hkmc2.Diagnostic.Source
import hkmc2.Message.MessageContext

abstract class JSBackendDiffMaker extends MLsDiffMaker:
  
  val debugLowering = NullaryCommand("dl")
  val js = NullaryCommand("js")
  val showSanitizedJS = NullaryCommand("ssjs")
  val showJS = NullaryCommand("sjs")
  val showRepl = NullaryCommand("showRepl")
  val noSanityCheck = NullaryCommand("noSanityCheck")
  val traceJS = NullaryCommand("traceJS")
  val handler = NullaryCommand("handler")
  val expect = Command("expect"): ln =>
    ln.trim
  val stackSafe = Command("stackSafe"): ln =>
    ln.trim
  
  private val baseScp: utils.Scope =
    utils.Scope.empty
  
  val ltl = new TraceLogger:
    override def doTrace = debugLowering.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  val replTL = new TraceLogger:
    override def doTrace = showRepl.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  lazy val host =
    hostCreated = true
    given TL = replTL
    val h = ReplHost(rootPath)
    h
  
  private var hostCreated = false
  override def run(): Unit =
    try super.run() finally if hostCreated then host.terminate()

  private val DEFAULT_STACK_LIMT = 500
  
  override def processTerm(blk: semantics.Term.Blk, inImport: Bool)(using Raise): Unit =
    super.processTerm(blk, inImport)
    val outerRaise: Raise = summon
    val reportedMessages = mutable.Set.empty[Str]
    val stackLimit = stackSafe.get match
      case None => None
      case Some("off") => None
      case Some(value) => value.toIntOption match
        case None => Some(DEFAULT_STACK_LIMT)
        case Some(value) =>
          if value < 0 then
            failures += 1
            output("/!\\ Stack limit must be positive, but the stack limit here is set to " + value)
            Some(DEFAULT_STACK_LIMT)
          else
            Some(value)
    if showJS.isSet then
      given Raise =
        case d @ ErrorReport(source = Source.Compilation) =>
          reportedMessages += d.mainMsg
          outerRaise(d)
        case d => outerRaise(d)
      given Elaborator.Ctx = curCtx
      val low = ltl.givenIn:
        new codegen.Lowering(lowerHandlers = handler.isSet, stackLimit = stackLimit)
          with codegen.LoweringSelSanityChecks(instrument = false)
          with codegen.LoweringTraceLog(instrument = false)
      val jsb = ltl.givenIn:
        new JSBuilder
          with JSBuilderArgNumSanityChecks(instrument = false)
      val le = low.program(blk)
      val nestedScp = baseScp.nest
      val je = nestedScp.givenIn:
        jsb.program(le, N, wd)
      val jsStr = je.stripBreaks.mkString(100)
      output(s"JS (unsanitized):")
      output(jsStr)
    if js.isSet then
      given Elaborator.Ctx = curCtx
      given Raise =
        case e: ErrorReport if reportedMessages.contains(e.mainMsg) =>
          if verbose.isSet then
            output(s"Skipping already reported diagnostic: ${e.mainMsg}")
        case d => outerRaise(d)
      val low = ltl.givenIn:
        new codegen.Lowering(lowerHandlers = handler.isSet, stackLimit = stackLimit)
          with codegen.LoweringSelSanityChecks(noSanityCheck.isUnset)
          with codegen.LoweringTraceLog(traceJS.isSet)
      val jsb = ltl.givenIn:
          new JSBuilder
            with JSBuilderArgNumSanityChecks(noSanityCheck.isUnset)
      val resSym = new TempSymbol(S(blk), "block$res")
      val lowered0 = low.program(blk)
      val le = lowered0.copy(main = lowered0.main.mapTail:
        case e: End =>
          Assign(resSym, Value.Lit(syntax.Tree.UnitLit(false)), e)
        case Return(res, implct) =>
          assert(implct)
          Assign(resSym, res, Return(Value.Lit(syntax.Tree.UnitLit(false)), true))
        case _: HandleBlockReturn => ???
        case tl: (Throw | Break | Continue) => tl
      )
      if showLoweredTree.isSet then
        output(s"Lowered:")
        output(le.showAsTree)
      
      // * We used to do this to avoid needlessly generating new variable names in separate blocks:
      // val nestedScp = baseScp.nest
      val nestedScp = baseScp
      // val nestedScp = codegen.js.Scope(S(baseScp), curCtx.outer, collection.mutable.Map.empty) // * not needed
      
      val resNme = nestedScp.allocateName(resSym)
      
      if ppLoweredTree.isSet then
        output(s"Pretty Lowered:")
        output(Printer.mkDocument(le)(using summon[Raise], nestedScp).toString)
      
      val (pre, js) = nestedScp.givenIn:
        jsb.worksheet(le)
      val preStr = pre.stripBreaks.mkString(100)
      val jsStr = js.stripBreaks.mkString(100)
      if showSanitizedJS.isSet then
        output(s"JS:")
        output(jsStr)
      def mkQuery(preStr: Str, jsStr: Str)(k: Str => Unit) =
        val queryStr = jsStr.replaceAll("\n", " ")
        val (reply, stderr) = host.query(preStr, queryStr, !expectRuntimeOrCodeGenErrors && fixme.isUnset && todo.isUnset)
        reply match
          case ReplHost.Result(content) => k(content)
          case ReplHost.Empty =>
          case ReplHost.Unexecuted(message) => ???
          case ReplHost.Error(isSyntaxError, message, otherOutputs) =>
            if otherOutputs.nonEmpty then
              otherOutputs.splitSane('\n').foreach: line =>
                output(s"> ${line}")
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
      
      if traceJS.isSet then
        host.execute(
          "globalThis.Predef.TraceLogger.enabled = true; " +
          "globalThis.Predef.TraceLogger.resetIndent(0)")
      
      // * Sometimes the JS block won't execute due to a syntax or runtime error so we always set this first
      host.execute(s"$resNme = undefined")
      
      mkQuery(preStr, jsStr): stdout =>
        stdout.splitSane('\n').init // should always ends with "undefined" (TODO: check)
          .foreach: line =>
            output(s"> ${line}")
      if traceJS.isSet then
        host.execute("globalThis.Predef.TraceLogger.enabled = false")
      
      if silent.isUnset then 
        import Elaborator.Ctx.*
        def definedValues = curCtx.env.iterator.flatMap:
          case (nme, e @ (_: RefElem | SelElem(RefElem(_: InnerSymbol), _, _))) =>
            e.symbol match
            case S(ts: TermSymbol) if ts.k.isInstanceOf[syntax.ValLike] => S((nme, ts, N))
            case S(ts: BlockMemberSymbol)
              if ts.trmImplTree.exists(_.k.isInstanceOf[syntax.ValLike]) => S((nme, ts, N))
            case S(vs: VarSymbol) => S((nme, vs, N))
            case _ => N
          case _ => N
        val valuesToPrint = ("", resSym, expect.get) +: definedValues.toSeq.sortBy(_._1)
        valuesToPrint.foreach: (nme, sym, expect) =>
          val le =
            import codegen.*
            Return(
              Call(
                Value.Ref(Elaborator.State.globalThisSymbol).selSN("Predef").selSN("printRaw"),
                Arg(false, Value.Ref(sym)) :: Nil)(true, false),
            implct = true)
          val je = nestedScp.givenIn:
            jsb.block(le)
          val jsStr = je.stripBreaks.mkString(100)
          mkQuery("", jsStr): out =>
            val result = out.splitSane('\n').init.mkString // should always ends with "undefined" (TODO: check)
            expect match
            case S(expected) if result =/= expected => raise:
              ErrorReport(msg"Expected: '${expected}', got: '${result}'" -> N :: Nil,
                source = Diagnostic.Source.Runtime)
            case _ => ()
            result match
            case "undefined" =>
            case "null" =>
            case _ =>
              output(s"${if nme.isEmpty then "" else s"$nme "}= ${result.indentNewLines("| ")}")
      

