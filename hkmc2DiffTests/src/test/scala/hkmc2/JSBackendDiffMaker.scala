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
  val noCodeGen = NullaryCommand("noCodeGen")
  val js = NullaryCommand("js")
  val showSanitizedJS = NullaryCommand("ssjs")
  val showJS = NullaryCommand("sjs")
  val showRepl = NullaryCommand("showRepl")
  val traceJS = NullaryCommand("traceJS")
  val expect = Command("expect"): ln =>
    ln.trim
  
  private val baseScp: utils.Scope =
    utils.Scope.empty(utils.Scope.Cfg.default)
  private lazy val irPrintingScp: utils.Scope = // for IR printing only
    Scope.empty(Scope.Cfg.default.copy(
      escapeChars = false,
      useSuperscripts = false,
      includeZero = false,
    ))
  
  val runtimeNme = baseScp.allocateName(Elaborator.State.runtimeSymbol)(using throw _)
  val termNme = baseScp.allocateName(Elaborator.State.termSymbol)(using throw _)
  val blockNme = baseScp.allocateName(Elaborator.State.blockSymbol)(using throw _)
  val optionNme = baseScp.allocateName(Elaborator.State.optionSymbol)(using throw _)
  val definitionMetadataNme = baseScp.allocateName(Elaborator.State.definitionMetadataSymbol)(using throw _)
  val prettyPrintNme = baseScp.allocateName(Elaborator.State.prettyPrintSymbol)(using throw _)
  
  val ltl = new TraceLogger:
    override def doTrace = debugLowering.isSet || scope.exists:
      showUCS.get.getOrElse(Set.empty).contains
    override def emitDbg(str: String): Unit = output(str)
  
  val dtl = new TraceLogger:
    override def doTrace = debugOptimizations.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  val replTL = new TraceLogger:
    override def doTrace = showRepl.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  lazy val host =
    hostCreated = true
    given TL = replTL
    val h = ReplHost(rootPath)
    def importRuntimeModule(name: Str, file: io.Path) =
      h.execute(s"const $name = (await import(\"${file}\")).default;") match
      case ReplHost.Result(msg) =>
        if msg.startsWith("Uncaught") then output(s"Failed to load $name: $msg")
      case r => output(s"Failed to load $name: $r")
    importRuntimeModule(runtimeNme, runtimeFile)
    h.execute(s"const $definitionMetadataNme = Symbol.for(\"mlscript.definitionMetadata\");")
    h.execute(s"const $prettyPrintNme = Symbol.for(\"mlscript.prettyPrint\");")
    if importQQ.isSet then importRuntimeModule(termNme, termFile)
    if stageCode.isSet then
      importRuntimeModule(blockNme, blockFile)
      importRuntimeModule(optionNme, optionFile)
    h
  
  private var hostCreated = false
  override def run(): Unit =
    try super.run() finally if hostCreated then host.terminate()
  
  override def processTerm(blk: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    super.processTerm(blk, inImport)
    
    val outerRaise: Raise = summon
    val reportedMessages = mutable.Set.empty[Str]
    
    val importAliases = blk.stats.collect:
        case Import(sym = sym: VarSymbol) => sym
      .toSet
    
    def definedValues(includeNonTerms: Bool): Ls[(Str, BoundSymbol, N)] =
      import Elaborator.Ctx.*
      curCtx.env.iterator.flatMap:
        case (nme, e @ (_: RefElem | SelElem(base = RefElem(_: InnerSymbol)))) =>
          e.symbol match
          case S(ts: TermSymbol) if ts.k.isInstanceOf[syntax.ValLike] => S((nme, ts, N))
          case S(ts: BlockMemberSymbol)
            if includeNonTerms
            || ts.trmImplTree.exists(t => t.k.isInstanceOf[syntax.ValLike] && (t.k isnt syntax.Ins))
          => S((nme, ts, N))
          case S(vs: VarSymbol) if !importAliases(vs) => S((nme, vs, N))
          case _ => N
        case _ => N
      .toList
    
    val symbolsToPreserve = definedValues(includeNonTerms = true).iterator.map(_._2).toSet
    
    lazy val blockPrinter =
      given ShowCfg = ShowCfg(
        showExpansionMappings = false,
        showFlowSymbols = true,
        debug = debug.isSet,
      )
      Printer()
    val print = (p: codegen.Program) =>
      blockPrinter.worksheet(p)(using irPrintingScp).mkString(output.ColWidth)
    
    Config.extractConfigFromStats(blk).givenIn {
    
    if showJS.isSet then config.copy(sanityChecks = N).givenIn:
      given Raise =
        case d @ ErrorReport(source = Source.Compilation) =>
          reportedMessages += d.mainMsg
          outerRaise(d)
        case d => outerRaise(d)
      given Elaborator.Ctx = curCtx
      val low = ltl.givenIn:
        codegen.Lowering()
      val jsb = ltl.givenIn:
        new JSBuilder
      var lowered = low.program(blk)
      if noOptimizations.isUnset then
        lowered = BlockSimplifier(symbolsToPreserve, dtl, print)(lowered)
        ltl.givenIn:
          lowered = DeadParamElim(lowered)
      val nestedScp = baseScp.nest
      val je = nestedScp.givenIn:
        jsb.programBody(lowered, N, wd)
      val jsStr = je.stripBreaks.mkString(output.ColWidth)
      outputSeparator("JS (unsanitized)")
      output(jsStr)
    
    if noCodeGen.isUnset then
      given Elaborator.Ctx = curCtx
      given Raise =
        case e: ErrorReport if reportedMessages.contains(e.mainMsg) =>
          if verbose.isSet then
            output(s"Skipping already reported diagnostic: ${e.mainMsg}")
        case d => outerRaise(d)
      val low = ltl.givenIn:
        new codegen.Lowering()
          with codegen.LoweringSelSanityChecks
          with codegen.LoweringTraceLog(traceJS.isSet)
      
      var lowered = low.program(blk)
      var optimized = lowered
      
      if showLoweredTree.isSet then
        outputSeparator("Lowered IR Tree")
        output(optimized.showAsTree)
      
      if showIR.isSet || showIRLines.isSet then
        given ShowCfg = ShowCfg(
          showExpansionMappings = false,
          showFlowSymbols = true,
          debug = debug.isSet,
        )
        val irStr = Printer().worksheet(optimized)(using irPrintingScp).mkString(output.ColWidth)
        val sloc = irStr.count(_ == '\n') + 1
        if showIRLines.isSet then output(s"Lines of IR: ${sloc}")
        if showIR.isSet then
          outputSeparator("Lowered IR")
          output(irStr)
      
      if noOptimizations.isUnset then
        optimized = WorkerWrapper(symbolsToPreserve, dtl, print)(optimized)
        
        optimized = BlockSimplifier(symbolsToPreserve, dtl, print)(optimized)
        ltl.givenIn:
          optimized = DeadParamElim(optimized)
      
      // TODO: Test that transformers retain object identity when there are no changes
      if (optimized isnt lowered) && (optimized === lowered) then
        output("/!\\ Warning: object identity between equal objects was not preserved by BlockSimplifier or DeadParamElim")
        def rec(lhs: Block, rhs: Block): Bool =
          (lhs is rhs) || {
            if
              lhs.subBlocks.iterator.zip(rhs.subBlocks.iterator).forall:
                case (s1: Block, s2: Block) => rec(s1, s2)
            then
              output(s"/!\\ Offending subblock: ${lhs.showAsTree}") 
              false
            else false
          }
        rec(optimized.main, lowered.main)
      if checkIR.isSet then
        BlockChecker().applyProgram(optimized)
      
      if showOptimizedIR.isSet then
        outputSeparator("Optimized IR")
        given ShowCfg = ShowCfg(
          showExpansionMappings = false,
          showFlowSymbols = true,
          debug = debug.isSet,
        )
        output(Printer().worksheet(optimized)(using irPrintingScp).mkString(output.ColWidth))
      if showOptimizedTree.isSet then
        outputSeparator("Optimized IR Tree")
        output(optimized.showAsTree)
      
      processIRBlock(optimized, definedValues, symbolsToPreserve)
      
      }
  end processTerm
  
  type ComputeDefinedValues = (includeNonTerms: Bool) => Ls[(Str, ValueSymbol, Opt[Str])]
  
  def processIRBlock
        (pgrm: Program, definedValues: ComputeDefinedValues, symbolsToPreserve: Set[BoundSymbol])
        (using Config, Raise, Elaborator.Ctx): Unit =
    
    if js.isSet then
      
      // * We used to do this to avoid needlessly generating new variable names in separate blocks:
      // val nestedScp = baseScp.nest
      val nestedScp = baseScp
      // val nestedScp = codegen.js.Scope(S(baseScp), curCtx.outer, collection.mutable.Map.empty) // * not needed
      
      val resSym = new TempSymbol(N, "block$res")
      
      val resNme = nestedScp.allocateName(resSym)
      
      val loweredMapped = pgrm.copy(main = pgrm.main.mapReturn:
        case Return(res) =>
          Assign(resSym, res, End())
      )
      val jsb = ltl.givenIn:
        new JSBuilder
          with JSBuilderArgNumSanityChecks
      val (pre, js) = nestedScp.givenIn:
        jsb.worksheet(loweredMapped)
      val preStr = pre.stripBreaks.mkString(output.ColWidth)
      val jsStr = js.stripBreaks.mkString(output.ColWidth)
      if showSanitizedJS.isSet then
        outputSeparator("JS (sanitized)")
        if preStr.nonEmpty then output(preStr)
        output(jsStr)
      
      if printedSeparatedSection then outputSeparator("Output")
      
      def mkQuery(preStr: Str, jsStr: Str)(k: Str => Unit) =
        val queryStr = jsStr.replaceAll("\n", " ")
        val (reply, stderr) =
          host.query(preStr, queryStr, !expectRuntimeOrCodeGenErrors && !tolerateErrors)
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
          s"$runtimeNme.TraceLogger.enabled = true; " +
          s"$runtimeNme.TraceLogger.resetIndent(0)")
      
      // * Sometimes the JS block won't execute due to a syntax or runtime error so we always set this first
      host.execute(s"$resNme = undefined")
      
      mkQuery(preStr, jsStr): stdout =>
        stdout.splitSane('\n').init // should always ends with "undefined" (TODO: check)
          .foreach: line =>
            output(s"> ${line}")
      if traceJS.isSet then
        host.execute(s"$runtimeNme.TraceLogger.enabled = false")
      
      if silent.isUnset then
        val valuesToPrint = ("", resSym, expect.get) +: definedValues(includeNonTerms = false).toSeq.sortBy(_._1)
        valuesToPrint.foreach: (nme, sym, expect) =>
          val le =
            import codegen.*
            Assign(
              Elaborator.State.noSymbol,
              Call(
                Elaborator.State.runtimeSymbol.asSimpleRef.selSN("printRaw"),
                (Arg(N, sym.asPath) :: Nil) ne_:: Nil)(true, false, false),
              End())
          val je = nestedScp.givenIn:
            jsb.block(le, endSemi = false)
          val jsStr = je.stripBreaks.mkString(output.ColWidth)
          mkQuery("", jsStr): out =>
            // Omit the last line which is always "undefined" or the unit.
            val result = out.lastIndexOf('\n') match
              case n if n >= 0 => out.substring(0, n)
              case _ => ""
            expect match
            case S(expected) if result =/= expected => raise:
              ErrorReport(msg"Expected: '${expected}', got: '${result}'" -> N :: Nil,
                source = Diagnostic.Source.Runtime)
            case _ => ()
            val anon = nme.isEmpty
            result match
            case "undefined" if anon =>
            case "()" if anon =>
            case _ => output(s"${if anon then "" else s"$nme "}= $result")
      
