package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.semantics.{Elaborator, Resolver, Resolvable, Symbol, SymbolPrinter}

import semantics.Elaborator.{Ctx, State}

abstract class MLsDiffMaker extends DiffMaker:
  
  val invalmlOpt: Command[?]
  
  val rootPath: Str // * Absolute path to the root of the project
  val preludeFile: io.Path // * Contains declarations of JS builtins
  val predefFile: io.Path // * Contains MLscript standard library definitions
  val runtimeFile: io.Path = predefFile.up / "Runtime.mjs" // * Contains MLscript runtime definitions
  val termFile: io.Path = predefFile.up / "Term.mjs" // * Contains MLscript runtime term definitions
  val blockFile: io.Path = predefFile.up / "Block.mjs" // * Contains MLscript runtime block definitions
  val optionFile: io.Path = predefFile.up / "Option.mjs" // * Contains MLscipt runtime option definition
  
  val wd = file.up
  
  val silent = NullaryCommand("silent")
  val dbgElab = NullaryCommand("de")
  val dbgParsing = NullaryCommand("dp")
  val dbgResolving = NullaryCommand("dr")
  val dbgFlow = NullaryCommand("df")
  
  val showLocations = NullaryCommand("loc")
  val showParse = NullaryCommand("p")
  val showParsedTree = NullaryCommand("pt")
  val showElab = NullaryCommand("el")
  val showElaboratedTree = NullaryCommand("elt")
  val showResolve = NullaryCommand("r")
  val showResolvedTree = NullaryCommand("rt")
  val showFlows = FlagCommand(false, "sf")
  val showLoweredTree = NullaryCommand("lot")
  val ppLoweredTreeOld = NullaryCommand("slot", () => output("Option ':slot' is deprecated, use ':sir' instead."))
  val showIR = NullaryCommand("sir")
  val checkIR = NullaryCommand("checkIR")
  val showOptimizedIR = NullaryCommand("soir")
  val showOptimizedTree = NullaryCommand("olot")
  val debugOptimizations = NullaryCommand("dopt")
  val noOptimizations = NullaryCommand("noOpt")
  val showContext = NullaryCommand("ctx")
  val parseOnly = NullaryCommand("parseOnly")
  val funcToCls = NullaryCommand("ftc")
  
  val flow = FlagCommand(false, "flow")
  private val flowScp: utils.Scope =
    utils.Scope.empty(utils.Scope.Cfg.default.copy(
      escapeChars = false,
      useSuperscripts = true,
      includeZero = true,
    ))
  
  /**
   * Enables Wasm support. All options in [[WasmDiffMaker]] are no-op if this option is not set.
   */
  val wasm = NullaryCommand("wasm")
  
  
  // * Compiler configuration
  
  val noSanityCheck = NullaryCommand("noSanityCheck")
  val noFreeze = NullaryCommand("noFreeze")
  val noModuleCheck = NullaryCommand("noModuleCheck")
  val effectHandlers = Command("effectHandlers")(_.trim)
  val effectHandlersOptions = Set("debug", "")
  val stackSafe = Command("stackSafe")(_.trim)
  val liftDefns = NullaryCommand("lift")
  val importQQ = NullaryCommand("qq")
  val stageCode = NullaryCommand("staging")
  val rewriteWhile = NullaryCommand("rewriteWhile")
  val noInlineOpt = NullaryCommand("noInline")
  val inlineThreshold = Command("inlineThreshold")(_.trim.toInt)
  val noTailRecOpt = NullaryCommand("noTailRec")
  val deforest = Command("deforest")(_.trim)
  val patMatConsequentSharingThreshold = Command("patMatConsequentSharingThreshold")(_.trim.toInt)
  val deadParamElim = Command("deadParamElim")(_.trim)

  private val DeforestKnownFlags = Set(
    "mono",
    "trackNonAffine",
    "noTrackNonAffine",
    "trackAccumulator",
    "noTrackAccumulator",
    "logNonAffine",
    "noLogNonAffine",
    "logAccumulator",
    "noLogAccumulator",
  )
  private val DeadParamElimKnownFlags = Set("debug", "mono", "poly", "off")
  
  def mkConfig: Config =
    import Config.*
    def parseFlags(raw: Opt[Str]): Set[Str] =
      raw.getOrElse("").split("\\s+").filter(_.nonEmpty).toSet
    def reportUnknownFlags(optionName: Str, flags: Set[Str], knownFlags: Set[Str]): Unit =
      val unknownFlags = flags -- knownFlags
      if unknownFlags.nonEmpty then
        output(s"$errMarker Unknown '$optionName' flags: ${unknownFlags.toList.sorted.mkString(", ")}")
    def reportExclusiveFlagConflict(optionName: Str, flags: Set[Str], positive: Str, negative: Str): Unit =
      if flags.contains(positive) && flags.contains(negative) then
        output(s"$errMarker '$optionName' flags '$positive' and '$negative' conflict")
    def resolveFlag(flags: Set[Str], positive: Str, negative: Str, default: Bool): Bool =
      if flags.contains(positive) then true
      else if flags.contains(negative) then false
      else default

    if stackSafe.isSet && effectHandlers.isUnset then
      output(s"$errMarker Option ':stackSafe' requires ':effectHandlers' to be set")
    if !effectHandlers.get.forall(effectHandlersOptions.contains(_)) then
      output(s"$errMarker Option ':effectHandlers' only supports 'debug' as option")
    if effectHandlers.isSet then
      if liftDefns.isUnset then
        output(s"$errMarker Option ':effectHandlers' requires ':lift'")
    if inlineThreshold.isSet && noInlineOpt.isSet then
      output(s"$errMarker Option ':noInline' conflicts with option ':inlineThreshold'")
    Config(
      baseDir = wd,
      sanityChecks = Opt.when(noSanityCheck.isUnset)(SanityChecks(light = true, checkUnreachable = true)),
      effectHandlers = Opt.when(effectHandlers.isSet)(EffectHandlers(
        debug = effectHandlers.get.contains("debug"),
        stackSafety = stackSafe.get.flatMap:
          case "off" => N
          case value => value.toIntOption match
            case N => S(StackSafety.default)
            case S(value) =>
              if value < 0 then
                failures += 1
                output("/!\\ Stack limit must be positive, but the stack limit here is set to " + value)
                S(StackSafety.default)
              // Minimum: 1 for initial depth, 3 for resuming in the trampoline, 1 for function entry.
              // The limit needs to be strictly greater than 1 + 3 + 1 = 5.
              else if value < 6 then
                failures += 1
                output("/!\\ Stack limit is too low, the minimum supported is 6.")
                S(StackSafety.default)
              else
                S(StackSafety(stackLimit = value))
        ,
      )),
      liftDefns = Opt.when(liftDefns.isSet)(LiftDefns()),
      patMatConsequentSharingThreshold = patMatConsequentSharingThreshold.get
        .orElse(Config.default.patMatConsequentSharingThreshold),
      stageCode = stageCode.isSet,
      target = if wasm.isSet then CompilationTarget.Wasm else CompilationTarget.JS,
      rewriteWhileLoops = rewriteWhile.isSet,
      tailRecOpt = !noTailRecOpt.isSet,
      deforest = Opt.when(deforest.isSet):
        val flags = parseFlags(deforest.get)
        reportUnknownFlags(":deforest", flags, DeforestKnownFlags)
        reportExclusiveFlagConflict(":deforest", flags, "trackNonAffine", "noTrackNonAffine")
        reportExclusiveFlagConflict(":deforest", flags, "trackAccumulator", "noTrackAccumulator")
        reportExclusiveFlagConflict(":deforest", flags, "logNonAffine", "noLogNonAffine")
        reportExclusiveFlagConflict(":deforest", flags, "logAccumulator", "noLogAccumulator")
        Deforest(FlowAnalysisConfig(
          debug = true,
          mono = flags.contains("mono"),
          trackNonAffine = resolveFlag(flags, "trackNonAffine", "noTrackNonAffine", default = true),
          trackAccumulator = resolveFlag(flags, "trackAccumulator", "noTrackAccumulator", default = flags.contains("logAccumulator")),
          logNonAffine = resolveFlag(flags, "logNonAffine", "noLogNonAffine", default = false),
          logAccumulator = resolveFlag(flags, "logAccumulator", "noLogAccumulator", default = false),
        )),
      inlining = Opt.when(!noInlineOpt.isSet)(Config.Inliner(inlineThreshold.get.getOrElse(1))),
      deadBranchRemoval = Config.default.deadBranchRemoval,
      qqEnabled = importQQ.isSet,
      funcToCls = funcToCls.isSet,
      commentGeneratedCode = debug.isSet,
      noFreeze = noFreeze.isSet,
      noModuleCheck = noModuleCheck.isSet,
      deadParamElim =
        if deadParamElim.isUnset then S(DeadParamElim.default)
        else
          val flags = parseFlags(deadParamElim.get)
          reportUnknownFlags(":deadParamElim", flags, DeadParamElimKnownFlags)
          reportExclusiveFlagConflict(":deadParamElim", flags, "mono", "poly")
          if flags.contains("off") && (flags - "off").nonEmpty then
            output(s"$errMarker ':deadParamElim off' conflicts with other flags")
          if flags.contains("off") then N
          else
            S(DeadParamElim(FlowAnalysisConfig(
              debug = flags.contains("debug"),
              mono = !flags.contains("poly"),
              trackNonAffine = false,
              trackAccumulator = false,
              logNonAffine = false,
              logAccumulator = false,
            ))),
    )
  
  
  val importCmd = Command("import"): ln =>
    given Config = mkConfig
    importFile(file.up / io.RelPath(ln.trim), verbose = silent.isUnset)
  
  // eg: `:ucs desugared normalized lowered`
  val showUCS = Command("ucs"): ln =>
    ln.split(" ").iterator.map(x => "ucs:" + x.trim).toSet
  
  
  given Elaborator.State = new Elaborator.State:
    override def dbg: Bool =
      dbgParsing.isSet
      || dbgElab.isSet
      || dbgResolving.isSet
      || debug.isSet
  
  
  protected lazy val dbgScp: utils.Scope = // for unique symbol debug-printing only
    Scope.empty(Scope.Cfg.default.copy(
      escapeChars = false,
      useSuperscripts = true,
      includeZero = true,
    ))
  
  
  val dbgPrinter: SymbolPrinter = new SymbolPrinter(dbgScp):
    override def preProcess(t: Product): Product = super.preProcess:
      case class Unexpanded(origin: Resolvable)
      t match
      case t: Resolvable if t.hasExpansion => t.expanded
      case t: Resolvable if dbgResolving.isSet => Unexpanded(t.duplicate.resolve)
      case t => t
    override def postProcess(t: Product): Str =
      super.postProcess(t) + (
        if showLocations.isSet then
          t match
          case t: Located => t.toLoc.fold(" loc[none]"): loc =>
            val (sl, _, sc) = loc.origin.fph.getLineColAt(loc.spanStart)
            val (el, _, ec) = loc.origin.fph.getLineColAt(loc.spanEnd)
            s" loc[$sl:$sc-$el:$ec]"
        else ""
      )
  
  
  val etl = new TraceLogger:
    override def doTrace = dbgElab.isSet || scope.exists:
      showUCS.get.getOrElse(Set.empty).contains
    override def emitDbg(str: String): Unit = output(str)
    override def trace[T](pre: => Str, post: T => Str = noPostTrace)(thunk: => T): T =
      // * This override is for avoiding to increase the indentation when tracing if doTrace is false,
      // * so that selectively-enabled tracing doesn't get strange indentation.
      // * Perhaps this should be the default behavior of TraceLogger.
      if doTrace then super.trace(pre, post)(thunk)
      else thunk
  
  val rtl = new TraceLogger:
    override def doTrace = dbgResolving.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  val ftl = new TraceLogger:
    override def doTrace = dbgFlow.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  var curCtx = Elaborator.State.init
  var curICtx = Resolver.ICtx.empty
  
  /** Persistent config modification from `#config(...)` directives. */
  var configModify: Config => Config = identity
  
  var prelude = Elaborator.Ctx.empty
  
  override def run(): Unit =
    if file =/= preludeFile then 
      given Config = mkConfig
      importFile(preludeFile, verbose = false)
      prelude = curCtx
    super.run()
  
  
  override def init(): Unit =
    import syntax.*
    import Tree.*
    import Keyword.*
    given raise: Raise = d =>
      output(s"Error: $d")
      ()
    if file != preludeFile then
      val cfg = mkConfig
      given Config = cfg.copy(
        deforest = cfg.deforest.map: d =>
          d.copy(config = d.config.copy(
            debug = false,
            logAccumulator = false,
            logNonAffine = false
          )),
        deadParamElim = cfg.deadParamElim.map: d =>
          d.copy(config = d.config.copy(
            debug = false,
            logAccumulator = false,
            logNonAffine = false
          ))
      )
      processTrees(
        PrefixApp(Keywrd(`import`), StrLit(predefFile.toString))
        :: Open(Ident("Predef"))
        :: Nil)
    super.init()
  
  
  def importFile(file: io.Path, verbose: Bool)(using Config): Unit =
    
    // val raise: Raise = throw _
    given raise: Raise = d =>
      output(s"Error: $d")
      ()
    
    val block = cctx.fs.read(file)
    val fph = new FastParseHelpers(block)
    val origin = Origin(file, 0, fph)
    
    val lexer = new syntax.Lexer(origin, dbg = dbgParsing.isSet)
    
    // Stupid hack to ignore diff-test directives like `:ignore`
    def dropCrap(ts: Ls[syntax.Stroken -> Loc]): Ls[syntax.Stroken -> Loc] = ts match
      case (syntax.IDENT(":", true), _) :: (syntax.IDENT(nme, false), _) :: rest =>
        dropCrap(rest.dropWhile(_._1 isnt syntax.NEWLINE).drop(1))
      case _ => ts
    
    val tokens = dropCrap(lexer.bracketedTokens)
    
    if showParse.isSet || dbgParsing.isSet then
      output(syntax.Lexer.printTokens(tokens))
    
    val rules = syntax.ParseRules()
    val p = new syntax.Parser(origin, tokens, rules, raise, dbg = dbgParsing.isSet):
      def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
    val res = p.parseAll(p.block(allowNewlines = true))
    val imprtSymbol =
      semantics.TopLevelSymbol("import#"+file.baseName)
    given Elaborator.Ctx = curCtx.nestLocal("import:"+file.baseName)
    val elab = Elaborator(etl, wd, Ctx.empty)
    try
      val resBlk = new syntax.Tree.Block(res)
      val (e, newCtx) = elab.importFrom(resBlk)
      val ctxWithImports = newCtx.withMembers(resBlk.definedSymbols)
      if verbose then
        output(s"Imported ${resBlk.definedSymbols.size} member(s)")
      curCtx = ctxWithImports
      processTerm(e, inImport = true)
    catch
      case err: Throwable =>
        uncaught(err)
  
  given tl: TraceLogger with
    override def doTrace = debug.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  
  def processOrigin(origin: Origin)(using Raise): Unit =
    val oldCtx = curCtx
    
    given Config = configModify(mkConfig)
    
    val lexer = new syntax.Lexer(origin, dbg = dbgParsing.isSet)
    val tokens = lexer.bracketedTokens
    
    if showParse.isSet || dbgParsing.isSet then
      output(syntax.Lexer.printTokens(tokens))
    
    val rules = syntax.ParseRules()
    val p = new syntax.Parser(origin, tokens, rules, raise, dbg = dbgParsing.isSet):
      def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
    val res = p.parseAll(p.block(allowNewlines = true))
    
    // If parsed tree is displayed, don't show the string serialization.
    if (parseOnly.isSet || showParse.isSet) && !showParsedTree.isSet then
      output(s"Parsed:${res.map("\n\t"+_.showDbg).mkString}")
    
    if showParsedTree.isSet then
      outputSeparator(s"Parsed tree")
      res.foreach(t => output(t.showAsTree))
    
    // if showParse.isSet then
    //   output(s"AST: $res")
    
    if parseOnly.isUnset then
      processTrees(res)(using summon, raise)
    
    if showContext.isSet then
      output("Env:")
      curCtx.env.foreach: (k, v) =>
        if !(oldCtx.env contains k) then
          output(s"  $k -> $v")
  
  
  private var blockNum = 0
  
  def processTrees(trees: Ls[syntax.Tree])(using Config, Raise): Unit =
    val elab = Elaborator(etl, file.up, prelude)
    // val blockSymbol =
    //   semantics.TopLevelSymbol("block#"+blockNum)
    blockNum += 1
    // given Elaborator.Ctx = curCtx.nest(S(blockSymbol))
    given Elaborator.Ctx = curCtx.nestLocal(s"block:${blockNum}")
    val blk = new syntax.Tree.Block(trees)
    val (e, newCtx) = elab.topLevel(blk)
    curCtx = newCtx
    
    // Extract SetConfig statements and update persistent config
    e.stats.foreach:
      case sc: semantics.SetConfig =>
        val prev = configModify
        configModify = cfg => sc.modify(prev(cfg))
      case _ => ()
    
    // If elaborated tree is displayed, don't show the string serialization.
    if (showElab.isSet || debug.isSet) && !showElaboratedTree.isSet then
      output(s"Elab: ${e.showDbg}")
    showElaboratedTree.get.foreach: post =>
      outputSeparator(s"Elaborated tree")
      output(e.showAsTree)
    
    processTerm(e, inImport = false)
      
  
  
  def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    given Ctx = curCtx
    given Config = Config.extractConfigFromStats(trm)
    val resolver = Resolver(rtl)
    curICtx = resolver.traverseBlock(trm)(using curICtx)
    
    if showResolve.isSet then
      output(s"Resolved: ${trm.showDbg}")
    showResolvedTree.get.foreach: post =>
      outputSeparator(s"Resolved tree")
      output(trm.showAsTree)
    
    if flow.isSet then
      val floan = semantics.flow.FlowAnalysis(using ftl)
      val flo = floan.typeProd(trm)
      floan.solveConstraints()
      floan.expandTerms()
      if showFlows.isSet then
        import semantics.ShowCfg
        given ShowCfg = ShowCfg(
          showExpansionMappings = true,
          showFlowSymbols = true,
          debug = debug.isSet,
        )
        outputSeparator(s"Flowed")
        output:
          import document.*
          doc" #{ ${trm.showTopLevel(using flowScp)} #} \nwhere #{ ${floan.showFlows(using flowScp)} #} ".mkString()
    
  

