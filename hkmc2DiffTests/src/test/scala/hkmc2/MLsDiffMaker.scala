package hkmc2

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.semantics.{Elaborator, Resolver, Resolvable, Symbol, SymbolPrinter}

import semantics.Elaborator.{Ctx, State}

abstract class MLsDiffMaker extends DiffMaker:
  
  val invalmlOpt: Command[?]
  
  val rootPath: Str // * Absolute path to the root of the project
  val preludeFile: io.Path // * Contains declarations of JS builtins
  val predefFile: io.Path // * Contains MLscript standard library definitions
  val runtimeFile: io.Path = predefFile.up / "Runtime.mjs" // * Contains MLscript runtime
  val runtimeSourceFile: io.Path = predefFile.up / "Runtime.mls" // * Contains MLscript runtime sources
  val termFile: io.Path = predefFile.up / "Term.mjs" // * Contains MLscript runtime term definitions
  val blockFile: io.Path = predefFile.up / "Block.mjs" // * Contains MLscript runtime block definitions
  // Reflection must use the same option constructors as Block.mls.
  val optionFile: io.Path = predefFile.up / "Option.mjs"
  
  val wd = file.up
  
  val importDot = NullaryCommand(".", () =>
    given Config = mkConfig
    importFile(wd / io.RelPath(".mls"), verbose = false, includeDirectives = true)
  )
  val importUpDot = NullaryCommand("..", () => doImportUp(wd))
  def doImportUp(wd: io.Path) =
    given Config = mkConfig
    importFile(wd.up / io.RelPath(".mls"), verbose = false, includeDirectives = true)
  
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
  val showResl = FlagCommand(false, "sr")
  val showLoweredTree = NullaryCommand("lot")
  val ppLoweredTreeOld = NullaryCommand("slot", () => output("Option ':slot' is deprecated, use ':sir' instead."))
  val showIR = NullaryCommand("sir")
  val showIRLines = NullaryCommand("sirl")
  val checkIR = NullaryCommand("checkIR")
  val showOptimizedIR = NullaryCommand("soir")
  val showOptimizedTree = NullaryCommand("olot")
  val showPipeline = NullaryCommand("showPipeline")
  val showPipelineTree = NullaryCommand("showPipelineTree")
  val debugOptimizations = NullaryCommand("dopt")
  val noOptimizations = NullaryCommand("noOpt")
  val showIRErasedTypes = NullaryCommand("siret", () =>
    if showIR.isUnset && showOptimizedIR.isUnset then
      output("Option ':siret' only has an effect if ':sir' or ':soir' is also set")
  )
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
  val noCheckCasts = NullaryCommand("noCheckCasts")
  val noFreeze = NullaryCommand("noFreeze")
  val noModuleCheck = NullaryCommand("noModuleCheck")
  val aggressive = NullaryCommand("aggressive")
  val noAggressive = NullaryCommand("noAggressive")
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
  val flowBasedOpt = Command("flowBasedOpt")(_.trim)

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
  private val FlowBasedOptKnownFlags =
    Set("debug", "debugEta", "debugDpe", "debugDce", "on", "off", "mono", "poly")
  
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
      language = Config.Language.default,
      baseDir = wd,
      sanityChecks = Opt.when(noSanityCheck.isUnset)(SanityChecks(light = true, checkUnreachable = true)),
      checkCasts = !noCheckCasts.isSet,
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

      qqEnabled = importQQ.isSet,
      funcToCls = funcToCls.isSet,
      commentGeneratedCode = debug.isSet,
      noFreeze = noFreeze.isSet,
      noModuleCheck = noModuleCheck.isSet,
      aggressive = aggressive.isSet && noAggressive.isUnset,
      debug = Config.Debug.default,
      optimizer = Optimizer(
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
        tailRecOpt = !noTailRecOpt.isSet,
        inlining = Opt.when(!noInlineOpt.isSet)(Config.Inliner(inlineThreshold =
          inlineThreshold.get.getOrElse(Config.default.inlineThreshold))),
        deadBranchRemoval = Config.default.deadBranchRemoval,
        deadCodeElim = noOptimizations.isUnset,
        flowBasedOpt =
          if flowBasedOpt.isUnset then S(FlowBasedOpt.default)
          else
            val flags = parseFlags(flowBasedOpt.get)
            reportUnknownFlags(":flowBasedOpt", flags, FlowBasedOptKnownFlags)
            reportExclusiveFlagConflict(":flowBasedOpt", flags, "on", "off")
            reportExclusiveFlagConflict(":flowBasedOpt", flags, "mono", "poly")
            if flags.contains("off") then N
            else S(FlowBasedOpt(FlowAnalysisConfig(
              debug = flags.contains("debug"),
              mono = !flags.contains("poly"),
              trackNonAffine = false,
              trackAccumulator = false,
              logNonAffine = false,
              logAccumulator = false,
              debugEta = flags.contains("debugEta"),
              debugDpe = flags.contains("debugDpe"),
              debugDce = flags.contains("debugDce"),
            ))),
        dataFlowAnalysis = noOptimizations.isUnset,
      ),
      checkInvariants = true,
    )
  
  
  val importCmd = Command("import"): ln =>
    given Config = mkConfig
    importFile(file.up / io.RelPath(ln.trim), verbose = silent.isUnset, includeDirectives = false)
  
  // eg: `:ucs desugared normalized lowered`
  val showUCS = Command("ucs"): ln =>
    ln.split(" ").iterator.map(x => "ucs:" + x.trim).toSet
  
  
  protected lazy val debugContext = new DebugContext:
    override protected def forceUids: Bool = dbgParsing.isSet || dbgResolving.isSet || debug.isSet
  protected lazy val debugOutputHandler = DebugOutputHandler(cctx.fs, str => output(str))

  protected def outputDebugSection(title: Str, contents: Str, out: Config.DebugOutput): Unit = out match
    case Config.DebugOutput.StdIO =>
      outputSeparator(title)
      output(contents)
    case _ => debugOutputHandler.emit(out, s"${title}\n${contents}")

  given Elaborator.State = new Elaborator.State
  
  
  protected lazy val dbgScp: utils.Scope = // for unique symbol debug-printing only
    Scope.empty(Scope.Cfg.default.copy(
      escapeChars = false,
      useSuperscripts = true,
      includeZero = true,
    ))
  
  
  val dbgPrinter: SymbolPrinter = new SymbolPrinter(dbgScp):
    override protected def preProcess(t: Product): Product =
      case class Unexpanded(origin: Resolvable)
      t match
        case t: Resolvable if t.hasExpansion => t.expanded
        case t: Resolvable if dbgResolving.isSet => Unexpanded(t.duplicate.resolve)
        case t => t
    override protected def postProcess(t: Product): Str =
      if showLocations.isSet then
        t match
          case t: Located => t.toLoc.fold(" loc[none]"): loc =>
            val (sl, _, sc) = loc.origin.fph.getLineColAt(loc.spanStart)
            val (el, _, ec) = loc.origin.fph.getLineColAt(loc.spanEnd)
            s" loc[$sl:$sc-$el:$ec]"
          case _ => ""
      else ""
  
  
  protected abstract class DiffTraceLogger(indentWhenDisabled: Bool)
      extends TraceLogger(debugContext, debugOutputHandler, indentWhenDisabled, prefix = "")(using dbgPrinter)

  protected def commandLogger(command: Command[?]): TraceLogger =
    new DiffTraceLogger(indentWhenDisabled = true):
      protected def phaseEnabled(config: Config.Debug): Bool = false
      protected def forceTrace(scope: Opt[Str]): Bool = command.isSet

  val etl = new DiffTraceLogger(indentWhenDisabled = false):
    protected def phaseEnabled(config: Config.Debug): Bool = config.elaboration
    protected def forceTrace(scope: Opt[Str]): Bool =
      dbgElab.isSet || scope.exists(showUCS.get.getOrElse(Set.empty).contains)
  
  val rtl = commandLogger(dbgResolving)
  
  val ftl = commandLogger(dbgFlow)
  
  var curCtx = Elaborator.State.init
  var curICtx = Resolver.ICtx.empty
  
  /** Persistent config modification from `#config(...)` directives. */
  var configModify: Config => Config = identity
  
  var prelude = Elaborator.Ctx.empty
  
  override def run(): Unit =
    if file =/= preludeFile then 
      given Config = mkConfig
      given Raise = d =>
        output(s"Error: $d")
        ()
      val preludeArtifact = cctx.getPrelude(preludeFile)
      curCtx = preludeArtifact.ctx
      prelude = preludeArtifact.ctx
    else
      // The compiler loads the prelude as one compilation unit. Its mutually
      // referring host signatures must see declarations across blank lines here
      // too; worksheet block boundaries are not part of the prelude's semantics.
      consumeEmptyLines.setCurrentValue(())
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
      // The synthetic Predef import bootstraps the host environment; it is not
      // a WASM test block, even when :wasm is enabled at the top of the file.
      given Config = cfg.copy(target = CompilationTarget.JS, optimizer = cfg.optimizer.copy(
        deforest = cfg.deforest.map: d =>
          d.copy(config = d.config.copy(
            debug = false,
            logAccumulator = false,
            logNonAffine = false
          )),
        flowBasedOpt = cfg.flowBasedOpt.map: d =>
          d.copy(config = d.config.copy(
            debug = false,
            logAccumulator = false,
            logNonAffine = false,
            debugEta = false,
            debugDpe = false,
            debugDce = false,
            logEffects = false,
          ))
      ))
      processTrees(
        PrefixApp(Keywrd(`import`), StrLit(predefFile.toString))
        :: Open(Ident("Predef"))
        :: Nil)
    super.init()
  
  
  def importFile(file: io.Path, verbose: Bool, includeDirectives: Bool)(using Config): Unit =
    
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
      case (syntax.IDENT(":..", true), _) :: rest =>
        doImportUp(file.up)
        dropCrap(rest.dropWhile(_._1 isnt syntax.NEWLINE).drop(1))
      case (syntax.IDENT(prefix @ (":" | ":!"), true), _) :: (syntax.IDENT(nme, false), _) :: rest =>
        if includeDirectives then
          val ln = rest.takeWhile(_._1 isnt syntax.NEWLINE)
          def render(ts: Ls[syntax.Stroken -> Loc]): Str = ts match
            case (st, _) :: rest =>
              val str = st match
                case syntax.IDENT(nme, _) => nme
                case syntax.SPACE => " "
                case _ => TODO(st)
              str + render(rest)
            case Nil => ""
          processLines(s"$prefix$nme ${render(ln)}" :: Nil, reprintCommands = false)
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
      val (e, newCtx) = elab.importFrom(resBlk, resBlk.definedSymbols.iterator.map(_._2).toList)
      if file.toString === runtimeSourceFile.toString then
        summon[Elaborator.State].initRuntimeSymbolsFromBlock(e)
      val ctxWithImports = newCtx.withMembers(resBlk.definedSymbols)
      if verbose then
        output(s"Imported ${resBlk.definedSymbols.size} member(s)")
      curCtx = ctxWithImports
      if includeDirectives then extractConfig(e.stats)
      processTerm(e, inImport = true)
    catch
      case err: Throwable =>
        uncaught(err)
  
  given tl: TraceLogger = commandLogger(debug)
  
  
  def processOrigin(origin: Origin)(using Raise): Unit =
    val oldCtx = curCtx
    
    val baseConfig = configModify(mkConfig)
    given Config = baseConfig
    
    val lexer = new syntax.Lexer(origin, dbg = dbgParsing.isSet):
      override protected def doPrintDbg(msg: Str): Unit = output(msg)
    val tokens = lexer.bracketedTokens
    
    if showParse.isSet || dbgParsing.isSet then
      output(syntax.Lexer.printTokens(tokens))
    
    val parser = new syntax.Parser(origin, tokens, syntax.ParseRules(), raise, dbg = dbgParsing.isSet):
      def doPrintDbg(msg: => Str): Unit = if dbg then output(msg)
    val res = parser.parseAll(parser.block(allowNewlines = true))
    val phaseConfig = Config.elaborationConfig(res, file.up)
    debugContext.configure(phaseConfig.debug)
    
    // If parsed tree is displayed, don't show the string serialization.
    if (parseOnly.isSet || showParse.isSet) && !showParsedTree.isSet && !phaseConfig.debug.showParsedTree then
      output(s"Parsed:${res.map("\n\t"+_.showDbg).mkString}")
    
    if showParsedTree.isSet then
      outputSeparator(s"Parsed tree")
      res.foreach(t => output(t.showAsTree))
    else if phaseConfig.debug.showParsedTree then
      outputDebugSection("Parsed tree", res.map(_.showAsTree).mkString("\n"), phaseConfig.debug.out)
    else DebugOutputHandler.showParsedDefinitions(res, phaseConfig, file.up): (tree, out) =>
      outputDebugSection("Parsed tree", tree.showAsTree, out)
    
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
  
  def extractConfig(stats: Ls[semantics.Statement]): Unit =
    // Extract SetConfig statements and update persistent config
    stats.foreach:
      case sc: semantics.SetConfig =>
        val prev = configModify
        configModify = cfg => sc.modify(prev(cfg))
      case _ => ()
  
  def processTrees(trees: Ls[syntax.Tree])(using Config, Raise): Unit =
    val blk = new syntax.Tree.Block(trees)
    val elaborationConfig = Config.elaborationConfig(blk, file.up)
    debugContext.configure(elaborationConfig.debug)
    // val blockSymbol =
    //   semantics.TopLevelSymbol("block#"+blockNum)
    blockNum += 1
    // given Elaborator.Ctx = curCtx.nest(S(blockSymbol))
    given Elaborator.Ctx = curCtx.nestLocal(s"block:${blockNum}")
    // Match the compiler's prelude bootstrap: builtin lookup uses the original
    // declaration symbols, including while those declarations are elaborated.
    if file == preludeFile then prelude = summon[Elaborator.Ctx].withMembers(blk.definedSymbols)
    val elab =
      given Config = elaborationConfig
      Elaborator(etl, file.up, prelude)
    val (e, newCtx) = elaborationConfig.givenIn(elab.topLevel(blk))
    curCtx = newCtx
    
    extractConfig(e.stats)
    
    // If elaborated tree is displayed, don't show the string serialization.
    if (showElab.isSet || debug.isSet) && !showElaboratedTree.isSet && !elaborationConfig.debug.showElaboratedTree then
      output(s"Elab: ${e.showDbg}")
    if showElaboratedTree.isSet then
      outputSeparator(s"Elaborated tree")
      output(e.showAsTree)
    else DebugOutputHandler.showElaboratedTree(e, elaborationConfig)(outputDebugSection)
    DebugOutputHandler.showElaboratedTerm(e, elaborationConfig, output.ColWidth)(outputDebugSection)(using flowScp)
    
    if showResl.isSet then
      import semantics.ShowCfg
      given ShowCfg = ShowCfg(
        showErasedTypes = showIRErasedTypes.isSet,
        showExpansionMappings = true,
        showFlowSymbols = true,
        debug = debug.isSet,
      )
      outputSeparator(s"Resolved")
      output:
        import document.*
        doc" #{ ${e.showTopLevel(using flowScp)} #} ".mkString(output.ColWidth)
    
    processTerm(e, inImport = false)
      
  
  
  def processTerm(trm: semantics.Term.Blk, inImport: Bool)(using Config, Raise): Unit =
    given Ctx = curCtx
    given Config = Config.extractConfigFromStats(trm)
    debugContext.configure(config.debug)
    if file.toString =/= runtimeSourceFile.toString && file.toString =/= preludeFile.toString then
      summon[Elaborator.State].initRuntimeSymbolsFromFile(runtimeSourceFile, prelude)(
        using summon[TL], summon[Raise], cctx)
    if !config.language.useNewResolution then
      val resolver = Resolver(rtl)
      curICtx = resolver.traverseBlock(trm)(using curICtx)
    
    if showResolve.isSet then
      output(s"Resolved: ${trm.showDbg}")
    if showResolvedTree.isSet then
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
          showErasedTypes = showIRErasedTypes.isSet,
          showExpansionMappings = true,
          showFlowSymbols = true,
          debug = debug.isSet,
        )
        outputSeparator(s"Flowed")
        output:
          import document.*
          doc" #{ ${trm.showTopLevel(using flowScp)} #} \nwhere #{ ${floan.showFlows(using flowScp)} #} ".mkString()
    
  
