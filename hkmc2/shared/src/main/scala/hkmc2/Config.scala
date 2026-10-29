package hkmc2

import hkmc2.utils.*, shorthands.*
import utils.*

import Config.*
import Message.MessageContext


/** The compilation target of a program. */
enum CompilationTarget:
  case JS
  case Wasm


def config(using Config): Config = summon

type Cfg[A] = Config ?=> A

case class Config(
  baseDir: io.Path,
  language: Language,
  sanityChecks: Opt[SanityChecks],
  checkCasts: Bool,
  effectHandlers: Opt[EffectHandlers],
  liftDefns: Opt[LiftDefns],
  patMatConsequentSharingThreshold: Opt[Int],
  stageCode: Bool,
  target: CompilationTarget,
  rewriteWhileLoops: Bool,
  qqEnabled: Bool,
  funcToCls: Bool,
  commentGeneratedCode: Bool,
  noFreeze: Bool,
  noModuleCheck: Bool,
  aggressive: Bool,
  debug: Debug,
  optimizer: Optimizer,
  // Check internal invariants whose checks are too costly to always run, such as MemberStorage.privateOwner's.
  checkInvariants: Bool,
):
  
  def stackSafety: Opt[StackSafety] = effectHandlers.flatMap(_.stackSafety)

  def checkInstantiateEffect: Bool = effectHandlers.exists(_.checkInstantiateEffect)
  
  // NOTE: Historically, we force the rewriting of while loops to functions when
  // handler lowering is on to prevent the "floating out" of definitions done by
  // handler lowering, which currently does not respect scopes introduced by
  // `Scoped` blocks. Currently, handler lowering relies on lifting instead which
  // will lift inner definitions out safely. As such, we no longer require this
  // rewrite.
  // see https://github.com/hkust-taco/mlscript/pull/356#discussion_r2579529893
  // and https://github.com/hkust-taco/mlscript/pull/356#discussion_r2585183902
  def shouldRewriteWhile: Bool =
    rewriteWhileLoops
  
  def tailRecOpt: Bool = optimizer.tailRecOpt
  
  def deforest: Opt[Deforest] = optimizer.deforest
  
  def inlining: Opt[Inliner] = optimizer.inlining
  
  def deadBranchRemoval: Bool = optimizer.deadBranchRemoval
  
  def flowBasedOpt: Opt[FlowBasedOpt] = optimizer.flowBasedOpt
  
  def mapOptimizer(f: Optimizer => Optimizer): Config = copy(optimizer = f(optimizer))
  
end Config


object Config:
  
  def default(baseDir: io.Path): Config = Config(
    language = Language.default,
    baseDir = baseDir,
    sanityChecks = N, // TODO make the default S
    // sanityChecks = S(SanityChecks(light = true)),
    checkCasts = true,
    effectHandlers = N,
    liftDefns = S(LiftDefns()),
    patMatConsequentSharingThreshold = default.patMatConsequentSharingThreshold, // minimum: 1
    target = CompilationTarget.JS,
    rewriteWhileLoops = false,
    stageCode = false,
    qqEnabled = false,
    funcToCls = false,
    commentGeneratedCode = false,
    noFreeze = false,
    noModuleCheck = false,
    aggressive = false,
    debug = Debug.default,
    optimizer = Optimizer.FastOpt,
    checkInvariants = false,
  )
  object default:
    val patMatConsequentSharingThreshold = S(15)
    val deadBranchRemoval = false // TODO
    val inlineThreshold = 10
  
  /** A language version, as named in `#lang` directives (e.g., `0.3.1` or `0.3.x`).
    * A `patch` of `N` stands for the `x` of a version like `0.3.x`, which denotes the latest state
    * of its minor series and is thus newer than every numbered patch of that series
    * (e.g., `0.3.1 < 0.3.x < 0.4.0`).
    * Version-gated features are enabled by comparing versions with the ordering defined here.
    * Version names must not be compared as strings, since that would make `0.10.x` older than `0.3.1`;
    * nor can versions be plain `(Int, Int, Opt[Int])` tuples compared with the standard tuple ordering,
    * since `Option`'s standard ordering puts `None` first, which would make `0.3.x` older than `0.3.1`. */
  case class Version(major: Int, minor: Int, patch: Opt[Int]) extends Ordered[Version]:
    def compare(that: Version): Int =
      if major =/= that.major then major.compare(that.major)
      else if minor =/= that.minor then minor.compare(that.minor)
      else (patch, that.patch) match
        case (S(p1), S(p2)) => p1.compare(p2)
        case (S(_), N) => -1
        case (N, S(_)) => 1
        case (N, N) => 0
    def name: Str = s"$major.$minor.${patch.fold("x")(_.toString)}"
  end Version
  
  object Version:
    // * Only accept canonical version names, so that each version has exactly one name
    // * (e.g., reject `0.03.1` as an alias of `0.3.1`).
    private val component = "0|[1-9][0-9]*"
    private val VersionName = s"($component)\\.($component)\\.($component|x)".r
    def parse(name: Str): Opt[Version] = name match
      case VersionName(majorName, minorName, patchName) =>
        for
          major <- majorName.toIntOption
          minor <- minorName.toIntOption
          patch <- if patchName === "x" then S(N) else patchName.toIntOption.map(S(_))
        yield Version(major, minor, patch)
      case _ => N
  end Version
  
  case class Language(
    allowUnresolvedAccesses: Bool,
    useNewResolution: Bool,
    strictResolution: Bool, // Reject multiple resolved selection targets as well as missing targets
    // Unknown inputs admitted by a public interface are checked regardless of this flag.
    eagerResolution: Bool, // Reject invalid selection/call candidates even when other candidates supply valid targets
    typeCheck: Opt[TypeChecking],
  )(
    // * `N` when no version was specified with `#lang` (see `Language.default`),
    // * in which case no version-gated feature is enabled.
    val version: Opt[Version],
  ):
    def newUnderscoreAndApplicationSyntax: Bool =
      version.exists(_ > Language.v0_3_1.version.get)
  end Language
  
  object Language:
    
    val v0_2_x = Language(
      typeCheck = N,
      useNewResolution = false,
      strictResolution = false,
      eagerResolution = false,
      allowUnresolvedAccesses = true,
    )(
      version = S(Version(0, 2, N)),
    )
    
    val v0_3_1 = Language(
      typeCheck = N,
      useNewResolution = true,
      strictResolution = false,
      eagerResolution = false,
      allowUnresolvedAccesses = false,
    )(
      version = S(Version(0, 3, S(1))),
    )
    
    val v0_3_x = v0_3_1.copy(
    )(
      version = S(Version(0, 3, N)),
    )
    
    val presets: Map[Version, Language] = Ls(
      v0_2_x,
      v0_3_1,
      v0_3_x,
    ).map: lang =>
      lang.version.getOrElse(lastWords("language presets must specify a version")) -> lang
    .toMap
    
    // * The language used when no version is specified with `#lang`.
    // * It behaves like the oldest preset, but has no version, so that a missing `#lang` can be reported.
    val default = v0_2_x.copy()(version = N)
    
    val latestVersion = Version(0, 3, N)
    val latest = presets(latestVersion)
    
  end Language
  
  // TODO
  case class TypeChecking()

  enum DebugOutput:
    case StdIO
    /** A relative path written in a directive is resolved, when the directive is parsed,
      * against the directory of the file in which it is written, as for imports. */
    case File(path: io.Path)

  case class Debug(
    showParsedTree: Bool,
    elaboration: Bool,
    showElaboratedTree: Bool,
    showElaboratedTerm: Bool,
    lowering: Bool,
    showLoweredTree: Bool,
    optimizations: Bool,
    showIR: Bool,
    showOptimizedIR: Bool,
    showUids: Bool,
    out: DebugOutput,
  )
  object Debug:
    val default = Debug(
      showParsedTree = false,
      elaboration = false,
      showElaboratedTree = false,
      showElaboratedTerm = false,
      lowering = false,
      showLoweredTree = false,
      optimizations = false,
      showIR = false,
      showOptimizedIR = false,
      showUids = true,
      out = DebugOutput.StdIO,
    )
  
  case class SanityChecks(light: Bool, checkUnreachable: Bool)
  
  case class EffectHandlers(
    debug: Bool,
    stackSafety: Opt[StackSafety],
    // Whether we check `Instantiate` nodes for effects. Currently, effects cannot be raised in constructors.
    checkInstantiateEffect: Bool = false,
    // A debug option that allows codegen to continue even if an unlifted definition is encountered.
    softLifterError: Bool = false,
    // Skips instrumenting module constructors, this can be used when the file is statically known to not
    // raise any effect and cannot use the Runtime.mls module during module construction due to cyclic dependency.
    // One specific scenario is Rendering.mls, which Runtime.mls depends on, and hence using stack safety will
    // reference Runtime.mls during construction of the Rendering module, causing a cyclic dependency error.
    doNotInstrumentTopLevelModCtor: Bool = false,
  )
  
  case class StackSafety(stackLimit: Int)
  object StackSafety:
    val default: StackSafety = StackSafety(
      stackLimit = 1000,
    )
  
  case class LiftDefns() // there may be other settings in the future, having it as a case class now

  case class FlowAnalysisConfig(
    debug: Bool,
    mono: Bool,
    trackNonAffine: Bool,
    trackAccumulator: Bool,
    logNonAffine: Bool,
    logAccumulator: Bool,
    // `debug` turns on all three at once
    debugEta: Bool = false,
    debugDpe: Bool = false,
    debugDce: Bool = false,
    logEffects: Bool = false,
  ):
    def effectiveDebugEta: Bool = debug || debugEta
    def effectiveDebugDpe: Bool = debug || debugDpe
    def effectiveDebugDce: Bool = debug || debugDce

    def effectiveTrackNonAffine: Bool =
      trackNonAffine || logNonAffine

    def effectiveTrackAccumulator: Bool =
      trackAccumulator || logAccumulator
  
  object FlowAnalysisConfig:
    val defaultMono = FlowAnalysisConfig(
      debug = false,
      mono = true,
      trackNonAffine = false,
      trackAccumulator = false,
      logNonAffine = false,
      logAccumulator = false,
    )
  
  case class Deforest(config: FlowAnalysisConfig):
    export config.{
      debug,
      mono,
      trackNonAffine,
      trackAccumulator,
      logNonAffine,
      logAccumulator,
      effectiveTrackNonAffine,
      effectiveTrackAccumulator,
    }
  object Deforest:
    val default = Deforest(FlowAnalysisConfig(
      debug = true,
      mono = false,
      trackNonAffine = true,
      trackAccumulator = false,
      logNonAffine = false,
      logAccumulator = false,
    ))

  case class FlowBasedOpt(config: FlowAnalysisConfig):
    export config.{debug, mono, effectiveDebugEta, effectiveDebugDpe, effectiveDebugDce}
  object FlowBasedOpt:
    val default = FlowBasedOpt(FlowAnalysisConfig.defaultMono)
    def withDebug(debug: Bool) =
      FlowBasedOpt(default.config.copy(debug = debug))

  /** `altSmallThreshold` is the alternative threshold for inlining things into @inline functions.
    * Normally, we avoid inlining into @inline functions as that could lead to unexpected code bloat. */
  case class Inliner(inlineThreshold: Int, altSmallThreshold: Int = 2)
  
  /** File directives apply to the whole compilation unit, including elaboration.
    * Read them before constructing the elaborator so its resolver agrees with lowering.
    * Elaboration still records SetConfig statements and reports directive errors once. */
  def elaborationConfig(prgm: syntax.Tree.Block, sourceDir: io.Path)(using Config): Config =
    elaborationConfig(prgm.desugStmts, sourceDir)

  /** Read directives from parsed trees before elaboration or tree display.
    * `sourceDir` is the directory of the file containing the trees. */
  def elaborationConfig(trees: Ls[syntax.Tree], sourceDir: io.Path)(using Config): Config =
    import syntax.Tree.*
    given Raise = _ => ()
    def modifier(tree: syntax.Tree): Config => Config = tree match
      case App(Directive(prefix, _), args) => modifier(Directive(prefix, args))
      case Directive(Ident("config"), Tup(args)) => ConfigParser.parseOverrides(args)
      case Directive(Ident("lang"), Tup(args)) => ConfigParser.parseLanguageDirective(args)
      case Directive(Ident("dbg"), Tup(args)) => ConfigParser.parseDebugDirective(args, definitionLocal = false, sourceDir)
      case _ => identity
    trees.foldLeft(config)((cfg, tree) => modifier(tree)(cfg))

  def extractConfigFromStats(prgm: semantics.Term.Blk)(using Config) =
    // Extract cumulative config modifications from SetConfig statements
    val configModify = prgm.stats.collect:
      case sc: semantics.SetConfig => sc.modify
    .foldLeft(identity[Config]): (acc, modify) =>
      cfg => modify(acc(cfg))
    configModify(config)
  
  case class Optimizer(
    deforest: Opt[Deforest],
    tailRecOpt: Bool,
    inlining: Opt[Inliner],
    deadBranchRemoval: Bool,
    deadCodeElim: Bool,
    dataFlowAnalysis: Bool,
    flowBasedOpt: Opt[FlowBasedOpt],
  )
  
  object Optimizer:
    val NoOpt = Optimizer(
      N,
      false,
      N,
      false,
      false,
      false,
      N
    )
    
    val FastOpt = Optimizer(
      deforest = N,
      tailRecOpt = true,
      inlining = S(Inliner(default.inlineThreshold)),
      deadBranchRemoval = default.deadBranchRemoval,
      deadCodeElim = true,
      dataFlowAnalysis = true,
      flowBasedOpt = S(FlowBasedOpt.default),
    )

end Config


object ConfigParser:
  import syntax.Tree
  import syntax.Tree.*
  import syntax.Keyword

  private object NamedArg:
    def unapply(tree: Tree): Opt[(Str, Tree)] = tree match
      case InfixApp(Ident(name), Keywrd(Keyword.`:`), value) => S(name -> value)
      case _ => N

  private object Call:
    def unapply(tree: Tree): Opt[(Str, Ls[Tree])] = tree match
      case App(Ident(name), Tup(args)) => S(name -> args)
      case _ => N

  private def unsupported(context: Str, tree: Tree)(using Raise): Unit =
    raise(ErrorReport(
      msg"Unsupported ${context} argument" -> tree.toLoc :: Nil,
      source = Diagnostic.Source.Compilation))

  private def expect(context: Str)(tree: Tree)(using Raise): Unit =
    raise(ErrorReport(
      msg"Expected ${context}" -> tree.toLoc :: Nil,
      source = Diagnostic.Source.Compilation))

  private def setFrom[A](tree: Tree)(parse: Tree => Opt[A])(assign: A => Unit)(using Raise): Bool =
    parse(tree) match
      case S(value) =>
        assign(value)
        true
      case N => false

  private def parsedField[A](value: Tree)(parse: Tree => Opt[A])(set: A => Config => Config)(using Raise): Config => Config =
    parse(value) match
      case S(v) => set(v)
      case N => identity

  private def optionalField[A](value: Tree)(parse: Tree => Opt[A])(set: Opt[A] => Config => Config)(using Raise): Config => Config =
    parseOpt(value)(parse) match
      case S(v) => set(v)
      case N => identity

  private def optionalFieldWithCurrent[A](
    value: Tree,
  )(
    current: Config => Opt[A],
  )(
    parse: (Tree, Opt[A]) => Opt[A],
  )(
    set: Opt[A] => Config => Config,
  )(using Raise): Config => Config =
    cfg =>
      parseOpt(value)(tree => parse(tree, current(cfg))) match
        case S(v) => set(v)(cfg)
        case N => cfg
  
  /** Parse a list of config override arguments (from the Tup tree) into a Config modification function. */
  def parseOverrides(args: Ls[Tree])(using Raise): Config => Config =
    args.foldLeft(identity[Config]): (acc, arg) =>
      val override_ = parseOverride(arg)
      cfg => override_(acc(cfg))
  
  /** Parse a single config override argument. */
  def parseOverride(arg: Tree)(using Raise): Config => Config = arg match
    case NamedArg(name, value) =>
      parseField(name, value)
    case _ =>
      raise(ErrorReport(
        msg"Unsupported config override syntax" -> arg.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      identity
  
  private def parseBool(tree: Tree)(using Raise): Opt[Bool] = tree match
    case BoolLit(v) => S(v)
    case Ident("true") => S(true)
    case Ident("false") => S(false)
    case _ =>
      expect("a boolean value")(tree)
      N
  
  private def parseInt(tree: Tree)(using Raise): Opt[Int] = tree match
    case IntLit(v) => S(v.toInt)
    case PrefixOpApp(Ident("-"), IntLit(v)) => S(-v.toInt)
    case _ =>
      expect("an integer value")(tree)
      N

  private def parseVersionName(tree: Tree)(using Raise): Opt[Str] = tree match
    case StrLit(name) => S(name)
    case Ident(name) => S(name)
    case IntLit(value) => S(value.toString)
    case DecLit(value) => S(value.toString)
    case Sel(prefix, Ident(suffix)) =>
      parseVersionName(prefix).map: prefix =>
        s"${prefix}.${suffix}"
    case _ =>
      expect("a language version name")(tree)
      N

  private def parseTypeChecking(tree: Tree)(using Raise): Opt[Config.TypeChecking] = tree match
    case Ident("TypeChecking") =>
      S(Config.TypeChecking())
    case Call("TypeChecking", Nil) =>
      S(Config.TypeChecking())
    case _ =>
      expect("TypeChecking()")(tree)
      N

  private def parseLanguagePreset(tree: Tree)(using Raise): Opt[Config.Language] =
    parseVersionName(tree).flatMap: name =>
      Config.Version.parse(name).flatMap(Config.Language.presets.get) match
        case S(language) => S(language)
        case N =>
          raise(ErrorReport(
            msg"Unknown language version '${name}'" -> tree.toLoc ::
              msg"Available language versions: ${Config.Language.presets.keys.toList.sorted.map(_.name).mkString(", ")}" -> N ::
              Nil,
            source = Diagnostic.Source.Compilation))
          N

  private def parsedLanguageModifier[A](
    value: Tree,
  )(
    parse: Tree => Opt[A],
  )(
    modify: A => Config.Language => Config.Language,
  )(using Raise): Opt[Config.Language => Config.Language] =
    parse(value).map(modify)

  private def parseLanguageFieldModifier(tree: Tree)(using Raise): Opt[Config.Language => Config.Language] = tree match
    case NamedArg("allowUnresolvedAccesses", value) =>
      parsedLanguageModifier(value)(parseBool): v =>
        lang => lang.copy(allowUnresolvedAccesses = v)(lang.version)
    case NamedArg("useNewResolution", value) =>
      parsedLanguageModifier(value)(parseBool): v =>
        lang => lang.copy(useNewResolution = v)(lang.version)
    case NamedArg("strictResolution", value) =>
      parsedLanguageModifier(value)(parseBool): v =>
        lang => lang.copy(strictResolution = v)(lang.version)
    case NamedArg("eagerResolution", value) =>
      parsedLanguageModifier(value)(parseBool): v =>
        lang => lang.copy(eagerResolution = v)(lang.version)
    case NamedArg("typeCheck", value) =>
      parsedLanguageModifier(value)(tree => parseOpt(tree)(parseTypeChecking)): v =>
        lang => lang.copy(typeCheck = v)(lang.version)
    case other =>
      unsupported("Language", other)
      N

  private def parseLanguageFieldModifiers(args: Ls[Tree])(using Raise): Opt[Ls[Config.Language => Config.Language]] =
    var modifiers = Ls.empty[Config.Language => Config.Language]
    var ok = true
    args.foreach: arg =>
      parseLanguageFieldModifier(arg) match
        case S(modifier) => modifiers ::= modifier
        case N => ok = false
    if ok then S(modifiers.reverse) else N

  private def applyLanguageFieldModifiers(
    base: Config.Language,
    modifiers: Ls[Config.Language => Config.Language],
  ): Config.Language =
    modifiers.foldLeft(base):
      case (language, modify) => modify(language)

  private def parseLanguage(tree: Tree)(using Raise): Opt[Config.Language => Config.Language] = tree match
    case Call("Language", args) =>
      parseLanguageFieldModifiers(args).map: modifiers =>
        language => applyLanguageFieldModifiers(language, modifiers)
    case _ =>
      parseLanguagePreset(tree).map: language =>
        _ => language

  private def parseLanguageDirectiveArgs(args: Ls[Tree])(using Raise): Config => Config =
    def isNamedArg(tree: Tree): Bool = tree match
      case NamedArg(_, _) => true
      case _ => false
    args match
      case Nil =>
        raise(ErrorReport(
          msg"Expected at least one language argument" -> N :: Nil,
          source = Diagnostic.Source.Compilation))
        identity
      case head :: tail if isNamedArg(head) =>
        parseLanguageFieldModifiers(args) match
          case S(modifiers) =>
            cfg => cfg.copy(language = applyLanguageFieldModifiers(cfg.language, modifiers))
          case N => identity
      case head :: tail =>
        val languageBase = parseLanguage(head)
        val tailModifiers = parseLanguageFieldModifiers(tail)
        (languageBase, tailModifiers) match
          case (S(makeBase), S(modifiers)) =>
            cfg =>
              val base = makeBase(cfg.language)
              cfg.copy(language = applyLanguageFieldModifiers(base, modifiers))
          case _ => identity

  private def parseLanguageOverride(value: Tree)(using Raise): Config => Config =
    parseLanguage(value) match
      case S(modify) =>
        cfg => cfg.copy(language = modify(cfg.language))
      case N => identity

  private def parseDebugOutput(tree: Tree, sourceDir: io.Path)(using Raise): Opt[Config.DebugOutput] = tree match
    case Ident("StdIO") | Call("StdIO", Nil) =>
      S(Config.DebugOutput.StdIO)
    case Call("File", StrLit(path) :: Nil) =>
      S(Config.DebugOutput.File(io.Path.resolve(sourceDir, path)))
    case _ =>
      expect("StdIO or File(\"path\")")(tree)
      N

  private def updateDebugFlag(name: Str, value: Bool, tree: Tree, definitionLocal: Bool)(using Raise): Config.Debug => Config.Debug =
    if definitionLocal && name === "optimizations" then
      raise(WarningReport(
        msg"Debugging aspect '${name}' is not supported in @dbg; use #dbg(${name}: ${value.toString}) instead." -> tree.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
    name match
      case "showParsedTree" => _.copy(showParsedTree = value)
      case "elaboration" => _.copy(elaboration = value)
      case "showElaboratedTree" => _.copy(showElaboratedTree = value)
      case "showElaboratedTerm" => _.copy(showElaboratedTerm = value)
      case "lowering" => _.copy(lowering = value)
      case "showLoweredTree" => _.copy(showLoweredTree = value)
      case "optimizations" => _.copy(optimizations = value)
      case "showIR" => _.copy(showIR = value)
      case "showOptimizedIR" => _.copy(showOptimizedIR = value)
      case "showUids" => _.copy(showUids = value)
      case _ =>
        raise(ErrorReport(
          msg"Unknown debugging aspect '${name}'" -> tree.toLoc :: Nil,
          source = Diagnostic.Source.Compilation))
        identity

  private def parseDebugArg(arg: Tree, definitionLocal: Bool, sourceDir: io.Path)(using Raise): Config.Debug => Config.Debug = arg match
    case Quoted(Ident(name)) =>
      updateDebugFlag(name, true, arg, definitionLocal)
    case Ident(name) if name.startsWith("'") =>
      updateDebugFlag(name.drop(1), true, arg, definitionLocal)
    case NamedArg("out", value) =>
      parseDebugOutput(value, sourceDir) match
        case S(out) => _.copy(out = out)
        case N => identity
    case NamedArg(name, value) =>
      parseBool(value) match
        case S(enabled) => updateDebugFlag(name, enabled, arg, definitionLocal)
        case N => identity
    case _ =>
      unsupported("debugging", arg)
      identity

  /** Parse `#dbg(...)` and `@dbg(...)` arguments into a cumulative debug configuration.
    * `sourceDir` is the directory of the file containing them. */
  def parseDebugDirective(args: Ls[Tree], definitionLocal: Bool, sourceDir: io.Path)(using Raise): Config => Config =
    val modifyDebug = args.foldLeft(identity[Config.Debug]): (acc, arg) =>
      val modify = parseDebugArg(arg, definitionLocal, sourceDir)
      debug => modify(acc(debug))
    new (Config => Config):
      def apply(cfg: Config): Config = cfg.copy(debug = modifyDebug(cfg.debug))
      override def toString: Str = "..."

  /** Select parsed-tree displays without duplicating diagnostics reported by elaboration. */
  def discoverDebugFromAnnotations(annotations: Ls[Tree], base: Config, sourceDir: io.Path): Opt[Config] =
    given Raise = _ => ()
    val modifiers = annotations.collect:
      case App(Ident("dbg"), Tup(args)) => parseDebugDirective(args, definitionLocal = true, sourceDir)
    if modifiers.isEmpty then N
    else S(modifiers.foldLeft(base)((cfg, modify) => modify(cfg)))

  /** Parse the `None`/`Some(...)` syntax for optional config fields.
    * Also accepts unwrapped values as a convenience (treated as `Some(value)`). */
  private def parseOpt[A](tree: Tree)(parseInner: Tree => Opt[A])(using Raise): Opt[Opt[A]] = tree match
    case Ident("None") | Ident("N") =>
      S(N)
    case App(Ident("Some") | Ident("S"), Tup(inner :: Nil)) =>
      parseInner(inner).map(v => S(v))
    case other =>
      parseInner(other).map(v => S(v))
  
  private def parseStackSafety(tree: Tree)(using Raise): Opt[Config.StackSafety] = tree match
    case Call("StackSafety", args) =>
      var stackLimit = Config.StackSafety.default.stackLimit
      args.foreach:
        case NamedArg("stackLimit", value) =>
          setFrom(value)(parseInt)(v => stackLimit = v)
        case IntLit(v) =>
          stackLimit = v.toInt
        case other =>
          unsupported("StackSafety", other)
      S(Config.StackSafety(stackLimit))
    case IntLit(v) =>
      S(Config.StackSafety(v.toInt))
    case _ =>
      expect("StackSafety(...) or an integer")(tree)
      N
  
  private def parseEffectHandlers(tree: Tree, current: Opt[Config.EffectHandlers])(using Raise): Opt[Config.EffectHandlers] = tree match
    case Call("EffectHandlers", args) =>
      val base = current.getOrElse(Config.EffectHandlers(debug = false, stackSafety = N))
      var debug = base.debug
      var stackSafety = base.stackSafety
      var checkInstantiateEffect = base.checkInstantiateEffect
      var softLifterError = base.softLifterError
      var doNotInstrumentTopLevelModCtor = base.doNotInstrumentTopLevelModCtor
      args.foreach:
        case NamedArg("debug", value) =>
          setFrom(value)(parseBool)(v => debug = v)
        case NamedArg("stackSafety", value) =>
          setFrom(value)(tree => parseOpt(tree)(parseStackSafety))(v => stackSafety = v)
        case NamedArg("checkInstantiateEffect", value) =>
          setFrom(value)(parseBool)(v => checkInstantiateEffect = v)
        case NamedArg("softLifterError", value) =>
          setFrom(value)(parseBool)(v => softLifterError = v)
        case NamedArg("doNotInstrumentTopLevelModCtor", value) =>
          setFrom(value)(parseBool)(v => doNotInstrumentTopLevelModCtor = v)
        case other =>
          unsupported("EffectHandlers", other)
      S(Config.EffectHandlers(debug, stackSafety, checkInstantiateEffect, softLifterError, doNotInstrumentTopLevelModCtor))
    case _ =>
      expect("EffectHandlers(...)")(tree)
      N

  private def parseFlowAnalysisConfig(
    tree: Tree,
    passName: Str,
    current: Opt[FlowAnalysisConfig],
    default: FlowAnalysisConfig,
  )(using Raise): Opt[FlowAnalysisConfig] =
    val base = current.getOrElse(default)
    tree match
    case Call(name, args) if name == passName =>
      var debug = base.debug
      var mono = base.mono
      var trackNonAffine = base.trackNonAffine
      var trackAccumulator = base.trackAccumulator
      var logNonAffine = base.logNonAffine
      var logAccumulator = base.logAccumulator
      var debugEta = base.debugEta
      var debugDpe = base.debugDpe
      var debugDce = base.debugDce
      var logEffects = base.logEffects
      args.foreach:
        case NamedArg("debug", value) =>
          setFrom(value)(parseBool)(v => debug = v)
        case NamedArg("mono", value) =>
          setFrom(value)(parseBool)(v => mono = v)
        case NamedArg("trackNonAffine", value) =>
          setFrom(value)(parseBool)(v => trackNonAffine = v)
        case NamedArg("trackAccumulator", value) =>
          setFrom(value)(parseBool)(v => trackAccumulator = v)
        case NamedArg("logNonAffine", value) =>
          setFrom(value)(parseBool)(v => logNonAffine = v)
        case NamedArg("logAccumulator", value) =>
          setFrom(value)(parseBool)(v => logAccumulator = v)
        case NamedArg("debugEta", value) =>
          setFrom(value)(parseBool)(v => debugEta = v)
        case NamedArg("debugDpe", value) =>
          setFrom(value)(parseBool)(v => debugDpe = v)
        case NamedArg("debugDce", value) =>
          setFrom(value)(parseBool)(v => debugDce = v)
        case NamedArg("logEffects", value) =>
          setFrom(value)(parseBool)(v => logEffects = v)
        case other =>
          unsupported(passName, other)
      S(Config.FlowAnalysisConfig(
        debug,
        mono,
        trackNonAffine,
        trackAccumulator,
        logNonAffine,
        logAccumulator,
        debugEta,
        debugDpe,
        debugDce,
        logEffects,
      ))
    case _ =>
      expect(s"${passName}(...)")(tree)
      N

  private def parseDeforest(tree: Tree, current: Opt[Config.Deforest])(using Raise): Opt[Config.Deforest] =
    parseFlowAnalysisConfig(
      tree,
      "Deforest",
      current.map(_.config),
      Config.Deforest.default.config
    ).map:
      Config.Deforest.apply

  private def parseFlowBasedOpt(tree: Tree, current: Opt[Config.FlowBasedOpt])(using Raise): Opt[Config.FlowBasedOpt] =
    parseFlowAnalysisConfig(
      tree,
      "FlowBasedOpt",
      current.map(_.config),
      Config.FlowBasedOpt.default.config
    ).map:
      Config.FlowBasedOpt.apply

  /** Parse a single field override like `tailRecOpt: false`. */
  private def parseField(name: Str, value: Tree)(using Raise): Config => Config = name match
    case "language" => parseLanguageOverride(value)
    case "noOpt" =>
      parsedField(value)(parseBool)(v => _.mapOptimizer(_ => Optimizer.NoOpt))
    case "tailRecOpt" =>
      parsedField(value)(parseBool)(v => _.mapOptimizer(_.copy(tailRecOpt = v)))
    case "noFreeze" =>
      parsedField(value)(parseBool)(v => _.copy(noFreeze = v))
    case "noModuleCheck" =>
      parsedField(value)(parseBool)(v => _.copy(noModuleCheck = v))
    case "aggressive" =>
      parsedField(value)(parseBool)(v => _.copy(aggressive = v))
    case "rewriteWhileLoops" =>
      parsedField(value)(parseBool)(v => _.copy(rewriteWhileLoops = v))
    case "stageCode" =>
      parsedField(value)(parseBool)(v => _.copy(stageCode = v))
    case "qqEnabled" =>
      parsedField(value)(parseBool)(v => _.copy(qqEnabled = v))
    case "funcToCls" =>
      parsedField(value)(parseBool)(v => _.copy(funcToCls = v))
    case "commentGeneratedCode" =>
      parsedField(value)(parseBool)(v => _.copy(commentGeneratedCode = v))
    case "effectHandlers" =>
      optionalFieldWithCurrent(value)(_.effectHandlers)(
        (tree, current) => parseEffectHandlers(tree, current)
      )(v => _.copy(effectHandlers = v))
    case "liftDefns" =>
      optionalField(value)(_ => S(Config.LiftDefns()))(v => _.copy(liftDefns = v))
    case "deforest" =>
      optionalFieldWithCurrent(value)(_.deforest)(
        (tree, current) => parseDeforest(tree, current)
      )(v => _.mapOptimizer(_.copy(deforest = v)))
    case "flowBasedOpt" =>
      optionalFieldWithCurrent(value)(_.flowBasedOpt)(
        (tree, current) => parseFlowBasedOpt(tree, current)
      )(v => _.mapOptimizer(_.copy(flowBasedOpt = v)))
    case "sanityChecks" =>
      optionalField(value)(_ => S(Config.SanityChecks(light = true, checkUnreachable = true)))(v => _.copy(sanityChecks = v))
    case "checkCasts" =>
      parsedField(value)(parseBool)(v => _.copy(checkCasts = v))
    case "patMatConsequentSharingThreshold" =>
      parsedField(value)(parseInt)(v => _.copy(patMatConsequentSharingThreshold = S(v)))
    case "inlining" =>
      optionalField(value)(parseInt)(v => _.mapOptimizer(_.copy(inlining = v.map(Inliner(_)))))
    case "deadBranchRemoval" =>
      parsedField(value)(parseBool)(v => _.mapOptimizer(_.copy(deadBranchRemoval = v)))
    case _ =>
      raise(ErrorReport(
        msg"Unknown config field '${name}'" -> value.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      identity

  /** Parse a `#lang(version)` directive as shorthand for `#config(language: version)`. */
  def parseLanguageDirective(args: Ls[Tree])(using Raise): Config => Config =
    parseLanguageDirectiveArgs(args)
end ConfigParser
