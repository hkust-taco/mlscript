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
  effectHandlers: Opt[EffectHandlers],
  liftDefns: Opt[LiftDefns],
  patMatConsequentSharingThreshold: Opt[Int],
  stageCode: Bool,
  target: CompilationTarget,
  rewriteWhileLoops: Bool,
  tailRecOpt: Bool,
  deforest: Opt[Deforest],
  etaExpansion: Opt[EtaExpansion],
  inlining: Opt[Inliner],
  deadBranchRemoval: Bool,
  qqEnabled: Bool,
  funcToCls: Bool,
  commentGeneratedCode: Bool,
  noFreeze: Bool,
  noModuleCheck: Bool,
  deadParamElim: Opt[DeadParamElim],
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
  
end Config


object Config:
  
  def default(baseDir: io.Path): Config = Config(
    language = Language.default,
    baseDir = baseDir,
    sanityChecks = N, // TODO make the default S
    // sanityChecks = S(SanityChecks(light = true)),
    effectHandlers = N,
    liftDefns = S(LiftDefns()),
    patMatConsequentSharingThreshold = default.patMatConsequentSharingThreshold, // minimum: 1
    target = CompilationTarget.JS,
    rewriteWhileLoops = false,
    stageCode = false,
    tailRecOpt = true,
    deforest = N,
    etaExpansion = S(EtaExpansion.default),
    inlining = S(Inliner(default.inlineThreshold)),
    deadBranchRemoval = default.deadBranchRemoval,
    qqEnabled = false,
    funcToCls = false,
    commentGeneratedCode = false,
    noFreeze = false,
    noModuleCheck = false,
    deadParamElim = S(DeadParamElim.default)
  )
  object default:
    val patMatConsequentSharingThreshold = S(15)
    val deadBranchRemoval = false // TODO
    val inlineThreshold = 10
  
  case class Language(
    allowUnresolvedAccesses: Bool,
    useNewResolution: Bool,
    typeCheck: Opt[TypeChecking],
  )(val versionName: Str)
  
  object Language:
    
    val v0_2_x = Language(
      typeCheck = N,
      useNewResolution = false,
      allowUnresolvedAccesses = true,
    )(
      versionName = "0.2.x",
    )
    
    val v0_3_x = Language(
      typeCheck = N,
      useNewResolution = true,
      allowUnresolvedAccesses = false,
    )(
      versionName = "0.3.x",
    )
    
    val presets: Map[Str, Language] = Ls(
      v0_2_x,
      v0_3_x,
    ).map(l => l.versionName -> l).toMap
    
    val default = v0_2_x
    
  end Language
  
  // TODO
  case class TypeChecking()
  
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
  ):
    def effectiveTrackNonAffine: Bool =
      trackNonAffine || logNonAffine

    def effectiveTrackAccumulator: Bool =
      trackAccumulator || logAccumulator
  
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

  case class DeadParamElim(config: FlowAnalysisConfig):
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
  object DeadParamElim:
    val default = DeadParamElim(FlowAnalysisConfig(
      debug = false,
      mono = true,
      trackNonAffine = false,
      trackAccumulator = false,
      logNonAffine = false,
      logAccumulator = false,
    ))

  case class EtaExpansion(config: FlowAnalysisConfig):
    export config.debug
  object EtaExpansion:
    def withDebug(debug: Bool): EtaExpansion =
      EtaExpansion(FlowAnalysisConfig(
        debug = debug,
        mono = true,
        trackNonAffine = false,
        trackAccumulator = false,
        logNonAffine = false,
        logAccumulator = false,
      ))
    val default: EtaExpansion = withDebug(debug = false)
  
  /** `altSmallThreshold` is the alternative threshold for inlining things into @inline functions.
    * Normally, we avoid inlining into @inline functions as that could lead to unexpected code bloat. */
  case class Inliner(inlineThreshold: Int, altSmallThreshold: Int = 2)
  
  def extractConfigFromStats(prgm: semantics.Term.Blk)(using Config) =
    // Extract cumulative config modifications from SetConfig statements
    val configModify = prgm.stats.collect:
      case sc: semantics.SetConfig => sc.modify
    .foldLeft(identity[Config]): (acc, modify) =>
      cfg => modify(acc(cfg))
    configModify(config)

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
    case App(Ident("-"), Tup(IntLit(v) :: Nil)) => S(-v.toInt)
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
      Config.Language.presets.get(name) match
        case S(language) => S(language)
        case N =>
          raise(ErrorReport(
            msg"Unknown language version '${name}'" -> tree.toLoc ::
              msg"Available language versions: ${Config.Language.presets.keys.toList.sorted.mkString(", ")}" -> N ::
              Nil,
            source = Diagnostic.Source.Compilation))
          N

  private def withLanguage(
    base: Config.Language,
    allowUnresolvedAccesses: Bool,
    useNewResolution: Bool,
    typeCheck: Opt[Config.TypeChecking],
  ): Config.Language =
    Config.Language(
      allowUnresolvedAccesses,
      useNewResolution,
      typeCheck,
    )(
      base.versionName,
    )

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
        language => withLanguage(language, v, language.useNewResolution, language.typeCheck)
    case NamedArg("useNewResolution", value) =>
      parsedLanguageModifier(value)(parseBool): v =>
        language => withLanguage(language, language.allowUnresolvedAccesses, v, language.typeCheck)
    case NamedArg("typeCheck", value) =>
      parsedLanguageModifier(value)(tree => parseOpt(tree)(parseTypeChecking)): v =>
        language => withLanguage(language, language.allowUnresolvedAccesses, language.useNewResolution, v)
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
        case other =>
          unsupported(passName, other)
      S(Config.FlowAnalysisConfig(
        debug,
        mono,
        trackNonAffine,
        trackAccumulator,
        logNonAffine,
        logAccumulator,
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

  private def parseDeadParamElim(tree: Tree, current: Opt[Config.DeadParamElim])(using Raise): Opt[Config.DeadParamElim] =
    parseFlowAnalysisConfig(
      tree,
      "DeadParamElim",
      current.map(_.config),
      Config.DeadParamElim.default.config
    ).map:
      Config.DeadParamElim.apply

  private def parseEtaExpansion(tree: Tree, current: Opt[Config.EtaExpansion])(using Raise): Opt[Config.EtaExpansion] =
    tree match
    case Call("EtaExpansion", args) =>
      var debug = current.getOrElse(Config.EtaExpansion.default).debug
      args.foreach:
        case NamedArg("debug", value) =>
          setFrom(value)(parseBool)(v => debug = v)
        case other =>
          unsupported("EtaExpansion", other)
      S(Config.EtaExpansion.withDebug(debug))
    case _ =>
      expect("EtaExpansion(...)")(tree)
      N
  
  /** Parse a single field override like `tailRecOpt: false`. */
  private def parseField(name: Str, value: Tree)(using Raise): Config => Config = name match
    case "language" => parseLanguageOverride(value)
    case "tailRecOpt" =>
      parsedField(value)(parseBool)(v => _.copy(tailRecOpt = v))
    case "noFreeze" =>
      parsedField(value)(parseBool)(v => _.copy(noFreeze = v))
    case "noModuleCheck" =>
      parsedField(value)(parseBool)(v => _.copy(noModuleCheck = v))
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
      )(v => _.copy(deforest = v))
    case "etaExpansion" =>
      optionalFieldWithCurrent(value)(_.etaExpansion)(
        (tree, current) => parseEtaExpansion(tree, current)
      )(v => _.copy(etaExpansion = v))
    case "deadParamElim" =>
      optionalFieldWithCurrent(value)(_.deadParamElim)(
        (tree, current) => parseDeadParamElim(tree, current)
      )(v => _.copy(deadParamElim = v))
    case "sanityChecks" =>
      optionalField(value)(_ => S(Config.SanityChecks(light = true, checkUnreachable = true)))(v => _.copy(sanityChecks = v))
    case "patMatConsequentSharingThreshold" =>
      parsedField(value)(parseInt)(v => _.copy(patMatConsequentSharingThreshold = S(v)))
    case "inlining" =>
      optionalField(value)(parseInt)(v => _.copy(inlining = v.map(Inliner(_))))
    case "deadBranchRemoval" =>
      parsedField(value)(parseBool)(v => _.copy(deadBranchRemoval = v))
    case _ =>
      raise(ErrorReport(
        msg"Unknown config field '${name}'" -> value.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      identity

  /** Parse a `#lang(version)` directive as shorthand for `#config(language: version)`. */
  def parseLanguageDirective(args: Ls[Tree])(using Raise): Config => Config =
    parseLanguageDirectiveArgs(args)
end ConfigParser
