package hkmc2

import mlscript.utils.*, shorthands.*
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
  
  // NOTE: We force the rewriting of while loops to functions when handler lowering is on
  // to prevent the "floating out" of definitions done by handler lowering,
  // which currently does not respect scopes introduced by `Scoped` blocks.
  // Currently, this is only a problem with while loops because we do not yet
  // construct nested Scoped blocks in other places (but will in the future).
  // see https://github.com/hkust-taco/mlscript/pull/356#discussion_r2579529893
  // and https://github.com/hkust-taco/mlscript/pull/356#discussion_r2585183902
  def shouldRewriteWhile: Bool =
    rewriteWhileLoops || effectHandlers.isDefined
  
end Config


object Config:
  
  def default(baseDir: io.Path): Config = Config(
    baseDir = baseDir,
    sanityChecks = N, // TODO make the default S
    // sanityChecks = S(SanityChecks(light = true)),
    effectHandlers = N,
    liftDefns = N,
    patMatConsequentSharingThreshold = default.patMatConsequentSharingThreshold, // minimum: 1
    target = CompilationTarget.JS,
    rewriteWhileLoops = false,
    stageCode = false,
    tailRecOpt = true,
    deforest = N,
    etaExpansion = S(EtaExpansion.default),
    inlining = S(Inliner(10)),
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
  
  /** Parse a list of config override arguments (from the Tup tree) into a Config modification function. */
  def parseOverrides(args: Ls[Tree])(using Raise): Config => Config =
    args.foldLeft(identity[Config]): (acc, arg) =>
      val override_ = parseOverride(arg)
      cfg => override_(acc(cfg))
  
  /** Parse a single config override argument. */
  def parseOverride(arg: Tree)(using Raise): Config => Config = arg match
    case InfixApp(Ident(name), Keywrd(Keyword.`:`), value) =>
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
      raise(ErrorReport(
        msg"Expected a boolean value" -> tree.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      N
  
  private def parseInt(tree: Tree)(using Raise): Opt[Int] = tree match
    case IntLit(v) => S(v.toInt)
    case App(Ident("-"), Tup(IntLit(v) :: Nil)) => S(-v.toInt)
    case _ =>
      raise(ErrorReport(
        msg"Expected an integer value" -> tree.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      N

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
    case App(Ident("StackSafety"), Tup(args)) =>
      var stackLimit = Config.StackSafety.default.stackLimit
      args.foreach:
        case InfixApp(Ident("stackLimit"), Keywrd(Keyword.`:`), value) =>
          parseInt(value).foreach(v => stackLimit = v)
        case IntLit(v) =>
          stackLimit = v.toInt
        case other =>
          raise(ErrorReport(
            msg"Unsupported StackSafety argument" -> other.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
      S(Config.StackSafety(stackLimit))
    case IntLit(v) =>
      S(Config.StackSafety(v.toInt))
    case _ =>
      raise(ErrorReport(
        msg"Expected StackSafety(...) or an integer" -> tree.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      N
  
  private def parseEffectHandlers(tree: Tree, current: Opt[Config.EffectHandlers])(using Raise): Opt[Config.EffectHandlers] = tree match
    case App(Ident("EffectHandlers"), Tup(args)) =>
      val base = current.getOrElse(Config.EffectHandlers(debug = false, stackSafety = N))
      var debug = base.debug
      var stackSafety = base.stackSafety
      var checkInstantiateEffect = base.checkInstantiateEffect
      var softLifterError = base.softLifterError
      var doNotInstrumentTopLevelModCtor = base.doNotInstrumentTopLevelModCtor
      args.foreach:
        case InfixApp(Ident("debug"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => debug = v)
        case InfixApp(Ident("stackSafety"), Keywrd(Keyword.`:`), value) =>
          parseOpt(value)(parseStackSafety).foreach(v => stackSafety = v)
        case InfixApp(Ident("checkInstantiateEffect"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => checkInstantiateEffect = v)
        case InfixApp(Ident("softLifterError"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => softLifterError = v)
        case InfixApp(Ident("doNotInstrumentTopLevelModCtor"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => doNotInstrumentTopLevelModCtor = v)
        case other =>
          raise(ErrorReport(
            msg"Unsupported EffectHandlers argument" -> other.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
      S(Config.EffectHandlers(debug, stackSafety, checkInstantiateEffect, softLifterError, doNotInstrumentTopLevelModCtor))
    case _ =>
      raise(ErrorReport(
        msg"Expected EffectHandlers(...)" -> tree.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      N

  private def parseFlowAnalysisConfig(
    tree: Tree,
    passName: Str,
    current: Opt[FlowAnalysisConfig],
    default: FlowAnalysisConfig,
  )(using Raise): Opt[FlowAnalysisConfig] =
    val base = current.getOrElse(default)
    tree match
    case App(Ident(name), Tup(args)) if name == passName =>
      var debug = base.debug
      var mono = base.mono
      var trackNonAffine = base.trackNonAffine
      var trackAccumulator = base.trackAccumulator
      var logNonAffine = base.logNonAffine
      var logAccumulator = base.logAccumulator
      args.foreach:
        case InfixApp(Ident("debug"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => debug = v)
        case InfixApp(Ident("mono"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => mono = v)
        case InfixApp(Ident("trackNonAffine"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => trackNonAffine = v)
        case InfixApp(Ident("trackAccumulator"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => trackAccumulator = v)
        case InfixApp(Ident("logNonAffine"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => logNonAffine = v)
        case InfixApp(Ident("logAccumulator"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => logAccumulator = v)
        case other =>
          raise(ErrorReport(
            msg"Unsupported ${passName} argument" -> other.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
      S(Config.FlowAnalysisConfig(
        debug,
        mono,
        trackNonAffine,
        trackAccumulator,
        logNonAffine,
        logAccumulator,
      ))
    case _ =>
      raise(ErrorReport(
        msg"Expected ${passName}(...)" -> tree.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
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
    case App(Ident("EtaExpansion"), Tup(args)) =>
      var debug = current.getOrElse(Config.EtaExpansion.default).debug
      args.foreach:
        case InfixApp(Ident("debug"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => debug = v)
        case other =>
          raise(ErrorReport(
            msg"Unsupported EtaExpansion argument" -> other.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
      S(Config.EtaExpansion.withDebug(debug))
    case _ =>
      raise(ErrorReport(
        msg"Expected EtaExpansion(...)" -> tree.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      N
  
  /** Parse a single field override like `tailRecOpt: false`. */
  private def parseField(name: Str, value: Tree)(using Raise): Config => Config = name match
    case "tailRecOpt" => parseBool(value) match
      case S(v) => _.copy(tailRecOpt = v)
      case N => identity
    case "noFreeze" => parseBool(value) match
      case S(v) => _.copy(noFreeze = v)
      case N => identity
    case "noModuleCheck" => parseBool(value) match
      case S(v) => _.copy(noModuleCheck = v)
      case N => identity
    case "rewriteWhileLoops" => parseBool(value) match
      case S(v) => _.copy(rewriteWhileLoops = v)
      case N => identity
    case "stageCode" => parseBool(value) match
      case S(v) => _.copy(stageCode = v)
      case N => identity
    case "qqEnabled" => parseBool(value) match
      case S(v) => _.copy(qqEnabled = v)
      case N => identity
    case "funcToCls" => parseBool(value) match
      case S(v) => _.copy(funcToCls = v)
      case N => identity
    case "commentGeneratedCode" => parseBool(value) match
      case S(v) => _.copy(commentGeneratedCode = v)
      case N => identity
    case "effectHandlers" =>
      cfg =>
        parseOpt(value)(v => parseEffectHandlers(v, cfg.effectHandlers)) match
          case S(v) => cfg.copy(effectHandlers = v)
          case N => cfg
    case "liftDefns" =>
      parseOpt(value)(_ => S(Config.LiftDefns())) match
        case S(v) => _.copy(liftDefns = v)
        case N => identity
    case "deforest" =>
      cfg =>
        parseOpt(value)(v => parseDeforest(v, cfg.deforest)) match
          case S(v) => cfg.copy(deforest = v)
          case N => cfg
    case "etaExpansion" =>
      cfg =>
        parseOpt(value)(v => parseEtaExpansion(v, cfg.etaExpansion)) match
          case S(v) => cfg.copy(etaExpansion = v)
          case N => cfg
    case "deadParamElim" =>
      cfg =>
        parseOpt(value)(v => parseDeadParamElim(v, cfg.deadParamElim)) match
          case S(v) => cfg.copy(deadParamElim = v)
          case N => cfg
    case "sanityChecks" =>
      parseOpt(value)(_ => S(Config.SanityChecks(light = true, checkUnreachable = true))) match
        case S(v) => _.copy(sanityChecks = v)
        case N => identity
    case "patMatConsequentSharingThreshold" =>
      parseInt(value) match
        case S(v) => _.copy(patMatConsequentSharingThreshold = S(v))
        case N => identity
    case "inlining" =>
      parseOpt(value)(parseInt) match
        case S(v) => _.copy(inlining = v.map(Inliner(_)))
        case _ => identity
    case "deadBranchRemoval" =>
      parseBool(value) match
        case S(v) => _.copy(deadBranchRemoval = v)
        case N => identity
    case _ =>
      raise(ErrorReport(
        msg"Unknown config field '${name}'" -> value.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      identity
end ConfigParser

