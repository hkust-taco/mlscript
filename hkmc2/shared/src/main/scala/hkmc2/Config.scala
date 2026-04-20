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
  inlining: Opt[Inliner],
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
    inlining = S(Inliner(1)),
    qqEnabled = false,
    funcToCls = false,
    commentGeneratedCode = false,
    noFreeze = false,
    noModuleCheck = false,
    deadParamElim = N
  )
  object default:
    val patMatConsequentSharingThreshold = S(15)
  
  case class SanityChecks(light: Bool)
  
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
  
  case class Deforest(val debug: Boolean, val mono: Boolean)
  object Deforest:
    val default = Deforest(true, false)

  case class DeadParamElim(val debug: Boolean, val mono: Boolean)
  object DeadParamElim:
    val default = DeadParamElim(true, true)
  
  case class Inliner(inlineThreshold: Int)

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

  private def parseDeforest(tree: Tree, current: Opt[Config.Deforest])(using Raise): Opt[Config.Deforest] = tree match
    case BoolLit(true) | Ident("true") | Ident("Deforest") =>
      S(current.getOrElse(Config.Deforest.default))
    case App(Ident("Deforest"), Tup(args)) =>
      val base = current.getOrElse(Config.Deforest.default)
      var debug = base.debug
      var mono = base.mono
      args.foreach:
        case InfixApp(Ident("debug"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => debug = v)
        case InfixApp(Ident("mono"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => mono = v)
        case other =>
          raise(ErrorReport(
            msg"Unsupported Deforest argument" -> other.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
      S(Config.Deforest(debug, mono))
    case _ =>
      raise(ErrorReport(
        msg"Expected Deforest(...), Deforest, or true" -> tree.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      N

  private def parseDeadParamElim(tree: Tree, current: Opt[Config.DeadParamElim])(using Raise): Opt[Config.DeadParamElim] = tree match
    case BoolLit(true) | Ident("true") | Ident("DeadParamElim") =>
      S(current.getOrElse(Config.DeadParamElim.default))
    case App(Ident("DeadParamElim"), Tup(args)) =>
      val base = current.getOrElse(Config.DeadParamElim.default)
      var debug = base.debug
      var mono = base.mono
      args.foreach:
        case InfixApp(Ident("debug"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => debug = v)
        case InfixApp(Ident("mono"), Keywrd(Keyword.`:`), value) =>
          parseBool(value).foreach(v => mono = v)
        case other =>
          raise(ErrorReport(
            msg"Unsupported DeadParamElim argument" -> other.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
      S(Config.DeadParamElim(debug, mono))
    case _ =>
      raise(ErrorReport(
        msg"Expected DeadParamElim(...), DeadParamElim, or true" -> tree.toLoc :: Nil,
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
    case "deadParamElim" =>
      cfg =>
        parseOpt(value)(v => parseDeadParamElim(v, cfg.deadParamElim)) match
          case S(v) => cfg.copy(deadParamElim = v)
          case N => cfg
    case "sanityChecks" =>
      parseOpt(value)(_ => S(Config.SanityChecks(light = true))) match
        case S(v) => _.copy(sanityChecks = v)
        case N => identity
    case "patMatConsequentSharingThreshold" =>
      parseInt(value) match
        case S(v) => _.copy(patMatConsequentSharingThreshold = S(v))
        case N => identity
    case "inlining" =>
      parseOpt(value)(parseInt) match
        case S(v) => _.copy(inlining = v.map(Inliner.apply))
        case _ => identity
    case _ =>
      raise(ErrorReport(
        msg"Unknown config field '${name}'" -> value.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      identity
end ConfigParser

