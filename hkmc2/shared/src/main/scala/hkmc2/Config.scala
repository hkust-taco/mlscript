package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import Config.*


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
  stageCode: Bool,
  target: CompilationTarget,
  rewriteWhileLoops: Bool,
  tailRecOpt: Bool,
  qqEnabled: Bool,
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
    target = CompilationTarget.JS,
    rewriteWhileLoops = false,
    stageCode = false,
    tailRecOpt = true,
    qqEnabled = false,
  )
  
  case class SanityChecks(light: Bool)
  
  case class EffectHandlers(
    debug: Bool,
    stackSafety: Opt[StackSafety],
    // Whether we check `Instantiate` nodes for effects. Currently, effects cannot be raised in constructors.
    checkInstantiateEffect: Bool = false,
    // A debug option that allows codegen to continue even if an unlifted definition is encountered.
    softLifterError: Bool = false
  )
  
  case class StackSafety(stackLimit: Int)
  object StackSafety:
    val default: StackSafety = StackSafety(
      stackLimit = 500,
    )

  case class LiftDefns() // there may be other settings in the future, having it as a case class now
  
end Config


