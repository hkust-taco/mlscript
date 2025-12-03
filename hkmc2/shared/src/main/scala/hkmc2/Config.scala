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
  sanityChecks: Opt[SanityChecks],
  effectHandlers: Opt[EffectHandlers],
  liftDefns: Opt[LiftDefns],
  stageCode: Bool,
  target: CompilationTarget,
  rewriteWhileLoops: Bool,
):
  
  def stackSafety: Opt[StackSafety] = effectHandlers.flatMap(_.stackSafety)
  
  // NOTE: with `Scoped` blocks inside loop bodies, currently this flag
  // forces the rewriting of while loops to make sure that
  // the handler lowering will not create classes containing unbound variables
  def shouldRewriteWhile: Bool =
    rewriteWhileLoops || effectHandlers.isDefined
  
end Config


object Config:
  
  val default: Config = Config(
    sanityChecks = N, // TODO make the default S
    // sanityChecks = S(SanityChecks(light = true)),
    effectHandlers = N,
    liftDefns = N,
    target = CompilationTarget.JS,
    rewriteWhileLoops = true,
    stageCode = false,
  )
  
  case class SanityChecks(light: Bool)
  
  case class EffectHandlers(debug: Bool, stackSafety: Opt[StackSafety])
  
  case class StackSafety(stackLimit: Int)
  object StackSafety:
    val default: StackSafety = StackSafety(
      stackLimit = 500,
    )

  case class LiftDefns() // there may be other settings in the future, having it as a case class now
  
end Config


