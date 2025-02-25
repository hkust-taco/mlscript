package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import Config.*


def config(using Config): Config = summon

case class Config(
  sanityChecks: Opt[SanityChecks],
  effectHandlers: Opt[EffectHandlers],
  liftDefns: Opt[LiftDefns],
):
  
  def stackSafety: Opt[StackSafety] = effectHandlers.flatMap(_.stackSafety)
  
end Config


object Config:
  
  val default: Config = Config(
    sanityChecks = N, // TODO make the default S
    // sanityChecks = S(SanityChecks(light = true)),
    effectHandlers = N,
    liftDefns = N,
  )
  
  case class SanityChecks(light: Bool)
  
  case class EffectHandlers(stackSafety: Opt[StackSafety])
  
  case class StackSafety(stackLimit: Int)
  object StackSafety:
    val default: StackSafety = StackSafety(
      stackLimit = 500,
    )

  case class LiftDefns() // there may be other settings in the future, having it as a case class now
  
end Config


