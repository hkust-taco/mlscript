package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import Config.*


def config(using Config): Config = summon

case class Config(
  sanityChecks: Opt[SanityChecks],
  effectHandlers: Opt[EffectHandlers],
):
  
  def stackSafety: Opt[StackSafety] = effectHandlers.flatMap(_.stackSafety)
  
end Config


object Config:
  
  val default: Config = Config(
    sanityChecks = N, // TODO make the default S
    // sanityChecks = S(SanityChecks(light = true)),
    effectHandlers = N,
  )
  
  case class SanityChecks(light: Bool)
  
  case class EffectHandlers(stackSafety: Opt[StackSafety])
  
  case class StackSafety(stackLimit: Int)
  object StackSafety:
    val default: StackSafety = StackSafety(
      stackLimit = 500,
    )
  
end Config


