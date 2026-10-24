package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import hkmc2.Message.MessageContext

/** Ordering rules shared by value parameters and function type parameters.
  * Callers keep their own binding and recovery logic: even an invalid parameter
  * advances the order, so later parameters are checked against the written list.
  * Restrictions specific to declarations (such as contextual parameters) are
  * checked before asking this validator about an optional parameter's position.
  */
private[semantics] final case class ParameterOrder(seenOptional: Bool, seenVariadic: Bool):
  def checkFixed(optional: Bool, loc: Opt[Loc])(using Raise): Unit =
    if optional && seenVariadic then
      raise(ErrorReport(msg"Optional parameters cannot follow a variadic parameter." -> loc :: Nil))
    else if !optional && seenOptional && !seenVariadic then
      raise(ErrorReport(msg"A required parameter cannot follow an optional parameter." -> loc :: Nil))

  def checkVariadic(loc: Opt[Loc])(using Raise): Unit =
    if seenVariadic then
      raise(ErrorReport(msg"A parameter list cannot have more than one variadic parameter." -> loc :: Nil))

  def next(optional: Bool, variadic: Bool): ParameterOrder =
    ParameterOrder(seenOptional || optional, seenVariadic || variadic)

private[semantics] object ParameterOrder:
  val empty: ParameterOrder = ParameterOrder(false, false)
