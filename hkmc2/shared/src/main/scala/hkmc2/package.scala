package hkmc2

import sourcecode.{Line, FileName}

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.Message.MessageContext


extension [A](a: A)
  infix inline def givenIn[R](inline k: A ?=> R) = k(using a)
  def abbreviate: Str = a.toString.truncate(100, "[...]")
  infix inline def ne_::(xs: Ls[A]): NELs[A] = new ::(a, xs)

extension [A](xs: Ls[A])
  def ne_! : NELs[A] = xs match
    case Nil => throw new IllegalArgumentException("Cannot convert an empty list to a non-empty list.")
    case xs: NELs[A] => xs
  inline def ne_? : Opt[NELs[A]] = xs match
    case Nil => N
    case xs: NELs[A] => S(xs)


// * Valid identifiers for the members of module and class-like definitions
// * Importantly, these are the same as valid JavaScript identifiers,
// * so we do not check them in JS code-generation.
val identifierPattern: scala.util.matching.Regex = "^[A-Za-z_$][A-Za-z0-9_$]*$".r


def softAssert(cond: Boolean, msg: => Str = "")(using Line, FileName, Raise): Unit =
  if !cond then
    raise:
      InternalError(
        msg"Compiler reached an unexpected state at '${summon[FileName].value}:${summon[Line].value}'${
          if msg === "" then "" else s": $msg"}" -> N
        :: msg"The compilation result may be incorrect." -> N
        :: msg"This is a compiler bug; please report it to the maintainers." -> N
        :: Nil)

def softTODO(cond: Boolean, msg: => Str = "")(using Line, FileName, Raise): Unit =
  if !cond then
    raise:
      InternalError(
        msg"Compiler reached an unsupported state${
          if msg === "" then "" else s": $msg"}" -> N
        :: msg"The compilation result may be incorrect." -> N
        :: msg"This is a known compiler limitation; if it is a blocker for you, please report it to the maintainers." -> N
        :: Nil)

