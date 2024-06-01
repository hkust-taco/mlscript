package hkmc2
package bbml

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import semantics.*, semantics.Term.*


sealed abstract class TypeArg

case class Wildcard(in: Type, out: Type) extends TypeArg

enum Type extends TypeArg:
  case ClassType(targs: Ls[TypeArg])
  case InfVar(lvl: Int, uid: Uid[InfVar], state: VarState)

class VarState:
  var lowerBounds: Ls[Type] = Nil
  var upperBounds: Ls[Type] = Nil

object InfVarUid extends Uid.Handler[Type.InfVar]

class Ctx

class BBTyper(raise: Raise):
  
  def typeCheck(t: Term)(using Ctx): Type = t match
    case Ref(sym: VarSymbol) =>
      ???
    case Ref(cls: ClassSymbol) =>
      ???
    case Blk(stats, res) =>
      ???
    case Lit(lit) =>
      ???
  




