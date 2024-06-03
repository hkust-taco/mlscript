package hkmc2
package bbml

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import semantics.*, semantics.Term.*


sealed abstract class TypeArg

case class Wildcard(in: Type, out: Type) extends TypeArg

enum Type extends TypeArg:
  case ClassType(name: ClassSymbol, targs: Ls[TypeArg])
  case InfVar(lvl: Int, uid: Uid[InfVar], state: VarState)
  case FunType(args: Ls[Type], ret: Type, eff: Type)
  case ComposedType(lhs: Type, rhs: Type, pol: Bool) // * positive -> union
  case NegType(ty: Type)
  case PolymorphicType(lvl: Int, tv: Ls[InfVar], body: Type)
  case Top // TODO: level?
  case Bot

// TODO: apply
opaque type RefType = Type.ClassType
object RefType

opaque type RegionType = Type.ClassType
object RegionType

opaque type CodeBaseType = Type.ClassType
object CodeBaseType

opaque type CodeType = CodeBaseType
object CodeType

opaque type VarType = CodeBaseType
object VarType

// TODO: builtin functions

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
  




