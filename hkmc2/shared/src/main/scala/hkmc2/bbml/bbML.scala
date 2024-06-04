package hkmc2
package bbml

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import semantics.*, semantics.Term.*
import syntax.*
import Tree.*

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

opaque type RefType = Type.ClassType
object RefType:
  def apply(cnt: TypeArg, reg: TypeArg): RefType = Type.ClassType(ClassSymbol(Tree.Ident("Ref")), cnt :: reg :: Nil)

opaque type RegionType = Type.ClassType
object RegionType:
  def apply(skolem: TypeArg): RegionType = Type.ClassType(ClassSymbol(Tree.Ident("Region")), skolem :: Nil)

opaque type CodeBaseType = Type.ClassType
object CodeBaseType:
  def apply(cr: TypeArg, isVar: TypeArg): CodeBaseType = Type.ClassType(ClassSymbol(Tree.Ident("CodeBase")), cr :: isVar :: Nil)

opaque type CodeType = CodeBaseType
object CodeType:
  def apply(cr: TypeArg): CodeType = CodeBaseType(cr, Type.Top)

opaque type VarType = CodeBaseType
object VarType:
  def apply(cr: TypeArg): VarType = CodeBaseType(cr, Type.Bot)

opaque type IntType = Type.ClassType
object IntType:
  def apply(): IntType = Type.ClassType(ClassSymbol(Tree.Ident("Int")), Nil)

opaque type NumType = Type.ClassType
object NumType:
  def apply(): NumType = Type.ClassType(ClassSymbol(Tree.Ident("Num")), Nil)

opaque type StrType = Type.ClassType
object StrType:
  def apply(): StrType = Type.ClassType(ClassSymbol(Tree.Ident("Str")), Nil)

opaque type BoolType = Type.ClassType
object BoolType:
  def apply(): BoolType = Type.ClassType(ClassSymbol(Tree.Ident("Bool")), Nil)

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
  




