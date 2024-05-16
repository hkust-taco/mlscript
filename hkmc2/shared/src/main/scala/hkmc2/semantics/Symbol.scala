package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


val suid = new Uid.Symbol.State

abstract class Symbol extends Located:
  def children: List[Located] = Nil
  def nme: Str
  val uid: Uid[Symbol] = suid.nextUid

class VarSymbol(val name: Str, uid: Int) extends Symbol:
  def nme: Str = name
  var decl: Opt[Declaration] = N
  override def toString: Str = s"$name@$uid"

abstract class MemberSymbol extends Symbol:
  def nme: Str
  var defn: Opt[Definition] = N

// No name means it's a built-in operator symbol
class TermSymbol(val name: Opt[Tree.Ident]) extends MemberSymbol:
  def nme: Str = name.fold("")(_.name) // FIXME
  override def toString: Str = s"${name.fold("‹builtin›")(_.name)}"

class ClassSymbol(val id: Tree.Ident) extends MemberSymbol:
  def nme = id.name
  override def toString: Str = s"class:$nme"
class ModuleSymbol(val name: Str) extends MemberSymbol:
  def nme = name
  override def toString: Str = s"module:$name"
class TypeAliasSymbol(val name: Str) extends MemberSymbol:
  def nme = name
  override def toString: Str = s"module:$name"


