package hkmc2
package semantics

import collection.mutable

import mlscript.utils.*, shorthands.*
import syntax.*


val suid = new Uid.Symbol.State

abstract class Symbol extends Located:
  def children: List[Located] = Nil
  def nme: Str
  val uid: Uid[Symbol] = suid.nextUid
  val directRefs: mutable.Buffer[Term.Ref] = mutable.Buffer.empty
  def ref: Term.Ref =
    val res = new Term.Ref(this)(directRefs.size)
    directRefs += res
    res

class VarSymbol(val name: Str, uid: Int) extends Symbol:
  def nme: Str = name
  var decl: Opt[Declaration] = N
  override def toString: Str = s"$name@$uid"

abstract class MemberSymbol extends Symbol:
  def nme: Str
  var defn: Opt[Definition] = N

class TermSymbol(val id: Tree.Ident) extends MemberSymbol:
  def nme: Str = id.name
  override def toString: Str = s"${id.name}"

class ClassSymbol(val id: Tree.Ident) extends MemberSymbol:
  def nme = id.name
  override def toString: Str = s"class:$nme"
class ModuleSymbol(val name: Str) extends MemberSymbol:
  def nme = name
  override def toString: Str = s"module:$name"
class TypeAliasSymbol(val name: Str) extends MemberSymbol:
  def nme = name
  override def toString: Str = s"module:$name"


