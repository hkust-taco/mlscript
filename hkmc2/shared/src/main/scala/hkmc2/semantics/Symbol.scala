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
  def refsNumber: Int = directRefs.size
  override def equals(x: Any): Bool = x match
    case that: Symbol => uid === that.uid
    case _ => false
  override def hashCode: Int = uid.hashCode

class FlowSymbol(label: Str, uid: Int) extends Symbol:
  def nme: Str = label
  import typing.*
  val outFlows: mutable.Buffer[FlowSymbol] = mutable.Buffer.empty
  val outFlows2: mutable.Buffer[Consumer] = mutable.Buffer.empty
  val inFlows: mutable.Buffer[ConcreteProd] = mutable.Buffer.empty
  override def toString: Str = s"$label@$uid"

class VarSymbol(val name: Str, uid: Int) extends FlowSymbol(name, uid):
  // def nme: Str = name
  var decl: Opt[Declaration] = N
  // override def toString: Str = s"$name@$uid"

abstract class MemberSymbol extends Symbol:
  def nme: Str
  var defn: Opt[Definition] = N

class TermSymbol(val id: Tree.Ident) extends MemberSymbol:
  def nme: Str = id.name
  override def toString: Str = s"${id.name}"

sealed trait CtorSymbol extends Symbol

case class Extr(isTop: Bool) extends CtorSymbol:
  def nme: Str = if isTop then "Top" else "Bot"
  override def toString: Str = nme

case class LitSymbol(lit: Literal) extends CtorSymbol:
  def nme: Str = lit.toString
  override def toString: Str = s"lit:$lit"
case class TupSymbol(arity: Opt[Int]) extends CtorSymbol:
  def nme: Str = s"Tuple#$arity"
  override def toString: Str = s"tup:$arity"

class ClassSymbol(val id: Tree.Ident) extends MemberSymbol with CtorSymbol:
  def nme = id.name
  override def toString: Str = s"class:$nme"
class ModuleSymbol(val name: Str) extends MemberSymbol:
  def nme = name
  override def toString: Str = s"module:$name"
class TypeAliasSymbol(val name: Str) extends MemberSymbol:
  def nme = name
  override def toString: Str = s"module:$name"


