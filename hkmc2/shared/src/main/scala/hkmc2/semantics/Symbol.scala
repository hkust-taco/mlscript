package hkmc2
package semantics

import collection.mutable

import mlscript.utils.*, shorthands.*
import syntax.*

import Tree.Ident


val suid = new Uid.Symbol.State

abstract class Symbol extends Located:
  def nme: Str
  val uid: Uid[Symbol] = suid.nextUid
  val directRefs: mutable.Buffer[Term.Ref] = mutable.Buffer.empty
  def ref(id: Tree.Ident): Term.Ref =
    val res = new Term.Ref(this)(id, directRefs.size)
    directRefs += res
    res
  def refsNumber: Int = directRefs.size
  override def equals(x: Any): Bool = x match
    case that: Symbol => uid === that.uid
    case _ => false
  override def hashCode: Int = uid.hashCode

class FlowSymbol(label: Str, uid: Int) extends Symbol:
  def nme: Str = label
  def toLoc: Option[Loc] = N // TODO track source trees of flows
  import typing.*
  val outFlows: mutable.Buffer[FlowSymbol] = mutable.Buffer.empty
  val outFlows2: mutable.Buffer[Consumer] = mutable.Buffer.empty
  val inFlows: mutable.Buffer[ConcreteProd] = mutable.Buffer.empty
  override def toString: Str = s"$label@$uid"

class VarSymbol(val id: Ident, uid: Int) extends FlowSymbol(id.name, uid):
  val name: Str = id.name
  var decl: Opt[Declaration] = N
  // override def toString: Str = s"$name@$uid"

abstract class MemberSymbol[Defn <: Definition] extends Symbol:
  def nme: Str
  var defn: Opt[Defn] = N

class TermSymbol(val id: Tree.Ident) extends MemberSymbol[Definition]:
  def nme: Str = id.name
  def toLoc: Option[Loc] = id.toLoc
  override def toString: Str = s"${id.name}"

sealed trait CtorSymbol extends Symbol

case class Extr(isTop: Bool) extends CtorSymbol:
  def nme: Str = if isTop then "Top" else "Bot"
  def toLoc: Option[Loc] = N
  override def toString: Str = nme

case class LitSymbol(lit: Literal) extends CtorSymbol:
  def nme: Str = lit.toString
  def toLoc: Option[Loc] = lit.toLoc
  override def toString: Str = s"lit:$lit"
case class TupSymbol(arity: Opt[Int]) extends CtorSymbol:
  def nme: Str = s"Tuple#$arity"
  def toLoc: Option[Loc] = N
  override def toString: Str = s"tup:$arity"

class ClassSymbol(val id: Tree.Ident) extends MemberSymbol[ClassDef] with CtorSymbol:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source trees of classes
  override def toString: Str = s"class:$nme"
class ModuleSymbol(val id: Tree.Ident) extends MemberSymbol[ModuleDef]:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source trees of modules
  override def toString: Str = s"module:${id.name}"
class TypeAliasSymbol(val id: Tree.Ident) extends MemberSymbol:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source trees of type aliases
  override def toString: Str = s"module:${id.name}"

