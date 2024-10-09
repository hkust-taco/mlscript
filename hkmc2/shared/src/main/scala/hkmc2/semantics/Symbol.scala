package hkmc2
package semantics

import scala.collection.mutable
import scala.collection.mutable.{Set => MutSet}

import mlscript.utils.*, shorthands.*
import syntax.*

import Tree.Ident


val suid = new Uid.Symbol.State

abstract class Symbol extends Located:
  def nme: Str
  val uid: Uid[Symbol] = suid.nextUid
  val directRefs: mutable.Buffer[Term.Ref] = mutable.Buffer.empty
  def ref(id: Tree.Ident =
    Tree.Ident("") // FIXME hack
  ): Term.Ref =
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

sealed trait LocalSymbol extends Symbol
sealed trait NamedSymbol extends Symbol:
  def name: Str

abstract class BlockLocalSymbol(name: Str, uid: Int) extends FlowSymbol(name, uid) with LocalSymbol:
  var decl: Opt[Declaration] = N

class TempSymbol(uid: Int, val trm: Opt[Term], dbgNme: Str = "tmp") extends BlockLocalSymbol(dbgNme, uid):
  val nameHints: MutSet[Str] = MutSet.empty
  override def toLoc: Option[Loc] = trm.flatMap(_.toLoc)
  override def toString: Str = s"$$${super.toString}"

class VarSymbol(val id: Ident, uid: Int) extends BlockLocalSymbol(id.name, uid) with NamedSymbol:
  val name: Str = id.name
  // override def toString: Str = s"$name@$uid"

abstract class MemberSymbol[Defn <: Definition] extends Symbol:
  def nme: Str
  var defn: Opt[Defn] = N

class TermSymbol(val id: Tree.Ident) extends MemberSymbol[Definition] with LocalSymbol with NamedSymbol:
  def nme: Str = id.name
  def name: Str = nme
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


