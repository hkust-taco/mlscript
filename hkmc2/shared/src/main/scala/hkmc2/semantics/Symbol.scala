package hkmc2
package semantics

import scala.collection.mutable
import scala.collection.mutable.{Set => MutSet}

import mlscript.utils.*, shorthands.*
import syntax.*

import Tree.Ident


// TODO refactor: don't rely on global state!
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
  
  def asCls: Opt[ClassSymbol] = this match
    case cls: ClassSymbol => S(cls)
    case mem: BlockMemberSymbol =>
      mem.clsTree.map(_.symbol.asInstanceOf[ClassSymbol])
    case _ => N
  def asMod: Opt[ModuleSymbol] = this match
    case cls: ModuleSymbol => S(cls)
    case mem: BlockMemberSymbol =>
      mem.modTree.map(_.symbol.asInstanceOf[ModuleSymbol])
    case _ => N
  def asAls: Opt[TypeAliasSymbol] = this match
    case cls: TypeAliasSymbol => S(cls)
    case mem: BlockMemberSymbol =>
      mem.alsTree.map(_.symbol.asInstanceOf[TypeAliasSymbol])
    case _ => N
  
  def asClsLike: Opt[ClassSymbol | ModuleSymbol] = asCls orElse asMod
  def asTpe: Opt[TypeSymbol] = asCls orElse asAls
  
  override def equals(x: Any): Bool = x match
    case that: Symbol => uid === that.uid
    case _ => false
  override def hashCode: Int = uid.hashCode

end Symbol


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
  def id: Ident

abstract class BlockLocalSymbol(name: Str, uid: Int) extends FlowSymbol(name, uid) with LocalSymbol:
  var decl: Opt[Declaration] = N

class TempSymbol(uid: Int, val trm: Opt[Term], dbgNme: Str = "tmp") extends BlockLocalSymbol(dbgNme, uid):
  val nameHints: MutSet[Str] = MutSet.empty
  override def toLoc: Option[Loc] = trm.flatMap(_.toLoc)
  override def toString: Str = s"$$${super.toString}"

class VarSymbol(val id: Ident, uid: Int) extends BlockLocalSymbol(id.name, uid) with NamedSymbol:
  val name: Str = id.name
  // override def toString: Str = s"$name@$uid"

class BuiltinSymbol(val nme: Str, val binary: Bool, val unary: Bool, val nullary: Bool) extends Symbol:
  def toLoc: Option[Loc] = N
  override def toString: Str = s"builtin:$nme"


/** This is the outside-facing symbol associated to a possibly-overloaded
  * definition living in a block – e.g., a module or class. */
class BlockMemberSymbol(val nme: Str, val trees: Ls[Tree]) extends MemberSymbol[Definition]:
  
  def toLoc: Option[Loc] = Loc(trees)
  
  def clsTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if t.k is Cls => t
  def modTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if t.k is Mod => t
  def alsTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if t.k is Als => t
  def trmTree: Opt[Tree.TermDef] = trees.collectFirst:
    case t: Tree.TermDef /* if t.k is  */ => t
  def trmImplTree: Opt[Tree.TermDef] = trees.collectFirst:
    case t: Tree.TermDef if t.rhs.isDefined => t
  
  lazy val hasLiftedClass: Bool =
    modTree.isDefined || trmTree.isDefined || clsTree.exists(_.paramLists.nonEmpty)
  
  override def toString: Str = s"member:$nme"

end BlockMemberSymbol


sealed abstract class MemberSymbol[Defn <: Definition] extends Symbol:
  def nme: Str
  var defn: Opt[Defn] = N


class TermSymbol(val k: TermDefKind, val owner: Opt[InnerSymbol], val id: Tree.Ident)
    extends MemberSymbol[Definition] with LocalSymbol with NamedSymbol:
  def nme: Str = id.name
  def name: Str = nme
  def toLoc: Option[Loc] = id.toLoc
  override def toString: Str = s"${owner.getOrElse("")}.${id.name}"


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


type TypeSymbol = ClassSymbol | TypeAliasSymbol


/** This is the symbol associated to specific definitions.
  * One overloaded `BlockMemberSymbol` may correspond to multiple `InnerSymbol`s
  * A `Ref(_: InnerSymbol)` represents a `this`-like reference to the current object. */
sealed trait InnerSymbol extends Symbol

class ClassSymbol(val tree: Tree.TypeDef, val id: Tree.Ident)
    extends MemberSymbol[ClassDef] with CtorSymbol with InnerSymbol:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of classe here
  override def toString: Str = s"class:$nme"
  /** Compute the arity. */
  def arity: Int = defn match
    case S(d) => d.paramsOpt.fold(0)(_.length)
    case N => tree.paramLists.headOption.fold(0)(_.fields.length)

class ModuleSymbol(val tree: Tree.TypeDef, val id: Tree.Ident)
    extends MemberSymbol[ModuleDef] with CtorSymbol with InnerSymbol:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of module here
  override def toString: Str = s"module:${id.name}"

class TypeAliasSymbol(val id: Tree.Ident) extends MemberSymbol[TypeDef]:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of type alias here
  override def toString: Str = s"module:${id.name}"

class TopLevelSymbol(blockNme: Str)
    extends MemberSymbol[ModuleDef] with InnerSymbol:
  def nme = blockNme
  def toLoc: Option[Loc] = N
  override def toString: Str = s"globalThis:$blockNme"


