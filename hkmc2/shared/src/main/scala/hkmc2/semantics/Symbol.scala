package hkmc2
package semantics

import scala.collection.mutable
import scala.collection.mutable.{Set => MutSet}

import mlscript.utils.*, shorthands.*
import syntax.*

import Elaborator.State
import Tree.Ident


abstract class Symbol(using State) extends Located:
  
  def nme: Str
  
  val uid: Uid[Symbol] = State.suid.nextUid
  
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
    case mem: BlockMemberSymbol => mem.clsTree.flatMap(_.symbol.asCls)
    case _ => N
  def asMod: Opt[ModuleSymbol] = this match
    case mod: ModuleSymbol => S(mod)
    case mem: BlockMemberSymbol => mem.modTree.flatMap(_.symbol.asMod)
    case _ => N
  /* 
  def asTrm: Opt[TermSymbol] = this match
    case trm: TermSymbol => S(trm)
    case mem: BlockMemberSymbol => mem.trmTree.flatMap(_.symbol.asTrm)
    case _ => N
  */
  def asPat: Opt[PatternSymbol] = this match
    case pat: PatternSymbol => S(pat)
    case mem: BlockMemberSymbol => mem.patTree.flatMap(_.symbol.asPat)
    case _ => N
  def asAls: Opt[TypeAliasSymbol] = this match
    case cls: TypeAliasSymbol => S(cls)
    case mem: BlockMemberSymbol => mem.alsTree.flatMap(_.symbol.asAls)
    case _ => N
  
  def asClsLike: Opt[ClassSymbol | ModuleSymbol | PatternSymbol] =
    (asCls: Opt[ClassSymbol | ModuleSymbol | PatternSymbol]) orElse asMod orElse asPat
  def asTpe: Opt[TypeSymbol] = asCls orElse asAls
  
  override def equals(x: Any): Bool = x match
    case that: Symbol => uid === that.uid
    case _ => false
  override def hashCode: Int = uid.hashCode

end Symbol


class FlowSymbol(label: Str)(using State) extends Symbol:
  def nme: Str = label
  def toLoc: Option[Loc] = N // TODO track source trees of flows
  import typing.*
  val outFlows: mutable.Buffer[FlowSymbol] = mutable.Buffer.empty
  val outFlows2: mutable.Buffer[Consumer] = mutable.Buffer.empty
  val inFlows: mutable.Buffer[ConcreteProd] = mutable.Buffer.empty
  override def toString: Str =
    label + State.dbgUid(uid)


sealed trait LocalSymbol extends Symbol
sealed trait NamedSymbol extends Symbol:
  def name: Str
  def id: Ident

abstract class BlockLocalSymbol(name: Str)(using State) extends FlowSymbol(name) with LocalSymbol:
  var decl: Opt[Declaration] = N

class TempSymbol(val trm: Opt[Term], dbgNme: Str = "tmp")(using State) extends BlockLocalSymbol(dbgNme):
  val nameHints: MutSet[Str] = MutSet.empty
  override def toLoc: Option[Loc] = trm.flatMap(_.toLoc)
  override def toString: Str = s"$$${super.toString}"


// * When instantiating forall-qualified TVs, we need to duplicate the information
// * for pretty-printing, but each instantiation should be different from each other
// * i.e., UID should be different
class InstSymbol(val origin: Symbol)(using State) extends LocalSymbol:
  override def nme: Str = origin.nme
  override def toLoc: Option[Loc] = origin.toLoc
  override def toString: Str = origin.toString


class VarSymbol(val id: Ident)(using State) extends BlockLocalSymbol(id.name) with NamedSymbol:
  val name: Str = id.name
  // override def toString: Str = s"$name@$uid"

class BuiltinSymbol
    (val nme: Str, val binary: Bool, val unary: Bool, val nullary: Bool, val functionLike: Bool)(using State)
    extends Symbol:
  def toLoc: Option[Loc] = N
  override def toString: Str = s"builtin:$nme${State.dbgUid(uid)}"


/** This is the outside-facing symbol associated to a possibly-overloaded
  * definition living in a block – e.g., a module or class. */
class BlockMemberSymbol(val nme: Str, val trees: Ls[Tree])(using State)
    extends MemberSymbol[Definition]:
  
  def toLoc: Option[Loc] = Loc(trees)
  
  def clsTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if t.k is Cls => t
  def modTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if (t.k is Mod) || (t.k is Obj) => t
  def alsTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if t.k is Als => t
  def patTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if t.k is Pat => t
  def trmTree: Opt[Tree.TermDef] = trees.collectFirst:
    case t: Tree.TermDef /* if t.k is  */ => t
  def trmImplTree: Opt[Tree.TermDef] = trees.collectFirst:
    case t: Tree.TermDef if t.rhs.isDefined => t
  
  lazy val hasLiftedClass: Bool =
    modTree.isDefined || trmTree.isDefined || clsTree.exists(_.paramLists.nonEmpty)
  
  override def toString: Str =
    s"member:$nme${State.dbgUid(uid)}"
  
end BlockMemberSymbol


sealed abstract class MemberSymbol[Defn <: Definition](using State) extends Symbol:
  def nme: Str
  var defn: Opt[Defn] = N
  val isGetter: Bool = false


class TermSymbol(val k: TermDefKind, val owner: Opt[InnerSymbol], val id: Tree.Ident)(using State)
    extends MemberSymbol[Definition] with LocalSymbol with NamedSymbol:
  def nme: Str = id.name
  def name: Str = nme
  def toLoc: Option[Loc] = id.toLoc
  override def toString: Str = s"${owner.getOrElse("")}.${id.name}"


sealed trait CtorSymbol extends Symbol

case class Extr(isTop: Bool)(using State) extends CtorSymbol:
  def nme: Str = if isTop then "Top" else "Bot"
  def toLoc: Option[Loc] = N
  override def toString: Str = nme

case class LitSymbol(lit: Literal)(using State) extends CtorSymbol:
  def nme: Str = lit.toString
  def toLoc: Option[Loc] = lit.toLoc
  override def toString: Str = s"lit:$lit"
case class TupSymbol(arity: Opt[Int])(using State) extends CtorSymbol:
  def nme: Str = s"Tuple#$arity"
  def toLoc: Option[Loc] = N
  override def toString: Str = s"tup:$arity"


type TypeSymbol = ClassSymbol | TypeAliasSymbol

type FieldSymbol = TermSymbol | MemberSymbol[?]


/** This is the symbol associated to specific definitions.
  * One overloaded `BlockMemberSymbol` may correspond to multiple `InnerSymbol`s
  * A `Ref(_: InnerSymbol)` represents a `this`-like reference to the current object. */
sealed trait InnerSymbol extends Symbol

class ClassSymbol(val tree: Tree.TypeDef, val id: Tree.Ident)(using State)
    extends MemberSymbol[ClassDef] with CtorSymbol with InnerSymbol with NamedSymbol:
  def name: Str = nme
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of classe here
  override def toString: Str = s"class:$nme${State.dbgUid(uid)}"
  /** Compute the arity. */
  def arity: Int = tree.paramLists.headOption.fold(0)(_.fields.length)

class ModuleSymbol(val tree: Tree.TypeDef, val id: Tree.Ident)(using State)
    extends MemberSymbol[ModuleDef] with CtorSymbol with InnerSymbol with NamedSymbol:
  def name: Str = nme
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of module here
  override def toString: Str = s"module:${id.name}${State.dbgUid(uid)}"

class TypeAliasSymbol(val id: Tree.Ident)(using State) extends MemberSymbol[TypeDef]:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of type alias here
  override def toString: Str = s"module:${id.name}${State.dbgUid(uid)}"

class PatternSymbol(val id: Tree.Ident, val params: Opt[Tree.Tup], val body: Tree)(using State)
    extends MemberSymbol[PatternDef] with CtorSymbol with InnerSymbol:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of pattern here
  override def toString: Str = s"pattern:${id.name}"
  /** The desugared nameless split. */
  private var _split: Opt[ucs.DeBrujinSplit] = N
  def split_=(split: ucs.DeBrujinSplit): Unit = _split = S(split)
  def split: ucs.DeBrujinSplit = _split.getOrElse:
    lastWords(s"found unelaborated pattern: $nme")
  /** The list of pattern parameters, for example,
    * `T` in `pattern Nullable(pattern T) = null | T`.
    */
  var patternParams: Ls[Param] = Nil

class TopLevelSymbol(blockNme: Str)(using State)
    extends MemberSymbol[ModuleDef] with InnerSymbol:
  def nme = blockNme
  def toLoc: Option[Loc] = N
  override def toString: Str = s"globalThis:$blockNme${State.dbgUid(uid)}"


