package hkmc2
package semantics

import scala.collection.mutable
import scala.collection.mutable.{Set => MutSet}

import mlscript.utils.*, shorthands.*
import syntax.*
import hkmc2.utils.*

import Elaborator.State
import Tree.Ident
import hkmc2.utils.SymbolSubst


abstract class Symbol(using State) extends Located:
  
  def nme: Str
  
  def getState: State = summon
  
  val uid: Uid[Symbol] = State.suid.nextUid
  
  val directRefs: mutable.Buffer[Term.Ref] = mutable.Buffer.empty
  def ref(id: Tree.Ident =
    Tree.Ident("") // FIXME hack
  ): Term.Ref =
    val res = new Term.Ref(this)(id, directRefs.size, N)
    directRefs += res
    res
  def refsNumber: Int = directRefs.size
  
  def existsNonModuleful: Bool = this match
    case mod: ModuleOrObjectSymbol => !(mod.tree.k is Mod)
    case mem: BlockMemberSymbol =>
      // Some block member symbols do not correspond to a definition
      // Tree, e.g., val definitions of a data class. So, it is supposed
      // that if there is no tree, then it is not moduleful (because
      // modules do have a tree).
      mem.trees.isEmpty
      || mem.trees.exists:
        case t @ Tree.TypeDef(k = Mod) => false
        case _ => true
    case _ => true
  
  def existsModuleful: Bool = 
    this match
    case mod: ModuleOrObjectSymbol => (mod.tree.k is Mod)
    case mem: BlockMemberSymbol => 
      mem.trees.exists:
        case t @ Tree.TypeDef(k = Mod) => true
        case _ => false
    case _ => false
  
  
  // * Not defining `asTrm` since `TermDef` curretly doesn't have a symbol
  def hasTrmDef: Bool = this match
    case trm: TermSymbol => true
    case mem: BlockMemberSymbol => mem.trmTree.nonEmpty
    case _ => false
  
  def asCls: Opt[ClassSymbol] = this match
    case cls: ClassSymbol => S(cls)
    case mem: BlockMemberSymbol => mem.clsTree.flatMap(_.symbol.asCls)
    case _ => N
  def asModOrObj: Opt[ModuleOrObjectSymbol] = this match
    case mod: ModuleOrObjectSymbol => S(mod)
    case mem: BlockMemberSymbol => mem.modOrObjTree.flatMap(_.symbol.asModOrObj)
    case _ => N
  def asMod: Opt[ModuleOrObjectSymbol] = asModOrObj.filter(_.tree.k is Mod)
  def asObj: Opt[ModuleOrObjectSymbol] = asModOrObj.filter(_.tree.k is Obj)
  def asClsOrMod: Opt[ClassSymbol | ModuleOrObjectSymbol] = asCls orElse asModOrObj
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
  
  def asClsLike: Opt[ClassSymbol | ModuleOrObjectSymbol | PatternSymbol] =
    (asCls: Opt[ClassSymbol | ModuleOrObjectSymbol | PatternSymbol]) orElse asModOrObj orElse asPat
  def asTpe: Opt[TypeSymbol] = asCls
    .orElse[TypeSymbol](asModOrObj)
    .orElse[TypeSymbol](asAls)
  def asNonModTpe: Opt[TypeSymbol] = asCls
    .orElse[TypeSymbol](asObj)
    .orElse[TypeSymbol](asAls)
  
  def asBlkMember: Opt[BlockMemberSymbol] = this match
    case mem: BlockMemberSymbol => S(mem)
    case mem: MemberSymbol[?] => mem.defn match
      case S(defn: TypeLikeDef) => S(defn.bsym)
      case S(defn: TermDefinition) => S(defn.sym)
      case N => N

  /** Get the symbol corresponding to the "representative" of a set of overloaded definitions,
    * or the sole definition, if it is not overloaded.
    * We should consider the ordering terms > classes/objects/types > modules, for this purpose. */
  def asPrincipal =
    asCls orElse
    asObj orElse
    asAls orElse
    asPat orElse
    asMod

  override def equals(x: Any): Bool = x match
    case that: Symbol => uid === that.uid
    case _ => false
  override def hashCode: Int = uid.hashCode

  def subst(using SymbolSubst): Symbol

end Symbol


class FlowSymbol(label: Str)(using State) extends Symbol:
  def nme: Str = label
  def toLoc: Option[Loc] = N // TODO track source trees of flows
  import typing.*
  val outFlows: mutable.Buffer[FlowSymbol] = mutable.Buffer.empty
  val outFlows2: mutable.Buffer[Consumer] = mutable.Buffer.empty
  val inFlows: mutable.Buffer[ConcreteProd] = mutable.Buffer.empty
  def showDbg: Str =
    label + s"‹$uid›"
  override def toString: Str =
    label + State.dbgUid(uid)

  def subst(using s: SymbolSubst): FlowSymbol = s.mapFlowSym(this)

object FlowSymbol:
  
  def app()(using State) =
    // FlowSymbol("‹app-res›")
    FlowSymbol("@")

  def sel(nme: Str)(using State) =
    FlowSymbol(s"⋅$nme")
  
end FlowSymbol

sealed trait LocalSymbol extends Symbol:
  def subst(using s: SymbolSubst): LocalSymbol
sealed trait NamedSymbol extends Symbol:
  def name: Str
  def id: Ident
  def subst(using s: SymbolSubst): NamedSymbol

abstract class BlockLocalSymbol(name: Str)(using State) extends FlowSymbol(name):
  self: LocalSymbol => // * using `with LocalSymbol` in the `extends` clause makes Scala think there's a bad override
  var decl: Opt[Declaration] = N

class TempSymbol(val trm: Opt[Term], dbgNme: Str = "tmp")(using State) extends BlockLocalSymbol(dbgNme) with LocalSymbol:
  // val nameHints: MutSet[Str] = MutSet.empty // * May be useful later?
  override def toLoc: Option[Loc] = trm.flatMap(_.toLoc)
  override def toString: Str = s"$$${super.toString}"
  override def subst(using s: SymbolSubst): TempSymbol = s.mapTempSym(this)


// * When instantiating forall-qualified TVs, we need to duplicate the information
// * for pretty-printing, but each instantiation should be different from each other
// * i.e., UID should be different
class InstSymbol(val origin: Symbol)(using State) extends LocalSymbol:
  override def nme: Str = origin.nme
  override def toLoc: Option[Loc] = origin.toLoc
  override def toString: Str = origin.toString

  def subst(using sub: SymbolSubst): InstSymbol = sub.mapInstSym(this)


class VarSymbol(val id: Ident)(using State) extends BlockLocalSymbol(id.name) with NamedSymbol with LocalSymbol:
  val name: Str = id.name
  override def toLoc: Opt[Loc] = id.toLoc
  // override def toString: Str = s"$name@$uid"
  override def subst(using s: SymbolSubst): VarSymbol = s.mapVarSym(this)

class BuiltinSymbol
    (val nme: Str, val binary: Bool, val unary: Bool, val nullary: Bool, val functionLike: Bool)(using State)
    extends Symbol:
  def toLoc: Option[Loc] = N
  override def toString: Str = s"builtin:$nme${State.dbgUid(uid)}"

  def subst(using sub: SymbolSubst): BuiltinSymbol = sub.mapBuiltInSym(this)


/** This is the outside-facing symbol associated to a possibly-overloaded
  * definition living in a block – e.g., a module or class.
  * `nameIsMeaningful` is `true` when the name comes from the user's source code;
  *   it is false when the name is a default given by the compiler, such as "lambda" when lifting lambdas. */
class BlockMemberSymbol(val nme: Str, val trees: Ls[TypeOrTermDef], val nameIsMeaningful: Bool = true)(using State)
    extends MemberSymbol[Definition]:
  
  def toLoc: Option[Loc] = Loc(trees)
  
  def describe: Str =
    trees match
    case td :: Nil => td.describe
    case _ => trees.iterator.map(_.describe).mkString("overloaded ", ", ", "symbol")
  
  def clsTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if t.k is Cls => t
  def modOrObjTree: Opt[Tree.TypeDef] = modTree orElse objTree
  def objTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if (t.k is Obj) => t
  def modTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if (t.k is Mod) => t
  def alsTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if t.k is Als => t
  def patTree: Opt[Tree.TypeDef] = trees.collectFirst:
    case t: Tree.TypeDef if t.k is Pat => t
  def trmTree: Opt[Tree.TermDef] = trees.collectFirst:
    case t: Tree.TermDef /* if t.k is  */ => t
  def trmImplTree: Opt[Tree.TermDef] = trees.collectFirst:
    case t: Tree.TermDef if t.rhs.isDefined => t
  
  def isParameterizedMethod: Bool = trmTree.exists(_.isParameterizedMethod)
  
  lazy val hasLiftedClass: Bool =
    objTree.isDefined || trmTree.isDefined || clsTree.exists(_.paramLists.nonEmpty)
  
  override def toString: Str =
    s"member:$nme${State.dbgUid(uid)}"
  
  def subst(using sub: SymbolSubst): BlockMemberSymbol = sub.mapBlockMemberSym(this)

end BlockMemberSymbol


sealed abstract class MemberSymbol[Defn <: Definition](using State) extends Symbol:
  def nme: Str
  var defn: Opt[Defn] = N
  def subst(using SymbolSubst): MemberSymbol[Defn]


class TermSymbol(val k: TermDefKind, val owner: Opt[InnerSymbol], val id: Tree.Ident)(using State)
    extends MemberSymbol[Definition] with LocalSymbol with NamedSymbol:
  def nme: Str = id.name
  def name: Str = nme
  def toLoc: Option[Loc] = id.toLoc
  override def toString: Str = s"${owner.getOrElse("")}.${id.name}"
  
  def subst(using sub: SymbolSubst): TermSymbol = sub.mapTermSym(this)


sealed trait CtorSymbol extends Symbol:
  def subst(using sub: SymbolSubst): CtorSymbol = sub.mapCtorSym(this)

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


/** A TypeSymbol that is not an alias. */
type BaseTypeSymbol = ClassSymbol | ModuleOrObjectSymbol

type TypeSymbol = BaseTypeSymbol | TypeAliasSymbol

type FieldSymbol = MemberSymbol[?]

/**
  * ErrorSymbol is a placeholder symbol denoting error (during symbol
  * resolution in the elaborator / resolver). This helps prevent the
  * same error from throwing multiple times.
  */
case class ErrorSymbol(val nme: Str, tree: Tree)(using State) extends MemberSymbol[Nothing]:

  override def toLoc: Option[Loc] = tree.toLoc

  override def subst(using sub: SymbolSubst): MemberSymbol[Nothing] = sub.mapErrorSym(this)

  override def toString = s"error:$nme"

sealed trait ClassLikeSymbol extends IdentifiedSymbol:
  self: MemberSymbol[? <: ClassDef | ModuleOrObjectDef] =>
  val tree: Tree.TypeDef
  def subst(using sub: SymbolSubst): ClassLikeSymbol


/** This is the symbol associated to specific definitions.
  * One overloaded `BlockMemberSymbol` may correspond to multiple `InnerSymbol`s
  * A `Ref(_: InnerSymbol)` represents a `this`-like reference to the current object. */
  // TODO prevent from appearing in Ref
sealed trait InnerSymbol(using State) extends Symbol:
  val privatesScope: Scope = Scope.empty // * Scope for private members of this symbol
  val thisProxy: TempSymbol = TempSymbol(N, s"this$$$nme")
  def subst(using SymbolSubst): InnerSymbol

trait IdentifiedSymbol extends Symbol:
  val id: Tree.Ident

class ClassSymbol(val tree: Tree.TypeDef, val id: Tree.Ident)(using State)
    extends MemberSymbol[ClassDef] with ClassLikeSymbol with CtorSymbol with InnerSymbol with NamedSymbol:
  def name: Str = nme
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of classe here
  override def toString: Str = s"class:$nme${State.dbgUid(uid)}"
  /** Compute the arity. */
  def arity: Int = tree.paramLists.headOption.fold(0)(_.fields.length)
  
  override def subst(using sub: SymbolSubst): ClassSymbol = sub.mapClsSym(this)

class ModuleOrObjectSymbol(val tree: Tree.TypeDef, val id: Tree.Ident)(using State)
    extends MemberSymbol[ModuleOrObjectDef] with ClassLikeSymbol with CtorSymbol with InnerSymbol with NamedSymbol:
  def name: Str = nme
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of module here
  override def toString: Str =
    if tree.k is Obj then s"object:$nme${State.dbgUid(uid)}"
    else s"module:${id.name}${State.dbgUid(uid)}"
  
  override def subst(using sub: SymbolSubst): ModuleOrObjectSymbol = sub.mapModuleSym(this)

class TypeAliasSymbol(val id: Tree.Ident)(using State) extends MemberSymbol[TypeDef]:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of type alias here
  override def toString: Str = s"type:${id.name}${State.dbgUid(uid)}"
  
  def subst(using sub: SymbolSubst): TypeAliasSymbol = sub.mapTypeAliasSym(this)

class PatternSymbol(val id: Tree.Ident, val params: Opt[Tree.Tup], val body: Tree)(using State)
    extends MemberSymbol[PatternDef] with CtorSymbol with InnerSymbol:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of pattern here
  override def toString: Str = s"pattern:${id.name}"
  
  override def subst(using sub: SymbolSubst): PatternSymbol = sub.mapPatSym(this)

class TopLevelSymbol(blockNme: Str)(using State)
    extends MemberSymbol[ModuleOrObjectDef] with InnerSymbol:
  def nme = blockNme
  def toLoc: Option[Loc] = N
  override def toString: Str = s"globalThis:$blockNme${State.dbgUid(uid)}"
  
  def subst(using sub: SymbolSubst): TopLevelSymbol = sub.mapTopLevelSym(this)

