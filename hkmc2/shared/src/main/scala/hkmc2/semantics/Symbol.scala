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
  
  def showDbg(using DebugPrinter): Str =
    this.showAsPlain
  
  def showPlainName(using scp: Scope): hkmc2.document.Document =
    import hkmc2.document.*
    scp.allocateOrGetName(this)(using throw _)
  
  def showName(using scp: Scope, cfg: ShowCfg)(using Raise): Str =
    cfg.shownSymbols += this
    import hkmc2.document.*
    val name = nme
    if cfg.showFlowSymbols
    then s"$name${scp.allocateOrGetName(this).stripPrefix(name)}"
    else name
  
  def prefix: Str = ""
  
  def showPrefix(using Scope, ShowCfg, Raise): Str = prefix
  
  def showFullName(using Scope, ShowCfg, Raise): Str =
    showPrefix + showName + State.dbgUid(uid)
  
  override def toString: Str =
    prefix + nme + State.dbgUid(uid)
  
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
  
  // * This is a hack for that `TermDef` currently doesn't have a symbol. 
  // * So, the symbol is from the `TermDefinition`. 
  def asTrm: Opt[TermSymbol] = this match
    case trm: TermSymbol => S(trm)
    case mem: BlockMemberSymbol => mem.tsym
    case _ => N
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
    .orElse[TypeSymbol](asObj)
    .orElse[TypeSymbol](asAls)
    .orElse[TypeSymbol](asMod)
  def asNonModTpe: Opt[TypeSymbol] = asCls
    .orElse[TypeSymbol](asObj)
    .orElse[TypeSymbol](asAls)
  
  def asBlkMember: Opt[BlockMemberSymbol] = this match
    case mem: BlockMemberSymbol => S(mem)
    case mem: DefinitionSymbol[?] => mem.defn match
      case S(defn: TypeLikeDef) => S(defn.bsym)
      case S(defn: TermDefinition) => S(defn.bsym)
      case N => N
    case _ => N
  
  /** Get the symbol corresponding to the "representative" of a set of overloaded definitions,
    * or the sole definition, if it is not overloaded.
    * We should consider the ordering terms > classes/objects/types > modules, for this purpose. */
  def asPrincipal: Opt[TermSymbol | ClassSymbol | ModuleOrObjectSymbol | TypeAliasSymbol | PatternSymbol] =
    val asTrm: Opt[TermSymbol | ClassSymbol | ModuleOrObjectSymbol | TypeAliasSymbol | PatternSymbol] = this.asTrm
    asTrm orElse
    asCls orElse
    asObj orElse
    asAls orElse
    asPat orElse
    asMod
  
  def orElseDisamb(disamb: Opt[DefinitionSymbol[?]]): Symbol = (this, disamb) match
    case (bms: BlockMemberSymbol, S(disamb)) =>
      disamb
    case (bms: BlockMemberSymbol, N) =>
      lastWords(s"Cannot disambiguate overloaded member symbol ${bms.nme}: no disambiguation provided")
    case (sym, N) =>
      sym
    case (sym, S(_)) =>
      lastWords(s"Cannot disambiguate non-BlockMember symbol ${sym.nme}: disambiguation provided")
  
  override def equals(x: Any): Bool = this is x
  override def hashCode: Int = uid.hashCode
  
  def subst(using SymbolSubst): Symbol
  
end Symbol


// * Used, eg, as the Assign receiver of intermediate computations whose result is not used
final class NoSymbol(using State) extends Symbol:
  def nme: Str = "‹no symbol›"
  def toLoc: Option[Loc] = N
  def subst(using s: SymbolSubst): NoSymbol = this


class FlowSymbol(label: Str)(using State) extends Symbol:
  def nme: Str = label
  def toLoc: Option[Loc] = N // TODO track source trees of flows
  import flow.*
  val outFlows: mutable.Buffer[FlowSymbol] = mutable.Buffer.empty
  val consumers: mutable.Buffer[Consumer] = mutable.Buffer.empty
  val producers: mutable.Buffer[ConcreteProd] = mutable.Buffer.empty
  def showDbg: Str =
    label + s"‹$uid›"
  def subst(using s: SymbolSubst): FlowSymbol = s.mapFlowSym(this)

object FlowSymbol:
  
  def app()(using State) =
    // FlowSymbol("‹app-res›")
    // FlowSymbol("@")
    FlowSymbol("app")

  def sel(nme: Str)(using State) =
    FlowSymbol(s"⋅$nme")
  def synthSel(nme: Str)(using State) =
    FlowSymbol(s"(⋅)$nme")
  def selProj(nme: Str)(using State) =
    FlowSymbol(s"#⋅$nme")

  def lds(nme: Str)(using State) =
    FlowSymbol(s"Ɛ⋅$nme")
  
end FlowSymbol

sealed trait LocalVarSymbol extends LocalSymbol
sealed trait LocalSymbol extends Symbol:
  def subst(using s: SymbolSubst): LocalSymbol
sealed trait NamedSymbol extends Symbol:
  def name: Str
  def id: Ident
  def subst(using s: SymbolSubst): NamedSymbol

class LabelSymbol(val trm: Opt[Term], name: Str = "lbl")(using State) extends LocalSymbol:
  def nme = name
  def subst(using s: SymbolSubst): LabelSymbol = s.mapLabelSym(this)
  def toLoc = trm.flatMap(_.toLoc)
  override def prefix: Str = "label:"

abstract class BlockLocalSymbol(name: Str)(using State) extends FlowSymbol(name):
  self: LocalSymbol => // * using `with LocalSymbol` in the `extends` clause makes Scala think there's a bad override
  var decl: Opt[Declaration] = N

class TempSymbol(val trm: Opt[Term], dbgNme: Str = "tmp")(using State) extends BlockLocalSymbol(dbgNme) with LocalVarSymbol:
  // val nameHints: MutSet[Str] = MutSet.empty // * May be useful later?
  override def toLoc: Option[Loc] = trm.flatMap(_.toLoc)
  override def prefix: Str = "tmp:"
  override def subst(using s: SymbolSubst): TempSymbol = s.mapTempSym(this)


// * When instantiating forall-qualified TVs, we need to duplicate the information
// * for pretty-printing, but each instantiation should be different from each other
// * i.e., UID should be different
class InstSymbol(val origin: Symbol)(using State) extends LocalSymbol:
  override def nme: Str = origin.nme
  override def toLoc: Option[Loc] = origin.toLoc
  def subst(using sub: SymbolSubst): InstSymbol = sub.mapInstSym(this)


class VarSymbol(val id: Ident)(using State) extends BlockLocalSymbol(id.name) with NamedSymbol with LocalVarSymbol:
  val name: Str = id.name
  override def toLoc: Opt[Loc] = id.toLoc
  // override def toString: Str = s"$name@$uid"
  override def subst(using s: SymbolSubst): VarSymbol = s.mapVarSym(this)

class BuiltinSymbol
    (val nme: Str, val binary: Bool, val unary: Bool, val nullary: Bool, val functionLike: Bool)(using State)
    extends Symbol:
  def toLoc: Option[Loc] = N
  override def prefix: Str = "builtin:"
  
  def subst(using sub: SymbolSubst): BuiltinSymbol = sub.mapBuiltInSym(this)
  
  def isPure: Bool = true // * For now, all builtins are pure
  
  // * A basic approximation of builtin operator types
  lazy val signature : semantics.flow.Producer =
    import typing.Type
    import typing.Type.*
    val binaryType : Type = Fun(args = Tup.mk(Top, Top), ret = Top, eff = N)
    val unaryType : Type = Fun(args = Tup.mk(Top), ret = Top, eff = N)
    val nullaryType : Type = Top
    val typ = (binary, unary, nullary) match
      case (true, true, true) => Union(binaryType, Union(unaryType, nullaryType))
      case (true, true, _) => Union(binaryType, unaryType)
      case (true, _, true) => Union(binaryType, nullaryType)
      case (_, true, true) => Union(unaryType, nullaryType)
      case (true, _, _) => binaryType
      case (_, true, _) => unaryType
      case (_, _, true) => nullaryType
      case _ => Bot
    semantics.flow.Producer.Typ(typ)


/** This is the outside-facing symbol associated to a possibly-overloaded
  * definition living in a block – e.g., a module or class.
  * `nameIsMeaningful` is `true` when the name comes from the user's source code;
  *   it is false when the name is a default given by the compiler, such as "lambda" when lifting lambdas. */
class BlockMemberSymbol(val nme: Str, val trees: Ls[TypeOrTermDef], val nameIsMeaningful: Bool = true)(using State)
    extends MemberSymbol:
  
  // * This is a hack for that `TermDef` currently doesn't have a symbol. 
  var tsym: Opt[TermSymbol] = N
  
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
  
  override def prefix: Str = "member:"
  
  def subst(using sub: SymbolSubst): BlockMemberSymbol = sub.mapBlockMemberSym(this)
  
  // * The flow of this symbol, when interpreted as a term (assuming no disambiguation)
  lazy val flow: FlowSymbol = FlowSymbol(s"flow:$nme")(using getState)
  
end BlockMemberSymbol


sealed abstract class MemberSymbol(using State) extends Symbol:
  def nme: Str
  def subst(using SymbolSubst): MemberSymbol


class TermSymbol(val k: TermDefKind, val owner: Opt[InnerSymbol], val id: Tree.Ident)(using State)
    extends MemberSymbol
    with DefinitionSymbol[TermDefinition]
    with LocalSymbol
    with NamedSymbol:
  def nme: Str = id.name
  def name: Str = nme
  
  def toLoc: Option[Loc] = id.toLoc
  override def prefix: Str = s"term:${owner.map(o => s"${o.nme}/").getOrElse("")}"
  override def showPrefix(using Scope, ShowCfg, Raise): Str =
    "term:" + owner.map(_.showName + "/").getOrElse("")
  
  def subst(using sub: SymbolSubst): TermSymbol = sub.mapTermSym(this)


class ClassCtorSymbol(
  override val k: syntax.Fun.type,
  override val owner: S[ClassSymbol],
  id: Tree.Ident
)(using State) extends TermSymbol(k, owner, id):
  override def subst(using sub: SymbolSubst): ClassCtorSymbol = sub.mapClassCtorSym(this)


object TermSymbol:
  def fromFunBms(b: BlockMemberSymbol, owner: Opt[InnerSymbol])(using State) =
    TermSymbol(syntax.Fun, owner, Tree.Ident(b.nme))


sealed trait CtorSymbol extends Symbol:
  def nme: Str
  def subst(using sub: SymbolSubst): CtorSymbol = sub.mapCtorSym(this)

case class Extr(isTop: Bool)(using State) extends CtorSymbol:
  def nme: Str = if isTop then "Top" else "Bot"
  def toLoc: Option[Loc] = N
  override def toString: Str = nme

sealed abstract case class LitSymbol(lit: Literal)(using State) extends CtorSymbol:
  def nme: Str = lit.idStr
  def toLoc: Option[Loc] = lit.toLoc
  override def prefix: Str = "lit:"
object LitSymbol:
  val cache: mutable.Map[Literal, LitSymbol] = mutable.Map.empty
  def apply(lit: Literal)(using State): LitSymbol =
    cache.getOrElseUpdate(lit, new LitSymbol(lit){})


/** A TypeSymbol that is not an alias. */
type BaseTypeSymbol = ClassSymbol | ModuleOrObjectSymbol

type TypeSymbol = BaseTypeSymbol | TypeAliasSymbol

/**
  * ErrorSymbol is a placeholder symbol denoting error (during symbol
  * resolution in the elaborator / resolver). This helps prevent the
  * same error from throwing multiple times.
  */
case class ErrorSymbol(val nme: Str, tree: Tree)(using State) extends MemberSymbol:
  override def toLoc: Option[Loc] = tree.toLoc
  override def subst(using sub: SymbolSubst): ErrorSymbol = sub.mapErrorSym(this)
  override def prefix: Str = "error:"

sealed trait ClassLikeSymbol extends IdentifiedSymbol:
  self: MemberSymbol & DefinitionSymbol[? <: ClassDef | ModuleOrObjectDef] =>
  val tree: Tree.TypeDef
  def subst(using sub: SymbolSubst): ClassLikeSymbol


/**
 * A symbol for entities with a definition.
 *
 * This is different from `MemberSymbol` because `BlockMemberSymbol` extends `MemberSymbol`, and its
 * definition is ambiguous in the sense that a `BlockMemberSymbol` corresponds to multiple
 * overloaded definitions. In contrast, a `DefinitionSymbol` corresponds to only one specific
 * definition.
 */
sealed trait DefinitionSymbol[Defn <: Definition] extends Symbol:
  this: MemberSymbol =>
  
  var defn: Opt[Defn] = N
  var decl: Opt[Declaration] = N // NOTE: currently only assigned for class params and only used by deforestation; may want to just remove it once deforestation is improved
  def bms: Opt[BlockMemberSymbol] = defn.map(_.bsym) 
  
  /** Whether we know it's pure when selected (eg getters are not always pure). */
  def isPure: Bool =
    this match
    case _: ModuleOrObjectSymbol => true
    case _ =>
      defn.exists:
        case d: ClassDef => true
        case TermDefinition(k = _: syntax.ValLike) => true
        case TermDefinition(k = syntax.Fun, params = _ :: _) =>
          true // References to functions are only guaranteed to be pure when the functions have parameter lists
        case _ => false
  
  def subst(using sub: SymbolSubst): DefinitionSymbol[Defn]
  
  def asMemSym: MemberSymbol = this
  
end DefinitionSymbol

/** This is the symbol associated to specific definitions.
  * One overloaded `BlockMemberSymbol` may correspond to multiple `InnerSymbol`s
  * A `Ref(_: InnerSymbol)` represents a `this`-like reference to the current object. */
  // TODO prevent from appearing in Ref
sealed trait InnerSymbol(using State) extends Symbol:
  // Ideally, InnerSymbol should extend DefinitionSymbol, but that requires us to specify the type
  // parameter to all occurrences of InnerSymbol. So, we use a self-type annotation instead to
  // ensure that any implementation of InnerSymbol is also a DefinitionSymbol.
  self: DefinitionSymbol[? <: ClassLikeDef] =>
  val privatesScope: Scope = Scope.empty(Scope.Cfg.default) // * Scope for private members of this symbol
  val thisProxy: TempSymbol = TempSymbol(N, s"this$$$nme")
  def subst(using SymbolSubst): InnerSymbol
  def asDefnSym: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol = this match
    case d: DefinitionSymbol[? <: ClassLikeDef] => d

trait IdentifiedSymbol extends Symbol:
  val id: Tree.Ident

class ClassSymbol(val tree: Tree.TypeDef, val id: Tree.Ident)(using State)
    extends MemberSymbol
    with ClassLikeSymbol
    with CtorSymbol
    with DefinitionSymbol[ClassDef]
    with InnerSymbol
    with NamedSymbol:

  def name: Str = nme
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of classe here
  override def prefix: Str = "class:"
  /** Compute the arity. */
  def arity: Int = tree.paramLists.headOption.fold(0)(_.fields.length)
  
  override def subst(using sub: SymbolSubst): ClassSymbol = sub.mapClsSym(this)

class ModuleOrObjectSymbol(val tree: Tree.TypeDef, val id: Tree.Ident)(using State)
    extends MemberSymbol
    with ClassLikeSymbol
    with CtorSymbol
    with DefinitionSymbol[ModuleOrObjectDef]
    with InnerSymbol
    with NamedSymbol:
  def name: Str = nme
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of module here
  override def prefix: Str =
    if tree.k is Obj then "object:"
    else "module:"

  override def subst(using sub: SymbolSubst): ModuleOrObjectSymbol = sub.mapModuleSym(this)

class TypeAliasSymbol(val id: Tree.Ident)(using State)
    extends MemberSymbol
    with DefinitionSymbol[TypeDef]:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of type alias here
  override def prefix: Str = "type:"

  def subst(using sub: SymbolSubst): TypeAliasSymbol = sub.mapTypeAliasSym(this)

class PatternSymbol(val id: Tree.Ident, val params: Opt[Tree.Tup], val body: Tree)(using State)
    extends MemberSymbol
    with CtorSymbol
    with DefinitionSymbol[PatternDef]
    with InnerSymbol:
  def nme = id.name
  def toLoc: Option[Loc] = id.toLoc // TODO track source tree of pattern here
  override def prefix: Str = "pattern:"
  
  override def subst(using sub: SymbolSubst): PatternSymbol = sub.mapPatSym(this)

class TopLevelSymbol(blockNme: Str)(using State)
    extends MemberSymbol
    with DefinitionSymbol[ModuleOrObjectDef]
    with InnerSymbol:
  def nme = blockNme
  def toLoc: Option[Loc] = N
  override def prefix: Str = "globalThis:"
  
  def subst(using sub: SymbolSubst): TopLevelSymbol = sub.mapTopLevelSym(this)

