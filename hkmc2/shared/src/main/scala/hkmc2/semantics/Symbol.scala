package hkmc2
package semantics

import scala.collection.mutable
import scala.collection.mutable.Buffer

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.utils.*

import Elaborator.State
import Tree.Ident
import hkmc2.codegen.{ErasedType, ErasedResult, ErasedCallableSignature, ErasedFuncSignature, ErasedGetterSignature, ErasedValueType, HasDelayedErasedType}
import hkmc2.utils.SymbolSubst
import sourcecode.{FileName, Line}


sealed abstract class MaybeSymbol:
  
  def nme: Str
  
  def showDbg(using DebugPrinter): Str =
    this.showAsPlain

end MaybeSymbol


abstract class Symbol(using ownerState: State) extends MaybeSymbol with Located:
  
  def getState: State = ownerState
  
  val uid: Uid[Symbol] = State.suid.nextUid
  
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
    showPrefix + showName
  
  override def toString: Str =
    prefix + nme
  
  private[semantics] val directRefs: mutable.Buffer[Term.Ref] = mutable.Buffer.empty
  def ref(id: Tree.Ident =
    Tree.Ident("") // FIXME hack
  )(using currentState: State): Term.Ref =
    val res = new Term.Ref(this)(id, N).withLocOf(id)
    if currentState is ownerState then directRefs += res
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
  
  override def equals(x: Any): Bool = this is x
  override def hashCode: Int = uid.hashCode
  
  def subst(using SymbolSubst): Symbol
  
end Symbol


// * Used, eg, as the Assign receiver of intermediate computations whose result is not used
object NoSymbol extends MaybeSymbol:
  def nme: Str = "‹no symbol›"
  override def toString: Str = nme
type NoSymbol = NoSymbol.type


/** Symbols bound by `Program.imports`.
  *
  * Imports bind member symbols or immutable variable symbols. Compiler-generated
  * prelude/runtime imports use the same immutable bindings as source import aliases.
  */
type ImportSymbol = VarSymbol | BlockMemberSymbol


abstract class FlowSymbol(label: Str)(using State) extends Symbol:
  def nme: Str = label
  def toLoc: Option[Loc] = N // TODO track source trees of flows
  import flow.*
  val outFlows: mutable.Buffer[FlowSymbol] = mutable.Buffer.empty
  val consumers: mutable.Buffer[Consumer] = mutable.Buffer.empty
  val producers: mutable.Buffer[ConcreteProd] = mutable.Buffer.empty

object FlowSymbol:
  
  def apply(label: Str)(using State): FlowSymbol =
    ConcreteFlowSymbol(label)
  
  def app()(using State) =
    // FlowSymbol("‹app-res›")
    // FlowSymbol("@")
    FlowSymbol("app")
  
  def pat()(using State) =
    FlowSymbol("pat")
  
  def neww()(using State) =
    FlowSymbol("new")
  
  def sel(nme: Str)(using State) =
    FlowSymbol(s"⋅$nme")
  def synthSel(nme: Str)(using State) =
    FlowSymbol(s"(⋅)$nme")
  def selProj(nme: Str)(using State) =
    FlowSymbol(s"#⋅$nme")
  
  def memSym(sym: MemberSymbol)(using State) =
    FlowSymbol(sym.nme)
  
  def lds(nme: Str)(using State) =
    FlowSymbol(s"Ɛ⋅$nme")
  
end FlowSymbol

class ConcreteFlowSymbol(label: Str)(using State) extends FlowSymbol(label):
  def subst(using s: SymbolSubst): FlowSymbol = s.mapFlowSym(this)


sealed trait LocalSymbol extends Symbol, ShapeHost

sealed trait NamedSymbol extends Symbol:
  def name: Str
  def id: Ident
  def subst(using s: SymbolSubst): NamedSymbol

class LabelSymbol(val trm: Opt[Term], name: Str = "lbl")(using State) extends LocalSymbol:
  def nme = name
  def subst(using s: SymbolSubst): LabelSymbol = s.mapLabelSym(this)
  def toLoc = trm.flatMap(_.toLoc)
  override def prefix: Str = "label:"

/** Symbol representing a named split (join point) introduced during normalization.
  * The `body` field holds the shared split that this symbol references.
  * The `label` field is set during lowering to the corresponding LabelSymbol. */
class SplitSymbol(val body: Split, name: Str = "split")(using State) extends LocalSymbol:
  var label: Opt[LabelSymbol] = N
  def nme = name
  def subst(using s: SymbolSubst): SplitSymbol = s.mapSplitSym(this)
  def toLoc = body.toLoc
  override def prefix: Str = "split:"

type SimpleRefSymbol = LocalVarSymbol | BuiltinSymbol | LabelSymbol

sealed abstract class LocalVarSymbol(name: Str)(using State) extends FlowSymbol(name) with LocalSymbol:
  self: LocalSymbol => // * using `with LocalSymbol` in the `extends` clause makes Scala think there's a bad override
  var decl: Opt[Declaration] = N
  /** The [[ErasedValueType]] of this variable, or `N` if the erased type is not known. */
  def erasedType: Opt[ErasedValueType]
  /** Whether the binding may be reassigned after initialization. Initializing an immutable
    * binding is allowed. Forwarding an uninitialized value (e.g. as an argument) is not a use;
    * actually using it before initialization is undefined behavior. */
  def mut: Bool
  def subst(using s: SymbolSubst): LocalVarSymbol

/** A temporary variable introduced by lowering.
  *
  * An initially unknown `erasedType` may be refined once: a temp holding a branching term's result is named before
  * those branches are lowered, so `Normalization` populates it with the join of their representations once they have
  * all been seen. `Normalization.joinTempType` is its only write site.
  */
class TempSymbol(val trm: Opt[Term], initErasedType: Opt[ErasedValueType], dbgNme: Str = "tmp")(using State)
    extends LocalVarSymbol(dbgNme):
  // val nameHints: MutSet[Str] = MutSet.empty // * May be useful later?
  private var _erasedType: Opt[ErasedValueType] = initErasedType
  
  override def toLoc: Option[Loc] = trm.flatMap(_.toLoc)
  override def prefix: Str = "tmp:"
  def mut: Bool = true // TODO: support immutable temporary variables (currently the UPS assigns some)
  override def subst(using s: SymbolSubst): TempSymbol = s.mapTempSym(this)
  
  def erasedType: Opt[ErasedValueType] = _erasedType
  
  /** Refines an unknown erased type, or raises a soft assertion if a known type would be replaced. */
  def erasedType_=(newType: Opt[ErasedValueType])(using Line, FileName, Raise): Unit =
    softAssert(_erasedType.isEmpty, s"Erased type of temporary '$nme' initialized more than once")
    if _erasedType.isEmpty then _erasedType = newType


// * When instantiating forall-qualified TVs, we need to duplicate the information
// * for pretty-printing, but each instantiation should be different from each other
// * i.e., UID should be different
class InstSymbol(val origin: Symbol)(using State) extends LocalSymbol:
  override def nme: Str = origin.nme
  override def toLoc: Option[Loc] = origin.toLoc
  def subst(using sub: SymbolSubst): InstSymbol = sub.mapInstSym(this)


/** A named binding. When mut is false, its value is fixed after initialization;
  * imports and lowered immutable vals use this to retain stability through IR rewrites.
  */
class VarSymbol(val id: Ident, val mut: Bool)(using State)
    extends LocalVarSymbol(id.name)
    with HasDelayedErasedType[ErasedValueType]
    with NamedSymbol:
  def this(id: Ident, erasedType: Opt[ErasedValueType], mut: Bool)(using State) =
    this(id, mut)
    this.erasedType = erasedType
  val name: Str = id.name
  /** Alternate source spellings of this binding, populated by `Elaborator.param` when a symbolic
    * suffix is removed from its canonical name (e.g. `foo_+` becomes `foo`, with alias `foo_+`).
    * Elaboration copies these names to generated constructor fields and class-local bindings so
    * their scopes and member lookup retain both spellings. Symbol cloning/refreshing preserves them.
    */
  var sourceAliases: Ls[Str] = Nil
  override def toLoc: Opt[Loc] = id.toLoc
  // override def toString: Str = s"$name@$uid"
  override def subst(using s: SymbolSubst): VarSymbol = s.mapVarSym(this)

/** A source type binder instantiated at a static application site. Its inference
  * host starts empty: the source binder's checking witnesses and subscriptions
  * belong to the generic definition, not to any of its applications.
  *
  * `siteBinders` are the explicit type binders in scope at the instantiation
  * site, or N for a synthesized site with no source scope. The bounds published
  * to an instance are templates written at its site (supplied type arguments,
  * argument shapes observed there), so reading them through a substitution also
  * reads those binders (see NewResolver.closure).
  */
final class TypeParameterInstance(val origin: VarSymbol, val siteBinders: Opt[Set[VarSymbol]])(using State)
    extends VarSymbol(origin.id, mut = origin.mut):
  require(!origin.isInstanceOf[TypeParameterInstance], "Instantiate original type binders only")
  decl = origin.decl

object BuiltinSymbol:
  enum Arity(val paramCount: Opt[Int]):
    case Unary extends Arity(S(1))
    case Binary extends Arity(S(2))
    // `super` forwards the selected constructor's arguments, including spreads.
    case Variadic extends Arity(N)

final class BuiltinSymbol(val nme: Str, val arity: BuiltinSymbol.Arity, val isPure: Bool)(using State)
    extends Symbol:
  def toLoc: Option[Loc] = N
  override def prefix: Str = "builtin:"
  
  def subst(using sub: SymbolSubst): BuiltinSymbol = sub.mapBuiltInSym(this)
  
  def unary: Bool = arity is BuiltinSymbol.Arity.Unary
  def binary: Bool = arity is BuiltinSymbol.Arity.Binary
  def functionLike: Bool = arity is BuiltinSymbol.Arity.Variadic
  
  lazy val erasedType: ErasedValueType = ErasedType.Function(rsc = S(false))
  
  /** Each operator symbol has one calling convention. Operand types stay unknown because these are
    * dynamic host operations; in particular, arithmetic may produce numbers, strings, or big integers.
    * `super` has no fixed signature: its parameters depend on the constructor being invoked.
    */
  lazy val erasedSignature: Opt[ErasedFuncSignature] = arity.paramCount.map: count =>
    val ret = nme match
      case "!" | "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">=" => S(ErasedType.Bool)
      case "typeof" => S(ErasedType.Str)
      case _ => N
    ErasedFuncSignature.Signature(List(List.fill(count)(N)), ErasedResult.Direct(ret))
  
  // * A basic approximation of builtin operator types
  lazy val signature : semantics.flow.Producer =
    import typing.Type
    import typing.Type.*
    val typ = arity.paramCount match
      case S(count) => Fun(args = Tup.mk(List.fill(count)(Top)*), ret = Top, eff = N)
      case N => Bot
    semantics.flow.Producer.Typ(typ)


/** This is the outside-facing symbol associated to a possibly-overloaded
  * definition living in a block – e.g., a module or class.
  * `nameIsMeaningful` is `true` when the name comes from the user's source code;
  *   it is false when the name is a default given by the compiler, such as "lambda" when lifting lambdas. */
class BlockMemberSymbol(val nme: Str, val trees: Ls[TypeOrTermDef], val nameIsMeaningful: Bool = true)(using State)
    extends MemberSymbol:
  
  // * This is a hack for that `TermDef` currently doesn't have a symbol. 
  var tsym: Opt[TermSymbol] = N
  var sourceAliases: Ls[Str] = Nil
  
  private var defnListeners: Buffer[() => Unit] = Buffer.empty
  def complete(): Unit = if defnListeners isnt null then
    val listeners = defnListeners
    // Completion callbacks may request this member again. Publish completion
    // first so reentrant listeners run immediately instead of mutating the queue.
    defnListeners = null // free memory and prevent further listening
    listeners.foreach(_())
  /** Called when all the symbols covered by this BMS are present, with their definitions set. */
  def onComplete(f: () => Unit): Unit =
    if defnListeners is null then
      f()
    else
      defnListeners += f
  
  // For constructor and record fields, trees is empty because the member was
  // synthesized. Use the source location of its TermSymbol to locate diagnostics.
  def toLoc: Option[Loc] = Loc(trees).orElse(tsym.flatMap(_.toLoc))
  
  def symbols = tsym.toList ::: trees.collect:
    case t: Tree.TypeDef => t.symbol
  
  /** The headers of this symbol's definitions (see `Definition.headerLoc`), spanning from the
    * first to the last when the symbol is overloaded. Diagnostics citing a member as a witness
    * use this rather than `toLoc`, which spans the definitions' whole trees, including their bodies. */
  def headerLoc: Option[Loc] =
    Loc.mk(symbols.iterator.flatMap(_.defn.flatMap(_.headerLoc))).orElse(toLoc)
  def describe: Str =
    symbols match
    case Nil => s"symbol"
    case sym :: Nil => s"${sym.describeKind}"
    case sym1 :: sym2 :: Nil => s"overloaded ${sym1.describeKind} and ${sym2.describeKind}"
    case _ => s"overloaded ${enumerate(symbols.map(_.describeKind).ne_!, "and")}"
  
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
  
  /** Resolution publishes direct override edges; only resolver subscriptions may observe the
    * growing graph. Erasure/lowering read the completed declaration identities, never value flow.
    * The host uses the same consumer-local copies as other inference publishers on imported code.
    * These edges belong to source declarations and are consumed before/while lowering. MIR
    * symbol refreshing does not copy them: lowered selections already contain their chosen target.
    */
  private[semantics] val overrideLinks: OverrideLinks = new OverrideLinks
  def overriddenMembers(using codegen.Erasure): Ls[TermSymbol] = overrideLinks.members


class TermSymbol(val k: TermDefKind, val owner: Opt[InnerSymbol], val id: Tree.Ident)(using State)
    extends MemberSymbol
    with DefinitionSymbol[TermDefinition]
    with NamedSymbol
:
  // `null` marks source declarations not yet visited by Erasure; `N` is an initialized, unknown erasure.
  // Generated MIR symbols initialize the same slot directly, retaining signatures separately from value types.
  private var assignedErasure: Opt[ErasedValueType | ErasedCallableSignature] = null
  def this(k: TermDefKind, owner: Opt[InnerSymbol], id: Tree.Ident,
      erasure: Opt[ErasedValueType | ErasedCallableSignature])(using State) =
    this(k, owner, id)
    initializeErasure(erasure)
  
  def isErased: Bool = assignedErasure != null
  /** The erased signature stored for this definition. `N` denotes an initialized unknown erasure;
    * reading this before `initializeErasure` is an error.
    *
    * Stored value definitions use the `ErasedValueType` arm, including function-valued slots whose
    * representation is `Function`. Function definitions use the `ErasedCallableSignature` arm:
    * `ErasedFuncSignature` describes one or more physical parameter lists (including an implicit empty list),
    * while `ErasedGetterSignature` describes getters with no physical parameter list.
    *
    * For a getter, `erasedType` exposes the call result's value type, while the stored signature also
    * records the body's result and wrapper kind. For example, an async getter's body returns `Int`
    * but a read yields `Promise`; retaining only `Promise` would lose the payload representation
    * needed when lowering or cloning the body.
    */
  def erasure: Opt[ErasedValueType | ErasedCallableSignature] =
    assert(isErased, s"Erasure of '$nme' read before initialization")
    assignedErasure
  def initializeErasure(value: Opt[ErasedValueType | ErasedCallableSignature]): Unit =
    assert(!isErased, "Erasure initialized more than once")
    assert(value != null, "An initialized erasure cannot be null")
    assignedErasure = value
  
  var sourceAliases: Ls[Str] = Nil
  def nme: Str = id.name
  def name: Str = nme
  
  def toLoc: Option[Loc] = id.toLoc
  override def prefix: Str = s"term:${owner.map(o => s"${o.nme}/").getOrElse("")}"
  override def showPrefix(using Scope, ShowCfg, Raise): Str =
    "term:" + owner.map(_.showName + "/").getOrElse("")
  def isExplicitlyPrivate: Bool = defn.exists(_.visibility is Visibility.Private)
  def isPrivate: Bool =
    // Note: Top-level definitions have no owner and do not use JS private fields;
    //    They are not directly accessible from other modules in source code,
    //    but are actually exported internally under mangled names.
    //    So, we do not consider them private for the purpose of this check.
    owner.isDefined &&
      // Refreshed IR symbols have no source definition. Their current definition
      // retains visibility, including after a method is copied by the inliner.
      ((k is LetBind) || irDefn.fold(isExplicitlyPrivate)(_.visibility is Visibility.Private))
  
  /** The erased type of what a reference to this term evaluates to.
    *
    * A definition with an [[erasedSignature]] evaluates to a closure the compiler builds, i.e. a first-class
    * `Function`. The signature describes calls to the definition, not the type of that closure.
    */
  def erasedType: Opt[ErasedValueType] = erasure match
    case S(_: ErasedFuncSignature) => S(ErasedType.Function(rsc = S(false)))
    case S(sig: ErasedGetterSignature) => sig.ret
    case S(tpe: ErasedValueType) => S(tpe)
    case N => N
  
  /** The erased signature of a `fun` definition with parameter lists, or `N` if this term has none. */
  def erasedSignature: Opt[ErasedFuncSignature] = erasure match
    case S(sig: ErasedFuncSignature) => S(sig)
    case S(_: ErasedValueType | _: ErasedGetterSignature) | N => N
  
  /** Creates a symbol with the same erased type or signature as this one. */
  def withSameErasure(k: TermDefKind, owner: Opt[InnerSymbol], id: Tree.Ident)(using State): TermSymbol =
    withMappedErasure(k, owner, id)(identity)
  
  /** Creates a symbol with the same erased type as this one, or its erased signature mapped by `f`. */
  def withMappedErasure(k: TermDefKind, owner: Opt[InnerSymbol], id: Tree.Ident)
      (f: ErasedFuncSignature => ErasedFuncSignature)(using State): TermSymbol =
    val erasure = this.erasure match
      case S(sig: ErasedFuncSignature) => S(f(sig))
      case other => other
    new TermSymbol(k, owner, id, erasure)
  
  /** The complete result behavior. Value slots have a direct result; getters retain
    * their wrapper kind without acquiring a first-class function representation.
    */
  def erasedResult: ErasedResult[ErasedValueType] = erasure match
    case S(sig: ErasedCallableSignature) => sig.result
    case S(tpe: ErasedValueType) => ErasedResult.Direct(S(tpe))
    case N => ErasedResult.Direct(N)

  /** The representation seen by a caller, including async/generator wrapping. */
  def declaredResultType: Opt[ErasedValueType] = erasedResult.callType

  def subst(using sub: SymbolSubst): TermSymbol = sub.mapTermSym(this)
  def mayRaiseEffects(using Config) =
    defn.forall(_.mayRaiseEffects)

object TermSymbol:
  def fromFunBms(b: BlockMemberSymbol, owner: Opt[InnerSymbol], erasedSignature: Opt[ErasedFuncSignature])(using State) =
    TermSymbol(syntax.Fun, owner, Tree.Ident(b.nme), erasedSignature)


/** Represents the companion constructor function of parameterized classes,
  * which is the one that is accessed on plain `C` references for a definition like `class C(...)`.
  * Note that the owner of this function is NOT the class; it is the same as the class's own owner. */
class ClassCtorSymbol(
  override val k: syntax.Fun.type,
  override val owner: Opt[InnerSymbol],
  val associatedCls: ClassSymbol,
)(using State) extends TermSymbol(k, owner, associatedCls.id, N):
  // Constructor functions occupy the class binding, not a private method slot.
  // MemberStorage determines that binding's runtime privacy from the class and module.
  // Their source accessibility is checked through the class and its constructor modifiers.
  override def isPrivate: Bool = false
  override def subst(using sub: SymbolSubst): ClassCtorSymbol = sub.mapClassCtorSym(this)
  override def mayRaiseEffects(using Config) =
    super.mayRaiseEffects || config.checkInstantiateEffect


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
  def apply(lit: Literal)(using State): LitSymbol =
    State.literalSymbols.getOrElseUpdate(lit, new LitSymbol(lit){})


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
  def defn: Opt[ClassLikeDef]
  val tree: Tree.TypeDef
  def subst(using sub: SymbolSubst): ClassLikeSymbol

  /** Published by erasure before class bodies are lowered, including for external declarations.
    * Full IR class definitions attach companion modules to their containing class and refresh
    * these headers when rewritten, just as they own `irDefn`.
    * Keeping the header separately is necessary for forward parents and declarations without
    * executable bodies; consumers must not reconstruct it from semantic terms.
    */
  var irClassHeader: Opt[codegen.ClassHeader] = N
  def irTermCompanion: Opt[TermSymbol] = irClassHeader.flatMap(_.termCompanion)


type AnyDefinitionSymbol = DefinitionSymbol[?]

/** Symbols that own a class, module, object, or pattern body; excludes the synthetic top-level receiver. */
type ClassLikeDefSymbol = ClassSymbol | ModuleOrObjectSymbol | PatternSymbol

/**
 * A symbol for entities with a definition.
 *
 * This is different from `MemberSymbol` because `BlockMemberSymbol` extends `MemberSymbol`, and its
 * definition is ambiguous in the sense that a `BlockMemberSymbol` corresponds to multiple
 * overloaded definitions. In contrast, a `DefinitionSymbol` corresponds to only one specific
 * definition.
 */
sealed trait DefinitionSymbol[Defn <: Definition] extends MemberSymbol:
  
  private var _defn: Opt[Defn] = N
  def defn: Opt[Defn] = _defn
  def defn_=(d: S[Defn]): Unit =
    require(_defn.isEmpty, s"Cannot reassign defn of ${this} from ${_defn} to ${d}")
    _defn = d
    defnListeners.foreach(_(d.value))
    defnListeners = null // free memory and prevent further listening
  
  var decl: Opt[Declaration] = N // NOTE: currently only assigned for class params and only used by deforestation; may want to just remove it once deforestation is improved
  def bms: Opt[BlockMemberSymbol] = defn.map(_.bsym) 
  
  // TODO: rm
  private[semantics] var defnListeners: Buffer[Defn => Unit] = Buffer.empty
  
  // * Although the IR is immutable,
  // * we consider that a given symbol is *owned* by the IR Defn node that defines it.
  var irDefn: Opt[codegen.Defn] = N
  def irFunDefn: Opt[codegen.FunDefn] = irDefn.collectFirst:
    case fd: codegen.FunDefn => fd
  def irClsLikeDefn: Opt[codegen.ClsLikeDefn] = irDefn.collectFirst:
    case cd: codegen.ClsLikeDefn => cd
  
  /** Whether we know it's pure when selected (eg getters are not always pure). */
  def isAccessPure: Bool =
    this match
    case _: ModuleOrObjectSymbol => true
    case _ =>
      defn.exists:
        case d: ClassDef => true
        case TermDefinition(k = syntax.MutVal) => false
        case TermDefinition(k = _: syntax.ValLike) => true
        case d @ TermDefinition(k = syntax.Fun, params = Nil) => !d.mayRaiseEffects
        case TermDefinition(k = syntax.Fun, params = _ :: _) =>
          true // References to functions are only guaranteed to be pure when the functions have parameter lists
        case _ => false
  
  def subst(using sub: SymbolSubst): DefinitionSymbol[Defn]
  
  def describeKind: Str =
    this match
    case sym: ClassSymbol => s"class"
    case sym: ModuleOrObjectSymbol => if sym.tree.k is Mod then "module" else "object"
    case sym: TypeAliasSymbol => "type alias"
    case sym: PatternSymbol => "pattern"
    case sym: TermSymbol => sym.k.desc
  
end DefinitionSymbol

/** Symbols denoting receivers in semantic terms and IR. Unlike inner receivers,
  * the global object has no class-like definition, private scope, or captured-this proxy. */
sealed trait ThisSymbol extends Symbol:
  def subst(using SymbolSubst): ThisSymbol

/** This is the symbol associated to specific definitions.
  * One overloaded `BlockMemberSymbol` may correspond to multiple `InnerSymbol`s
  * A `Ref(_: InnerSymbol)` represents a `this`-like reference to the current object. */
  // TODO prevent from appearing in Ref
sealed trait InnerSymbol(using State) extends ThisSymbol, ShapePublisher:
  // Ideally, InnerSymbol should extend DefinitionSymbol, but that requires us to specify the type
  // parameter to all occurrences of InnerSymbol. So, we use a self-type annotation instead to
  // ensure that any implementation of InnerSymbol is also a DefinitionSymbol.
  self: DefinitionSymbol[? <: ClassLikeDef] =>
  val privatesScope: Scope = Scope.empty(Scope.Cfg.default) // * Scope for private members of this symbol
  /** The IR class containing this owner's members, shared by instance and static receivers.
    * This is needed because in the IR,
    * a module actually stores its members as static members of its companion class. */
  def irClassContainer: InnerSymbol =
    asClsOrMod.flatMap(_.irClassHeader.flatMap(_.companionClass)).getOrElse(this)
  // TODO(Derppening): Can we meaningfully infer the erased type of `this` from the definition?
  val thisProxy: TempSymbol = TempSymbol(N, initErasedType = N, s"this$$$nme")
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

  /** The [[ErasedValueType]] of this module or object. */
  val erasedType: Opt[ErasedValueType] = S(ErasedType.ValueLike(rsc = S(false), this))
  
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

  /** The fixed-point machine compiled from this definition, memoized across
    * `@compile` match sites (see `ups.FixedPointCompiler`). */
  var fixedPointMachine: Opt[ups.FixedPointCompiler.Machine] = N

  override def subst(using sub: SymbolSubst): PatternSymbol = sub.mapPatSym(this)

class TopLevelSymbol(blockNme: Str)(using State)
    extends ThisSymbol:
  def nme = blockNme
  def toLoc: Option[Loc] = N
  override def prefix: Str = "globalThis:"
  
  def subst(using sub: SymbolSubst): TopLevelSymbol = sub.mapTopLevelSym(this)
