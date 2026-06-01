package hkmc2
package utils

import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import sourcecode.{Name, Line, FileName}

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext
import Scope.*
import hkmc2.semantics.InnerSymbol
import hkmc2.semantics.Symbol
import hkmc2.semantics.VarSymbol
import hkmc2.semantics.Elaborator
import hkmc2.semantics.TopLevelSymbol
import semantics.Elaborator.State
import hkmc2.codegen.js.JSBuilder


/** When `curThis` is N, it means this scope does not rebind `this`.
  * When `curThis` is Some(None), it means the scope rebinds `this`
  * to something unknown, following JavaScript's inane `this` handling in `function`s.
  * When `curThis` is Some(Some(sym)), it means the scope rebinds `this`
  * to an inner symbol (e.g., class or module).
  * Note: I made `Scope` a case class just so that it can benefit from `printAsTree`. */
case class Scope
    (val parentOrCfg: Cfg \/ Scope, val curThis: Opt[Opt[InnerSymbol]], private val bindings: MutMap[Symbol, Str])
    (using State):
  
  lazy val parent: Opt[Scope] = parentOrCfg.toOption
  lazy val cfg: Cfg = parentOrCfg.fold(identity, _.cfg)
  // * Track every owner whose `this` is currently in lexical scope so codegen can tell
  // * whether a private field access stays inside the declaring owner or needs an accessor.
  lazy val inScopeOwners: Set[InnerSymbol] =
    parent.fold(Set.empty[InnerSymbol])(_.inScopeOwners) ++ curThis.iterator.flatten
  
  private val existingNames = MutMap.empty[Str, Symbol]
  
  private var thisProxyAccessed = false
  lazy val thisProxy =
    curThis match
    case N | S(N) => die
    case S(S(State.globalThisSymbol)) => "globalThis"
    case S(S(thisSym)) => 
      thisProxyAccessed = true
      given Raise = throw _
      allocateName(thisSym.thisProxy)
  
  /** Whether the code generator has produced a binding for `thisProxy` yet. */
  var thisProxyDefined: Bool = false
  
  private def thisError(thisSym: InnerSymbol)(using Raise): Str =
    raise:
      InternalError(msg"`this` not in scope: ${thisSym.toString}" -> N :: Nil,
        extraInfo = Some(this, thisSym),
        source = Diagnostic.Source.Compilation)
    "‹MISSING_THIS›"
  
  def addToBindings(symbol: Symbol, name: String, shadow: Bool)(using Raise, Line, Name, FileName) =
    val fullName =
      if !shadow && lookup(symbol).nonEmpty
      then
        raise:
          InternalError(msg"`${symbol.toString}` is already in scope" -> symbol.toLoc :: Nil, extraInfo = Some(this))
        name + "‹BAD_SHADOW›"
      else name
    bindings += symbol -> fullName
    existingNames += fullName -> symbol
    fullName
  
  def getBindings: Iterator[(Symbol, String)] =
    bindings.iterator
  
  def findThis_!(thisSym: InnerSymbol)(using Raise): Str =
    // println(s"findThis_! $thisSym")
    def getParent = parent.fold(
      if thisSym.isInstanceOf[TopLevelSymbol]
      // * TopLevelSymbol scopes are special and not nested in codegen `Scope`s
      // * to avoid needlessly generating new variable names in separate blocks.
      then "this"
      else thisError(thisSym)
    )
    curThis match
    case S(S(sym: TopLevelSymbol)) if sym === State.globalThisSymbol =>
      // `this` at the top level evaluates to `undefined` in strict mode.
      // We need this because we generate some code that uses `this`/`globalThis`,
      // for example the symbol loading code.
      "globalThis"
    case S(S(`thisSym`)) => "this" // no need to qualify `this`
    case S(_) => getParent(_.findThisProxy_!(thisSym))
    case N => getParent(_.findThis_!(thisSym))
  
  def findThisProxy_!(thisSym: InnerSymbol)(using Raise): Str =
    // println(s"findThisProxy_! $thisSym")
    if thisSym.isInstanceOf[TopLevelSymbol]
    then "globalThis"
    else curThis match
      case S(S(`thisSym`)) => thisProxy
      case _ => parent.fold(thisError(thisSym))(_.findThisProxy_!(thisSym))
  
  def nest: Scope = Scope(R(this), N, MutMap.empty)
  
  def getThisScope: Opt[Scope] = curThis.fold(parent.flatMap(_.getThisScope))(_ => S(this))
  
  def getOuterThisScope: Opt[Scope] = parent.flatMap(_.getThisScope)
  
  def nestRebindThis[R](thisSym: Opt[InnerSymbol])(k: Scope ?=> R): (Opt[Str], R) =
    val nested = Scope(R(this), S(thisSym), MutMap.empty)
    val res = k(using nested)
    getOuterThisScope match
    case N => (N, res)
    case S(outer) =>
      (if outer.thisProxyAccessed then S(outer.thisProxy) else N, res)
  
  
  def inScope(name: Str): Bool =
    existingNames.contains(name) || parent.exists(_.inScope(name))
  def reverseLookup(name: Str): Opt[Symbol] =
    existingNames.get(name).orElse(parent.flatMap(_.reverseLookup(name)))
  
  def lookup(l: Symbol): Opt[Str] =
    // curThis.filter(_ is l).map(_ => thisProxy) orElse
    bindings.get(l).orElse(parent.flatMap(_.lookup(l)))
  
  def lookup_!(l: Symbol, loc: Opt[Loc])(using Raise): Str =
    lookup(l).getOrElse:
      // * Prevent long-winded error messages which quote the entire definition.
      val extraLoc = l match
        case sym: semantics.BlockMemberSymbol =>
          sym.trees.collectFirst:
            case t: syntax.Tree.TypeDef => t.head.toLoc
          .flatten.orElse(l.toLoc)
        case other => other.toLoc
      raise(ErrorReport(msg"No definition found in scope for member '${l.nme}'" -> loc ::
          (if extraLoc.isEmpty then Nil else msg"which references the symbol introduced here" -> extraLoc :: Nil),
        extraInfo = Some(l -> l.getClass -> this),
        source = Diagnostic.Source.Compilation))
      l.nme
  
  // * Note: it is sound for an existing name to have been allocated with a different prefix (which is only cosmetic)
  def allocateOrGetName(l: Symbol, prefix: Str = "")(using Raise): Str =
    lookup(l).getOrElse(allocateName(l, prefix = prefix))
  
  def allocateName(l: Symbol, prefix: Str = "", shadow: Bool = false)(using Raise, Line, Name, FileName): Str =
    
    val c = cfg
    
    // * May be useful later?
    /* 
    val base: Str = l match
      case tmp: semantics.TempSymbol if tmp.nameHints.sizeCompare(1) =/= 0 =>
        prefix + tmp.nameHints.head
      case _ => if l.nme.isEmpty && prefix.isEmpty then "tmp" else prefix + l.nme
    */
    val base = if l.nme.isEmpty && prefix.isEmpty then c.defaultName else prefix + l.nme
    
    val realBase = if cfg.escapeChars
      then Scope.replaceInvalidCharacters(base)
      else base
    
    val name =
      // Try just realBase.
      if !c.includeZero && !inScope(realBase) && !JSBuilder.keywords.contains(realBase) && realBase.nonEmpty
      then realBase
      else
        // Try realBase with an integer.
        ((if c.includeZero then 0 else 1) to Int.MaxValue).iterator
          .map: i =>
            val idx =
              if c.useSuperscripts
              then i.toString.map:
                case '0' => '⁰'
                case '1' => '¹'
                case '2' => '²'
                case '3' => '³'
                case '4' => '⁴'
                case '5' => '⁵'
                case '6' => '⁶'
                case '7' => '⁷'
                case '8' => '⁸'
                case '9' => '⁹'
                case _ => die
              else i.toString
            s"$realBase$idx"
          .filterNot(inScope).next()
    
    val fullName = addToBindings(l, name, shadow = shadow)
    
    fullName


object Scope:
  
  case class Cfg(escapeChars: Bool, useSuperscripts: Bool, includeZero: Bool, defaultName: Str)
  object Cfg:
    val default = Cfg(escapeChars = true, useSuperscripts = false, includeZero = false, defaultName = "tmp")
  end Cfg
  
  def scope(using scp: Scope): Scope = scp
  
  def empty(cfg: Cfg)(using State): Scope =
    Scope(L(cfg), S(S(State.globalThisSymbol)), MutMap.empty)
  
  def replaceInvalidCharacters(str: Str): Str =
    str.iterator.map:
        case c if c.isLetter || c.isDigit => c
        // case '\'' => "$tick"
        case '$' => "$"
        case '_' => "_"
        case _ => "$_"
      .mkString
  
end Scope

