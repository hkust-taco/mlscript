package hkmc2
package utils

import scala.collection.mutable.{Map => MutMap}

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext
import Scope.*
import hkmc2.semantics.InnerSymbol
import hkmc2.semantics.VarSymbol
import hkmc2.semantics.Elaborator
import hkmc2.semantics.TopLevelSymbol
import semantics.Elaborator.State
import hkmc2.codegen.Local
import hkmc2.codegen.js.JSBuilder


/** When `curThis`, it means this scope does not rebind `this`.
  * When `curThis` is Some(None), it means the scope rebinds `this`
  * to something unknown, following JavaScript's inane `this` handling in `function`s.
  * When `curThis` is Some(Some(sym)), it means the scope rebinds `this`
  * to an inner symbol (e.g., class or module). */
class Scope
    (val parent: Opt[Scope], val curThis: Opt[Opt[InnerSymbol]], val bindings: MutMap[Local, Str])
    (using State):
  
  private var thisProxyAccessed = false
  lazy val thisProxy =
    curThis match
    case N | S(N) => die
    case S(S(State.globalThisSymbol)) => "globalThis"
    case S(S(thisSym)) => 
      thisProxyAccessed = true
      allocateName(thisSym, "this$")
  
  /** Whether the code generator has produced a binding for `thisProxy` yet. */
  var thisProxyDefined: Bool = false
  
  private def thisError(thisSym: InnerSymbol)(using Raise): Nothing =
    raise(InternalError(msg"`this` not in scope: ${thisSym.toString}" -> N :: Nil,
      source = Diagnostic.Source.Compilation))
    die
  
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
  
  def nest: Scope = Scope(Some(this), N, MutMap.empty)
  
  def getThisScope: Opt[Scope] = curThis.fold(parent.flatMap(_.getThisScope))(_ => S(this))
  
  def getOuterThisScope: Opt[Scope] = parent.flatMap(_.getThisScope)
  
  def nestRebindThis[R](thisSym: Opt[InnerSymbol])(k: Scope ?=> R): (Opt[Str], R) =
    val nested = Scope(Some(this), S(thisSym), MutMap.empty)
    val res = k(using nested)
    getOuterThisScope match
    case N => (N, res)
    case S(outer) =>
      (if outer.thisProxyAccessed then S(outer.thisProxy) else N, res)
  
  // TODO more efficient!
  def inScope(name: Str): Bool =
    bindings.valuesIterator.contains(name) || parent.exists(_.inScope(name))
  
  def lookup(l: Local): Opt[Str] =
    // curThis.filter(_ is l).map(_ => thisProxy) orElse
    bindings.get(l).orElse(parent.flatMap(_.lookup(l)))
  
  def lookup_!(l: Local)(using Raise): Str =
    lookup(l).getOrElse:
      raise(InternalError(msg"Not in scope: ${l.toString} (${l.getClass.toString})" -> l.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      l.nme
  
  def allocateName(l: Local, prefix: Str = ""): Str =
    
    val base: Str = l match
      case tmp: semantics.TempSymbol if tmp.nameHints.sizeCompare(1) === 0 =>
        prefix + tmp.nameHints.head
      case _ => if l.nme.isEmpty && prefix.isEmpty then "tmp" else prefix + l.nme
    
    val realBase = Scope.replaceInvalidCharacters(base)
    
    val name =
      // Try just realBase.
      if !inScope(realBase) && !JSBuilder.keywords.contains(realBase) then realBase
      else
        // Try realBase with an integer.
        (1 to Int.MaxValue).iterator.map(i => s"$realBase$i").filterNot(inScope).next
    
    bindings += l -> name
    
    name


object Scope:
  
  def scope(using scp: Scope): Scope = scp
  
  def empty(using State): Scope =
    Scope(N, S(S(State.globalThisSymbol)), MutMap.empty)
  
  def replaceInvalidCharacters(str: Str): Str =
    str.iterator.map:
        case c if c.isLetter || c.isDigit => c
        // case '\'' => "$tick"
        case '$' => "$"
        case _ => "$_"
      .mkString
  
end Scope


