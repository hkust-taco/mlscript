package hkmc2
package codegen
package js

import scala.collection.mutable.{Map => MutMap}

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext
import Scope.*
import hkmc2.semantics.MemberSymbol
import hkmc2.semantics.VarSymbol


class Scope(val parent: Opt[Scope], val curThis: Opt[MemberSymbol[?]], val bindings: MutMap[Local, Str]):
  
  private var thisProxyAccessed = false
  lazy val thisProxy =
    thisProxyAccessed = true
    allocateName(curThis.get, "this$")
  
  private def thisError(thisSym: MemberSymbol[?])(using Raise): Nothing =
    raise(InternalError(msg"`this` not in scope: ${thisSym.toString}" -> N :: Nil,
      source = Diagnostic.Source.Compilation))
    die
  
  def findThis_!(thisSym: MemberSymbol[?])(using Raise): Str =
    curThis match
      case S(`thisSym`) => "this" // no need to qualify `this`
      case S(_) => parent.fold(thisError(thisSym))(_.findThisProxy_!(thisSym))
      case N => parent.fold(thisError(thisSym))(_.findThis_!(thisSym))
  
  def findThisProxy_!(thisSym: MemberSymbol[?])(using Raise): Str =
    curThis match
      case S(`thisSym`) => thisProxy
      case _ => parent.fold(thisError(thisSym))(_.findThisProxy_!(thisSym))
  
  def nest: Scope = Scope(Some(this), N, MutMap.empty)
  
  def getOuterThisScope: Opt[Scope] =
    curThis.fold(parent)(thisSym => parent.flatMap(_.getOuterThisScope))
  
  def nestRebindThis[R](thisSym: MemberSymbol[?])(k: Scope ?=> R): (Opt[Str], R) =
    val nested = Scope(Some(this), S(thisSym), MutMap.empty)
    val res = k(using nested)
    getOuterThisScope match
    case N => (N, res)
    case S(outer) =>
      (if outer.thisProxyAccessed then S(outer.thisProxy) else N, res)
  
  def inScope(name: Str): Bool =
    bindings.valuesIterator.contains(name) || parent.exists(_.inScope(name))
  
  def lookup(l: Local): Opt[Str] =
    bindings.get(l).orElse(parent.flatMap(_.lookup(l)))
  
  def lookup_!(l: Local)(using Raise): Str =
    lookup(l).getOrElse:
      raise(InternalError(msg"Not in scope: ${l.toString}" -> l.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      l.nme
  
  def allocateName(l: Local, prefix: Str = ""): Str =
    
    val base: Str = l match
      case tmp: semantics.TempSymbol if tmp.nameHints.sizeCompare(1) === 0 =>
        prefix + tmp.nameHints.head
      case _ => if l.nme.isEmpty && prefix.isEmpty then "tmp" else prefix + l.nme
    
    val realBase = Scope.replaceTicks(base)
    
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
  
  def empty: Scope = Scope(N, N, MutMap.empty)
  
  def replaceTicks(str: Str): Str = str.replace('\'', '$')
  
end Scope


