package hkmc2
package codegen
package js

import scala.collection.mutable.{Map => MutMap}

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext
import Scope.*


class Scope(val parent: Opt[Scope], val bindings: MutMap[Local, Str]):
  
  def nest: Scope = Scope(Some(this), MutMap.empty)
  
  def inScope(name: Str): Bool =
    bindings.valuesIterator.contains(name) || parent.exists(_.inScope(name))
  
  def lookup(l: Local): Opt[Str] =
    bindings.get(l).orElse(parent.flatMap(_.lookup(l)))
  
  def lookup_!(l: Local)(using Raise): Str =
    lookup(l).getOrElse:
      raise(InternalError(msg"Not in scope: ${l.toString}" -> l.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      l.nme
  
  def allocateName(l: Local): Str =
    
    val prefix: Str = l match
      case tmp: semantics.TempSymbol if tmp.nameHints.sizeCompare(1) === 0 =>
        tmp.nameHints.head
      case _ => if l.nme.isEmpty then "tmp" else l.nme
    
    val realPrefix = Scope.replaceTicks(prefix)
    
    val name =
      // Try just prefix.
      if !inScope(realPrefix) && !JSBuilder.keywords.contains(realPrefix) then realPrefix
      else
        // Try prefix with an integer.
        (1 to Int.MaxValue).iterator.map(i => s"$realPrefix$i").filterNot(inScope).next
    
    bindings += l -> name
    
    name


object Scope:
  
  def scope(using scp: Scope): Scope = scp
  
  def empty: Scope = Scope(None, MutMap.empty)
  
  def replaceTicks(str: Str): Str = str.replace('\'', '$')
  
end Scope


