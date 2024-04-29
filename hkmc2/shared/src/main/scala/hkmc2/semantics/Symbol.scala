package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


abstract class Symbol extends Located:
  def children: List[Located] = Nil

class VarSymbol(val name: Str, uid: Int) extends Symbol:
  override def toString: Str = s"$name@$uid"

abstract class MemberSymbol extends Symbol

// No name means it's a built-in operator symbol
class TermSymbol(val name: Opt[Tree.Ident]) extends MemberSymbol:
  override def toString: Str = s"${name.getOrElse("<builtin>")}"

class ClassSymbol(val name: Str) extends Symbol


