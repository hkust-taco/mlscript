package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


abstract class Symbol extends Located:
  def children: List[Located] = Nil

class VarSymbol(val name: Str, uid: Int) extends Symbol:
  override def toString: Str = s"$name@$uid"

class ClassSymbol(val name: Str) extends Symbol


