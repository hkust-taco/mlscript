package hkmc2
package semantics

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import syntax.*


type Scoped[A] = Scope ?=> A

class Scope(val name: Str, enclosing: Opt[Scope]):
  private val symbolTable = mutable.HashMap.empty[Str, Symbol]
  

