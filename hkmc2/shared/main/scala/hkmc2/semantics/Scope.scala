package hkmc2
package semantics

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import syntax.*


// TODO move to codegen

type Scoped[A] = Scope ?=> A

class Scope(val name: Str, enclosing: Opt[Scope]):
  private val symbolTable = mutable.HashMap.empty[Str, Symbol]

// class Scope(val name: Str, enclosing: Opt[Scope], symbolTable: Map[Str, Symbol]):
//   ()

