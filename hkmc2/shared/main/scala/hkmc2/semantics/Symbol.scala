package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


abstract class Symbol extends Located

abstract class VarSymbol(val name: Str) extends Symbol

abstract class ClassSymbol(val name: Str) extends Symbol


