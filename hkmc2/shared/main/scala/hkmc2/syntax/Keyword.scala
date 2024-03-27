package hkmc2
package syntax

import collection.mutable
import mlscript.utils.*, shorthands.*


class Keyword(val name: String, val leftPrec: Opt[Int], val rightPrec: Opt[Int]):
  Keyword.all += name -> this

object Keyword:
  
  val all: mutable.Map[Str, Keyword] = mutable.Map.empty
  
  // val Let = Keyword("let", 0, 0)
  // val Let = Keyword("let", 0, 0)
  
  val `if` = Keyword("if", N, N)
  val `then` = Keyword("then", N, N)
  val `else` = Keyword("else", N, N)
  val `case` = Keyword("case", N, N)
  val `fun` = Keyword("fun", N, N)
  val `val` = Keyword("val", N, N)
  val `var` = Keyword("var", N, N)
  val `is` = Keyword("is", N, N)
  val `as` = Keyword("as", N, N)
  val `of` = Keyword("of", N, N)
  val `and` = Keyword("and", N, N)
  val `or` = Keyword("or", N, N)
  val `let` = Keyword("let", N, N)
  val `rec` = Keyword("rec", N, N)
  val `in` = Keyword("in", N, N)
  val `out` = Keyword("out", N, N)
  val `mut` = Keyword("mut", N, N)
  val `set` = Keyword("set", N, N)
  val `do` = Keyword("do", N, N)
  val `while` = Keyword("while", N, N)
  val `declare` = Keyword("declare", N, N)
  val `class` = Keyword("class", N, N)
  val `trait` = Keyword("trait", N, N)
  val `mixin` = Keyword("mixin", N, N)
  val `interface` = Keyword("interface", N, N)
  val `extends` = Keyword("extends", N, N)
  val `with` = Keyword("with", N, N)
  val `override` = Keyword("override", N, N)
  val `super` = Keyword("super", N, N)
  val `new` = Keyword("new", N, N)
  // val `namespace` = Keyword("namespace", N, N)
  val `module` = Keyword("module", N, N)
  val `type` = Keyword("type", N, N)
  val `where` = Keyword("where", N, N)
  val `forall` = Keyword("forall", N, N)
  val `exists` = Keyword("exists", N, N)
  val `null` = Keyword("null", N, N)
  val `undefined` = Keyword("undefined", N, N)
  val `abstract` = Keyword("abstract", N, N)
  val `constructor` = Keyword("constructor", N, N)
  val `virtual` = Keyword("virtual", N, N)
  val `true` = Keyword("true", N, N)
  val `false` = Keyword("false", N, N)
  val `public` = Keyword("public", N, N)
  val `private` = Keyword("private", N, N)
  val `=` = Keyword("=", N, N)
  
  val modifiers = Set(
    `abstract`, mut, virtual, `override`, declare, public, `private`)


