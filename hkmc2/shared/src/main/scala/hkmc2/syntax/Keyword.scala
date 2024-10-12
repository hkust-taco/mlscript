package hkmc2
package syntax

import collection.mutable
import mlscript.utils.*, shorthands.*


class Keyword(val name: String, val leftPrec: Opt[Int], val rightPrec: Opt[Int]):
  Keyword.all += name -> this
  def assumeLeftPrec: Int = leftPrec.getOrElse(lastWords(s"$this does not have left precedence"))
  def assumeRightPrec: Int = rightPrec.getOrElse(lastWords(s"$this does not have right precedence"))
  def leftPrecOrMin: Int = leftPrec.getOrElse(Int.MinValue)
  def rightPrecOrMin: Int = rightPrec.getOrElse(Int.MaxValue)
  override def toString: Str = s"keyword '$name'"

object Keyword:
  def unapply(kw: Keyword): Opt[Str] = S(kw.name)
  
  val all: mutable.Map[Str, Keyword] = mutable.Map.empty
  
  // val Let = Keyword("let", 0, 0)
  // val Let = Keyword("let", 0, 0)
  
  private var _curPrec = 2
  private def curPrec: S[Int] = S(_curPrec)
  private def nextPrec: S[Int] =
    val res = _curPrec
    _curPrec += 1
    S(res)

  val `class` = Keyword("class", N, curPrec)
  
  val eqPrec = nextPrec
  val ascPrec = nextPrec // * `x => x : T` should parsed as `x => (x : T)`
  val `=` = Keyword("=", eqPrec, eqPrec)
  val `:` = Keyword(":", ascPrec, eqPrec)
  
  val `if` = Keyword("if", N, nextPrec)
  val `then` = Keyword("then", nextPrec, curPrec)
  val `else` = Keyword("else", nextPrec, curPrec)
  val `case` = Keyword("case", N, N)
  val `fun` = Keyword("fun", N, N)
  val `val` = Keyword("val", N, N)
  val `var` = Keyword("var", N, N)
  val `as` = Keyword("as", N, N)
  val `of` = Keyword("of", N, N)
  val `or` = Keyword("or", nextPrec, curPrec)
  val `and` = Keyword("and", nextPrec, nextPrec)
  val `is` = Keyword("is", nextPrec, curPrec)
  val `let` = Keyword("let", nextPrec, curPrec)
  val `region` = Keyword("region", curPrec, curPrec)
  val `rec` = Keyword("rec", N, N)
  val `in` = Keyword("in", curPrec, curPrec)
  val `out` = Keyword("out", N, curPrec)
  val `mut` = Keyword("mut", N, nextPrec)
  val `set` = Keyword("set", N, N)
  val `do` = Keyword("do", N, N)
  val `while` = Keyword("while", N, N)
  val `declare` = Keyword("declare", N, N)
  val `trait` = Keyword("trait", N, N)
  val `mixin` = Keyword("mixin", N, N)
  val `interface` = Keyword("interface", N, N)
  val `restricts` = Keyword("restricts", eqPrec, nextPrec)
  val `extends` = Keyword("extends", nextPrec, nextPrec)
  val `with` = Keyword("with", curPrec, curPrec)
  val `override` = Keyword("override", N, N)
  val `super` = Keyword("super", N, N)
  val `new` = Keyword("new", N, curPrec) // TODO: check the prec
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
  val `true` = Keyword("true", N, curPrec)
  val `false` = Keyword("false", N, curPrec)
  val `public` = Keyword("public", N, N)
  val `private` = Keyword("private", N, N)
  val `return` = Keyword("return", N, curPrec)
  
  // * The lambda operator is special:
  // *  it should associate very strongly on the left and very loosely on the right
  // *  so that we can write things like `f() |> x => x is 0` ie `(f()) |> (x => (x is 0))`
  val `=>` = Keyword("=>", nextPrec, eqPrec)
  val `->` = Keyword("->", curPrec, eqPrec)
  
  val modifiers = Set(
    `abstract`, mut, virtual, `override`, declare, public, `private`)
  
  type Infix = `and`.type | `or`.type | `then`.type | `else`.type | `is`.type | `:`.type | `->`.type | `=>`.type | `extends`.type | `restricts`.type
  
  val maxPrec = curPrec
  

