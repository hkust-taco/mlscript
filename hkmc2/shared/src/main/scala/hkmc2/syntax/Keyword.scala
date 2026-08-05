package hkmc2
package syntax

import collection.mutable
import hkmc2.utils.*, shorthands.*


class Keyword(
    val name: String,
    val leftPrec: Opt[Int],
    val rightPrec: Opt[Int],
    
    /** If the operator can be used infix, can it be done on a newline (with no indent)?
        For instance, if `via` has `canStartInfixOnNewLine`, then one can write:
          foo
          via f
          via g
        But `is` does not have `canStartInfixOnNewLine` so that
          if x
            is A then foo
            is B then bar
        does not parse as
          if x { is A then foo { is B then ... } }
        Note: Currently, this just fails to parse.
        We should probably rather make `is` a normal operator like `+`; then it would work.
      */
    val canStartInfixOnNewLine: Bool = true
):
  Keyword.all += name -> this
  def assumeLeftPrec: Int = leftPrec.getOrElse(lastWords(s"$this does not have left precedence"))
  def assumeRightPrec: Int = rightPrec.getOrElse(lastWords(s"$this does not have right precedence"))
  def leftPrecOrMin: Int = leftPrec.getOrElse(Int.MinValue)
  def rightPrecOrMin: Int = rightPrec.getOrElse(Int.MinValue)
  def rightPrecOrMax: Int = rightPrec.getOrElse(Int.MaxValue)
  override def toString: Str = s"keyword '$name'"

object Keyword:
  def unapply(kw: Keyword): Opt[Str] = S(kw.name)
  
  val all: mutable.Map[Str, Keyword] = mutable.Map.empty
  
  // val Let = Keyword("let", 0, 0)
  // val Let = Keyword("let", 0, 0)
  
  private var _curPrec = 2
  private def curPrec: S[Int] = S(_curPrec)
  private def nextPrec: S[Int] =
    _curPrec += 1
    S(_curPrec)
  
  val `class` = Keyword("class", N, N)
  
  val `extends` = Keyword("extends", nextPrec, curPrec)
  val `restricts` = Keyword("restricts", curPrec, curPrec)
  val `with` = Keyword("with", curPrec, curPrec)
  
  val `val` = Keyword("val", N, curPrec)

  val eqPrec = nextPrec
  val `=` = Keyword("=", eqPrec, eqPrec)
  val `..` = Keyword("..", N, N)
  val `...` = Keyword("...", N, N)
  // val `;` = Keyword(";", ascPrec, eqPrec)
  
  val `if` = Keyword("if", N, nextPrec)
  val `while` = Keyword("while", N, curPrec)
  val `assert` = Keyword("assert", N, curPrec)
  type `assert` = `assert`.type
  
  val `case` = Keyword("case", N, curPrec)
  
  val thenPrec = nextPrec
  
  val whereLhsPrec = nextPrec
  
  val `then` = Keyword("then", thenPrec, eqPrec)
  val `do` = Keyword("do", thenPrec, eqPrec)
  val `drop` = Keyword("drop", thenPrec, eqPrec)
  
  val `else` = Keyword("else", N, eqPrec)
  type `else` = `else`.type
  
  val `try` = Keyword("try", N, curPrec)
  val `finally` = Keyword("finally", N, curPrec, canStartInfixOnNewLine = true)
  
  val `return` = Keyword("return", N, curPrec)
  val `throw` = Keyword("throw", N, curPrec)
  val `yield` = Keyword("yield", N, curPrec)
  val `yield*` = Keyword("yield*", N, curPrec)
  val `import` = Keyword("import", N, curPrec)
  
  val `fun` = Keyword("fun", N, N)
  // val `val` = Keyword("val", N, N)
  val `var` = Keyword("var", N, N)
  val `where` = Keyword("where", whereLhsPrec, curPrec)
  val `of` = Keyword("of", N, N) // * Note that `of` is parsed specially, so its precedence is not listed here
  
  val `in` = Keyword("in", nextPrec, curPrec)
  val `out` = Keyword("out", N, curPrec)
  
  // * `|` should bind looser than `=>` RHS, so that `0 => false | 1 => true` works
  val pipePrec = nextPrec
  val ampPrec = nextPrec
  val `|` = Keyword("|", pipePrec, pipePrec)
  val `&` = Keyword("&", ampPrec, ampPrec)
  
  val lamRhsPrec = nextPrec
  // * ^ `x => x as T` should parsed as `x => (x as T)`
  // * ^ `(a, b) => a and b` should parsed as `(a, b) => (a and b)`
  // *    so `=>` RHS should bind looser than `and` and `or`
  
  val `or` = Keyword("or", nextPrec, curPrec)
  val `and` = Keyword("and", nextPrec, nextPrec)
  
  // * Ideally, `is` RHS should bind looser than `|`, so that `x is A | B` works
  // * However, we also want `is` RHS to bing stronger than `and`/`or`, so that `x is A and b is B` works!
  // * So, for now, we settle on requiring parentheses in `x is (A | B)`
  val isRhsPrec = nextPrec
  // * We have a similar conundrum for `as`; we adopt a similar resolution:
  val `as` = Keyword("as", nextPrec,
    // isRhsPrec // * Allows `42 as Int | Num` to parse as `42 as (Int | Num)`
    curPrec // * Allows `pattern Steps = Steps as Step | _` to parse as `(Steps as Step) | _`, which is more natural
  )
  
  // * `x => x : T` should parsed as `x => (x : T)`
  // * (though this is not very important, since we now use `as` for type ascription)
  val colonPrec = nextPrec
  val `:` = Keyword(":", colonPrec, eqPrec)
  
  val `not` = Keyword("not", nextPrec, nextPrec)
  val `is` = Keyword("is", nextPrec, isRhsPrec, canStartInfixOnNewLine = false)
  
  // val `let` = Keyword("let", nextPrec, curPrec)
  val `let` = Keyword("let", N, N)
  val `handle` = Keyword("handle", N, N)
  val `region` = Keyword("region", N, N)
  val `rec` = Keyword("rec", N, N)
  val `set` = Keyword("set", N, curPrec)
  val `declare` = Keyword("declare", N, N)
  val `data` = Keyword("data", N, N)
  val `trait` = Keyword("trait", N, N)
  val `mixin` = Keyword("mixin", N, N)
  val `interface` = Keyword("interface", N, N)
  val `override` = Keyword("override", N, N)
  val `super` = Keyword("super", N, N)
  // val `namespace` = Keyword("namespace", N, N)
  val `using` = Keyword("using", N, N)
  val `module` = Keyword("module", N, N)
  val `object` = Keyword("object", N, N)
  val `open` = Keyword("open", N, curPrec)
  val `type` = Keyword("type", N, N)
  val `forall` = Keyword("forall", N, N)
  val `exists` = Keyword("exists", N, N)
  val `null` = Keyword("null", N, N)
  val `undefined` = Keyword("undefined", N, N)
  val `abstract` = Keyword("abstract", N, N)
  val `constructor` = Keyword("constructor", N, N)
  val `virtual` = Keyword("virtual", N, N)
  val `staged` = Keyword("staged", N, N)
  val `true` = Keyword("true", N, N)
  val `false` = Keyword("false", N, N)
  val `public` = Keyword("public", N, N)
  val `private` = Keyword("private", N, N)
  val `this` = Keyword("this", N, N)
  val `outer` = Keyword("outer", N, N)
  val `pattern` = Keyword("pattern", N, N)
  
  val `->` = Keyword("->", nextPrec, eqPrec)
  
  val maxPrec = curPrec
  
  // * The lambda operator is special:
  // *  it should associate very strongly on the left and very loosely on the right
  // *  so that we can write things like `f() |> x => x is 0` ie `(f()) |> (x => (x is 0))`
  // * Currently, the precedence of normal operators starts at the maximum precedence of keywords,
  // * so we need to start the precedence of `=>` to account for that.
  val `=>` = Keyword("=>", S(maxPrec.get + charPrecList.length), lamRhsPrec)

  // * `new` is a strange keyword:
  // * it has a very high precedence that sits between that of selection and that of application.
  // * Indeed, `new Foo().bar` should parse as `(new Foo()).bar`, not `new (Foo().bar)`,
  // * but `new Foo.Bar` should parse as `new (Foo.Bar)`.
  val newRightPrec = S(maxPrec.get + charPrecList.length - 1)
  // * ^ maxPrec.get + charPrecList.length is the precedence of selection
  val `new` = Keyword("new", N, newRightPrec)
  val `new!` = Keyword("new!", N, newRightPrec)
  val `mut` = Keyword("mut", N, newRightPrec)
  
  // * `#` is both a prefix keyword (for directives like `#config(...)`)
  // * and an infix operator (for disambiguation like `Lazy#get()`).
  // * It has very high left precedence (like selection) when used as infix.
  // * The right precedence is set to the same level (very tight) so that infix `#`
  // * only picks up the immediately following identifier, e.g., `arr.Cls#d.f()`
  // * parses as `App(Sel(InfixApp(Sel(arr, Cls), #, d), f), ())`.
  // * In prefix position, this means `#config` only gets the name; `(args)` is
  // * consumed by `exprCont` and the elaborator reconstructs the directive.
  // * `canStartInfixOnNewLine = false` prevents it from being parsed as infix
  // * when it appears on a new line after an expression.
  val hashSelPrec = S(maxPrec.get + charPrecList.length)
  val `#` = Keyword("#", hashSelPrec, hashSelPrec, canStartInfixOnNewLine = false)
  
  val __ = Keyword("_", N, N)
  
  val modifiers = Set(
    `abstract`, mut, virtual, `override`, declare, public, `private`)
  
  type Prefix =
    `do`.type | `drop`.type | `not`.type | `new!`.type | `else`.type | `return`.type | `throw`.type | `yield`.type |
    `yield*`.type | `import`.type | `|`.type | `&`.type
  
  type Infix =
    `is`.type | `:`.type | `->`.type | `=>`.type | `extends`.type | `restricts`.type | `as`.type |
    `|`.type | `&`.type | `do`.type |
    `where`.type | `with`.type | `and`.type | `or`.type | `then`.type | `else`.type | `#`.type
  
  type InfixSplittable =
    `is`.type | `:`.type | `->`.type | `=>`.type | `extends`.type | `restricts`.type | `as`.type | `do`.type |
    `where`.type | `with`.type | `of`.type
  
  type Ellipsis = `...`.type | `..`.type
  
  type IfLike = `if`.type | `while`.type
  type SplitLike = IfLike | `case`.type
  
  type LetLike = `let`.type | `set`.type
  
  type Modifier = `in`.type | `out`.type | `mut`.type | `abstract`.type | `declare`.type | `data`.type | `virtual`.type | `override`.type |
    `public`.type | `private`.type | `staged`.type

