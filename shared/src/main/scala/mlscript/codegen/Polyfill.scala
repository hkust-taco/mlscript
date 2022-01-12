package mlscript

import mlscript.utils._, shorthands._
import scala.collection.immutable.HashMap

class Polyfill {
  private val featFnNameMap = collection.mutable.HashMap[Str, Str]()
  private val emittedFeatSet = collection.mutable.HashSet[Str]()

  def use(feat: Str, fnName: Str): Str = {
    featFnNameMap += feat -> fnName
    fnName
  }

  def used(feat: Str): Bool = featFnNameMap.contains(feat)

  def get(feat: Str): Opt[Str] = featFnNameMap get feat

  def emit(): Ls[JSStmt] = (featFnNameMap flatMap { case (feat, fnName) =>
    if (emittedFeatSet contains feat)
      N
    else
      Polyfill.featFactoryMap get feat match {
        case S(factory) =>
          emittedFeatSet += feat
          S(factory(fnName))
        case N          => N
      }
  }).toList
}

object Polyfill {
  def apply(): Polyfill = new Polyfill()

  val featFactoryMap: HashMap[Str, Str => JSStmt] = HashMap.from(
    "withConstruct" -> ((name: Str) => {
      val obj = JSIdent("Object")
      val tgt = JSIdent("target")
      val body: Ls[JSStmt] = JSIfStmt(
        (tgt.typeof() :=== JSExpr("string")) :|| (tgt.typeof() :=== JSExpr("number")) :||
          (tgt.typeof() :=== JSExpr("boolean")) :|| (tgt.typeof() :=== JSExpr("bigint")) :||
          (tgt.typeof() :=== JSExpr("symbol")),
        obj("assign")(tgt, JSIdent("fields")).`return` :: Nil,
      ) :: JSIfStmt(
        tgt.instanceOf(JSIdent("String")) :|| tgt.instanceOf(JSIdent("Number")) :||
          tgt.instanceOf(JSIdent("Boolean")) :|| tgt.instanceOf(JSIdent("BigInt")),
        obj("assign")(tgt("valueOf")(), tgt, JSIdent("fields")).`return` :: Nil,
      ) :: JSConstDecl("copy", obj("assign")(JSRecord(Nil), tgt, JSIdent("fields"))) ::
        obj("setPrototypeOf")(JSIdent("copy"), obj("getPrototypeOf")(tgt)).stmt ::
        JSIdent("copy").`return` ::
        Nil
      JSFuncDecl(
        name,
        JSNamePattern("target") :: JSNamePattern("fields") :: Nil,
        body
      )
    }) :: "id" -> {
      JSFuncDecl(_, JSNamePattern("x") :: Nil, JSIdent("x").`return` :: Nil)
    } :: "succ" -> {
      JSFuncDecl(_, JSNamePattern("x") :: Nil, (JSIdent("x") + JSLit("1")).`return` :: Nil)
    } :: "error" -> {
      JSFuncDecl(
        _,
        Nil,
        JSInvoke(
          JSIdent("Error", true),
          JSExpr("unexpected runtime error") :: Nil
        ).`throw` :: Nil
      )
    } :: 
      "concat" -> { makeBinaryFunc(_, "+") } ::
      "add" -> { makeBinaryFunc(_, "+") } ::
      "sub" -> { makeBinaryFunc(_, "-") } ::
      "mul" -> { makeBinaryFunc(_, "*") } ::
      "div" -> { makeBinaryFunc(_, "/") } ::
      "gt" -> { makeBinaryFunc(_, ">") } ::
      "not" -> { makeUnaryFunc(_, "!") } ::
      Nil
  )

  def isPreludeFunction(name: Str): Bool = {
    !(name === "withConstruct") && featFactoryMap.keySet.contains(name)
  }

  private def makeBinaryFunc(name: Str, op: Str): JSFuncDecl =
    JSFuncDecl(
      name,
      JSNamePattern("x") :: JSNamePattern("y") :: Nil,
      JSIfStmt(
        JSIdent("arguments").member("length") :=== JSLit("2"),
        (JSIdent("x").binary(op, JSIdent("y"))).`return` :: Nil,
        JSArrowFn(
          JSNamePattern("y") :: Nil,
          L(JSIdent("x").binary(op, JSIdent("y")))
        ).`return` :: Nil
      ) :: Nil
    )

  private def makeUnaryFunc(name: Str, op: Str): JSFuncDecl =
    JSFuncDecl(
      name,
      JSNamePattern("x") :: Nil,
      (JSIdent("x").unary(op)).`return` :: Nil
    )
}
