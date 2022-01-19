package mlscript

import mlscript.utils._, shorthands._
import scala.collection.immutable.HashMap

class Polyfill {
  private val featFnNameMap = collection.mutable.HashMap[Str, Str]()
  private val emittedFeatSet = collection.mutable.HashSet[Str]()

  def use(feat: Str, jsFnName: Str): Str = {
    featFnNameMap += feat -> jsFnName
    jsFnName
  }

  /**
    * Check whether a feature has been already used.
    */
  def used(feat: Str): Bool = featFnNameMap.contains(feat)

  def get(feat: Str): Opt[Str] = featFnNameMap get feat

  def emit(): Ls[JSStmt] = (featFnNameMap flatMap { case (featName, fnName) =>
    if (emittedFeatSet contains featName)
      N
    else
      Polyfill.getFeature(featName) match {
        case S(feature) =>
          emittedFeatSet += featName
          S(feature(fnName))
        case N          => N
      }
  }).toList
}

object Polyfill {
  def apply(): Polyfill = new Polyfill()

  abstract class Feature {
    val name: Str
    def apply(name: Str): JSStmt
  }

  final case class BuiltinFunc(val name: Str, maker: Str => JSStmt) extends Feature {
    def apply(name: Str): JSStmt = maker(name)
  }

  final case class RuntimeHelper(val name: Str, maker: Str => JSStmt) extends Feature {
    def apply(name: Str): JSStmt = maker(name)
  }

  val features: Ls[Feature] =
    RuntimeHelper("prettyPrint", (name: Str) => {
      val arg = JSIdent("value")
      val default = arg.member("constructor").member("name") + JSExpr(" ") +
        JSIdent("JSON").member("stringify")(arg, JSIdent("undefined"), JSIdent("2"))
      JSFuncDecl(
        name,
        JSNamePattern("value") :: Nil,
        arg
          .typeof()
          .switch(
            default.`return` :: Nil,
            JSExpr("number") -> Nil,
            JSExpr("boolean") -> {
              arg.member("toString")().`return` :: Nil
            },
            // Returns `"[Function: <name>]"`
            JSExpr("function") -> {
              val name = arg.member("name") ?? JSExpr("<anonymous>")
              val repr = JSExpr("[Function: ") + name + JSExpr("]")
              (repr.`return` :: Nil)
            },
            JSExpr("string") -> ((JSExpr("\"") + arg + JSExpr("\"")).`return` :: Nil)
          ) :: Nil,
      )
    }) :: RuntimeHelper("withConstruct", (name: Str) => {
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
    }) :: BuiltinFunc("toString", {
      JSFuncDecl(_, JSNamePattern("x") :: Nil, JSIdent("String")(JSIdent("x")).`return` :: Nil)
    }) :: BuiltinFunc("id", {
      JSFuncDecl(_, JSNamePattern("x") :: Nil, JSIdent("x").`return` :: Nil)
    }) :: BuiltinFunc("succ", {
      JSFuncDecl(_, JSNamePattern("x") :: Nil, (JSIdent("x") + JSLit("1")).`return` :: Nil)
    }) :: BuiltinFunc("error", {
      JSFuncDecl(
        _,
        Nil,
        JSInvoke(
          JSIdent("Error", true),
          JSExpr("unexpected runtime error") :: Nil
        ).`throw` :: Nil
      )
    }) :: BuiltinFunc("concat", { makeBinaryFunc(_, "+") }) ::
      BuiltinFunc("add", { makeBinaryFunc(_, "+") }) ::
      BuiltinFunc("sub", { makeBinaryFunc(_, "-") }) ::
      BuiltinFunc("mul", { makeBinaryFunc(_, "*") }) ::
      BuiltinFunc("div", { makeBinaryFunc(_, "/") }) ::
      BuiltinFunc("gt", { makeBinaryFunc(_, ">") }) ::
      BuiltinFunc("not", { makeUnaryFunc(_, "!") }) ::
      BuiltinFunc("negate", { makeUnaryFunc(_, "-") }) ::
      Nil
  
  private val nameFeatureMap = HashMap.from(features map { feature => (feature.name, feature) })

  def getFeature(name: Str): Opt[Feature] = nameFeatureMap get name

  def isPreludeFunction(name: Str): Bool = nameFeatureMap.get(name).map({
    case BuiltinFunc(_, _) => true
    case _                 => false
  }).getOrElse(false)

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
