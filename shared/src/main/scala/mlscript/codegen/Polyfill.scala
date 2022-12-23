package mlscript

import mlscript.utils._, shorthands._
import scala.collection.immutable.HashMap
import scala.collection.mutable.ArrayBuffer

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
        case N => N
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

  import JSCodeHelpers._

  val features: Ls[Feature] = {
    val buffer = new ArrayBuffer[Feature]()
    buffer += RuntimeHelper(
      "prettyPrint",
      (name: Str) => {
        val arg = JSIdent("value")
        JSFuncDecl(
          name,
          JSNamePattern("value") :: Nil,
          arg
            .typeof()
            .switch(
              JSIdent("String")(arg).`return` :: Nil,
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
              JSExpr("string") -> ((JSExpr("\"") + arg + JSExpr("\"")).`return` :: Nil),
              JSExpr("undefined") -> (JSExpr("undefined").`return` :: Nil),
              JSExpr("object") -> (JSIfStmt(
                arg :=== JSIdent("null"),
                JSExpr("null").`return` :: Nil,
                JSTryStmt(
                  (arg.member("constructor").member("name") +
                    JSExpr(" ") +
                    JSIdent("JSON").member("stringify")(arg, JSIdent("undefined"), JSIdent("2"))).`return` :: Nil,
                  JSCatchClause(
                    JSIdent("_"),
                    JSIdent("String")(arg).`return` :: Nil,
                  )
                ) :: Nil,
              ) :: Nil)
            ) :: Nil,
        )
      }
    )
    buffer += RuntimeHelper(
      "withConstruct",
      (name: Str) => {
        val obj = id("Object")
        val t = id("target")
        val f = id("fields")
        fn(name, param("target"), param("fields")) (
          JSIfStmt(
            (t.typeof() :=== JSExpr("string")) :|| (t.typeof() :=== JSExpr("number")) :||
              (t.typeof() :=== JSExpr("boolean")) :|| (t.typeof() :=== JSExpr("bigint")) :||
              (t.typeof() :=== JSExpr("symbol")),
            obj("assign")(t, f).`return` :: Nil,
          ),
          JSIfStmt(
            t.instanceOf(id("String")) :|| t.instanceOf(id("Number")) :||
              t.instanceOf(id("Boolean")) :|| t.instanceOf(id("BigInt")),
            obj("assign")(t("valueOf")(), t, f).`return` :: Nil,
          ),
          JSIfStmt(
            id("Array")("isArray")(t),
            Ls(
              const("clone", id("Array")("from")(t)),
              forIn(param("key"), t) {
                id("clone").prop(id("key")) := t.prop(id("key"))
              },
              forIn(param("key"), f) {
                id("clone").prop(id("key")) := f.prop(id("key"))
              },
              `return`(id("clone"))
            )
          ),
          JSIfStmt(
            // * "Strict equality checks (===) should be used in favor of ==.
            // *  The only exception is when checking for undefined and null by way of null."
            // *  (http://contribute.jquery.org/style-guide/js/)
            JSBinary("==", t, JSLit("null")),
            `return`(obj("assign")(JSRecord(Nil), JSRecord(Nil), f)) :: Nil,
          ),
          JSConstDecl("copy", obj("assign")(JSRecord(Nil), t, f)),
          obj("setPrototypeOf")(id("copy"), obj("getPrototypeOf")(t)).stmt,
          id("copy").`return`
        )
      }
    )
    buffer += BuiltinFunc(
      "toString", fn(_, param("x")) { `return` { id("String")(id("x")) } }
    )
    buffer += BuiltinFunc(
      "id", fn(_, param("x")) { `return`(id("x")) }
    )
    buffer += BuiltinFunc(
      "emptyArray", fn(_) { `return`(JSArray(Nil)) }
    )
    buffer += BuiltinFunc(
      "succ", fn(_, param("x")) { `return` { id("x") + lit(1) } }
    )
    buffer += BuiltinFunc(
      "error", fn(_) {
        `throw`(JSNew(JSIdent("Error"))(JSExpr("unexpected runtime error")))
      }
    )
    buffer += BuiltinFunc("concat", makeBinaryFunc("+"))
    buffer += BuiltinFunc("add", makeBinaryFunc("+"))
    buffer += BuiltinFunc("sub", makeBinaryFunc("-"))
    buffer += BuiltinFunc("mul", makeBinaryFunc("*"))
    buffer += BuiltinFunc("div", makeBinaryFunc("/"))
    buffer += BuiltinFunc("gt", makeBinaryFunc(">"))
    buffer += BuiltinFunc("not", makeUnaryFunc("!"))
    buffer += BuiltinFunc("negate", makeUnaryFunc("-"))
    buffer.toList
  }

  private val nameFeatureMap = HashMap.from(features map { feature => (feature.name, feature) })

  def getFeature(name: Str): Opt[Feature] = nameFeatureMap get name

  def isPreludeFunction(name: Str): Bool = nameFeatureMap
    .get(name)
    .map({
      case BuiltinFunc(_, _) => true
      case _                 => false
    })
    .getOrElse(false)

  private def makeBinaryFunc(op: Str)(name: Str): JSFuncDecl =
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

  private def makeUnaryFunc(op: Str)(name: Str): JSFuncDecl =
    fn(name, param("x")) { `return`(id("x").unary(op)) }
}
