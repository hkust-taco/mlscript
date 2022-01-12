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
    }) :: Nil
  )
}
