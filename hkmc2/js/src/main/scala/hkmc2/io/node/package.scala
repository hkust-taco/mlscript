package hkmc2
package io

import scala.scalajs.js
import scala.scalajs.js.annotation._

import mlscript.utils._, shorthands._

/**
  * The package object contains facades for Node.js modules. So, it can be used
  * conveniently in 
  */
package object node:
  /**
    * Node.js fs module facade.
    */
  @js.native
  @JSImport("fs", JSImport.Namespace)
  object fs extends js.Object:
    def readFileSync(path: Str, encoding: Str): Str = js.native
    def writeFileSync(path: Str, data: Str): Unit = js.native
    def readdirSync(path: Str): js.Array[Str] = js.native
    def existsSync(path: Str): Bool = js.native
  
  @js.native
  trait ParsedPath extends js.Object:
    val base: Str = js.native
    val name: Str = js.native
    val ext: Str = js.native
  
  /**
    * Node.js path module facade.
    */
  @js.native
  @JSImport("path", JSImport.Namespace)
  object path extends js.Object:
    def sep: Str = js.native
    def parse(path: Str): ParsedPath = js.native
    def relative(from: Str, to: Str): Str = js.native
    def join(paths: Str*): Str = js.native
    def isAbsolute(path: Str): Bool = js.native
    def dirname(path: Str): Str = js.native
  
  /**
    * Node.js process module facade.
    */
  @js.native
  @JSGlobal("process")
  object process extends js.Object:
    def cwd(): Str = js.native
