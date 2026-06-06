package hkmc2
package io

import scala.scalajs.js
import scala.scalajs.js.annotation._

import hkmc2.utils.*, shorthands.*

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
    def lstatSync(path: Str): Stats = js.native
  
  /**
    * The facade for [[fs.Stats]]. Only a few useful members are listed here.
    * Refer to https://nodejs.org/api/fs.html#class-fsstats for the full list
    * of methods.
    */
  @js.native
  trait Stats extends js.Object:
    def isDirectory(): Bool = js.native
    def isFile(): Bool = js.native
    def isSymbolicLink(): Bool = js.native
    /** The size of the file in bytes. */
    val size: Long = js.native
    /** The timestamp indicating the last time this file was accessed. */
    def atime: js.Date = js.native
    /** The timestamp indicating the last time this file was modified. */
    def mtime: js.Date = js.native
    /** The timestamp indicating the last time the file status was changed. */
    def ctime: js.Date = js.native
    /** The timestamp indicating the creation time of this file. */
    def birthtime: js.Date = js.native
  
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
