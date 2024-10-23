package hkmc2
package semantics

import scala.collection.mutable
import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import utils.TraceLogger

import Elaborator.*
import hkmc2.syntax.LetBind

class Importer:
  self: Elaborator =>
  import tl.*
  
  def importPath(path: Str): Import =
    // log(s"pwd: ${os.pwd}")
    // log(s"wd: ${wd}")
    val file = wd / os.RelPath(path)
    log(s"importing $file")
    
    val nme = file.baseName
    val id = new syntax.Tree.Ident(nme) // TODO loc
    
    val sym = TermSymbol(LetBind, N, id)
    
    file.ext match
    case "mjs" | "js" =>
      Import(sym, file)
    case "mls" =>
      val block = os.read(file)
      val fph = new FastParseHelpers(block)
      val origin = Origin(file.toString, 0, fph)
      // TODO import symbolsfrom MLs file
      val jsFile = ??? // TODO resolve corresponding JS file
      Import(sym, jsFile)
    

