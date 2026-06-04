package hkmc2
package semantics

import scala.collection.mutable
import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.Message.MessageContext
import hkmc2.io
import utils.TraceLogger

import Elaborator.*
import hkmc2.syntax.LetBind


class Importer:
  self: Elaborator =>
  import tl.*
  
  def importPath(path: Str, alias: Opt[syntax.Tree.Ident])(using cfg: Config): Import =
    // log(s"pwd: ${os.pwd}")
    // log(s"wd: ${wd}")
    
    val file =
      if path.startsWith("/")
      then io.Path(path)
      else wd / io.RelPath(path)
    
    val nme = file.baseName
    val id = alias.getOrElse(new syntax.Tree.Ident(nme)) // TODO loc
    
    lazy val sym = VarSymbol(id)
    
    if path.startsWith(".") || path.startsWith("/") then // leave alone imports like "fs"
      log(s"importing $file")
      
      val nme = file.baseName
      val id = new syntax.Tree.Ident(nme) // TODO loc
      
      file.ext match
      
      case "mjs" | "js" =>
        Import(sym, file.toString, file)
        
      case "mls" if {
        !cctx.beingCompiled.contains(file) `||`:
          raise:
            ErrorReport:
                msg"Circular imports of `mls` files are not yet supported" -> N
                :: (cctx.allFilesBeingImported :+ file).map(f => msg"  importing ${f.toString}" -> N)
          false
      } =>
        
        val importedSym = tl.trace(s">>> Importing $file"):
          given TL = tl
          val artifact = cctx.getElaboratedBlock(file, prelude)
          artifact.tree.definedSymbols.find(_._1 === nme) match
          case Some(nme -> imsym) => imsym
          case None => lastWords(s"File $file does not define a symbol named $nme")
        val sym: VarSymbol | BlockMemberSymbol = alias.fold(importedSym): alias =>
          VarSymbol(alias)
        
        val jsFile = file.up / io.RelPath(file.baseName + ".mjs")
        Import(sym, jsFile.toString, jsFile)
        
      case _ =>
        if file.ext =/= "mls" then raise:
          ErrorReport(msg"Unsupported file extension: ${file.ext}" -> N :: Nil)
        Import(sym, path, file)
      
    else
      Import(sym, path, file)
    

