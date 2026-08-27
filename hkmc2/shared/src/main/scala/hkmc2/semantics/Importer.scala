package hkmc2
package semantics

import scala.collection.mutable
import scala.annotation.tailrec

import hkmc2.utils.*, shorthands.*
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
        
      case "mls" =>
        def reportCycle(files: Ls[io.Path]): Import =
          raise:
            ErrorReport:
                msg"Circular imports of `mls` files are not yet supported" -> N
                :: files.map(f => msg"  importing ${f.toString}" -> N)
          Import(sym, path, file)

        if cctx.beingCompiled.contains(file) then
          reportCycle(cctx.allFilesBeingImported :+ file)
        else
          cctx.withActiveDependency(file)(reportCycle):
            val importedSym = tl.trace(s">>> Importing $file"):
              given TL = tl
              val artifact = cctx.getElaboratedBlock(file, prelude)
              artifact.compilationUnit.defaultExport.getOrElse:
                lastWords(s"File $file does not define a symbol named $nme")
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
    
