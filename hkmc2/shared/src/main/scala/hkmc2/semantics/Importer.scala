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


class Importer extends NewResolver:
  self: Elaborator =>
  import tl.*


  def importPath(path: Str, alias: Opt[syntax.Tree.Ident])(loc: Opt[Loc])(using cfg: Config, ctx: Elaborator.Ctx, rs: ResolutionContext): Import =
    // log(s"pwd: ${os.pwd}")
    // log(s"wd: ${wd}")
    
    val file = io.Path.resolve(wd, path)
    
    val nme = file.baseName
    val id = alias.getOrElse(new syntax.Tree.Ident(nme)) // TODO loc
    
    lazy val sym = VarSymbol(id, erasedType = N)
    
    if path.startsWith(".") || path.startsWith("/") then // leave alone imports like "fs"
      log(dbg"importing $file")
      
      val nme = file.baseName
      val id = new syntax.Tree.Ident(nme) // TODO loc
      
      file.ext match
      
      case "mjs" | "js" =>
        if newResolution then sym.currentShapes.add(DynShape())
        Import(sym, file.toString, file)(loc)
        
      case "mls" =>
        def reportCycle(files: Ls[io.Path]): Import =
          raise:
            ErrorReport:
                msg"Circular imports of `mls` files are not yet supported" -> N
                :: files.map(f => msg"  importing ${f.toString}" -> N)
          Import(sym, path, file)(loc)

        if cctx.beingCompiled.contains(file) then
          reportCycle(cctx.allFilesBeingImported :+ file)
        else
          cctx.withActiveDependency(file)(reportCycle):
            val importedSym = tl.trace(dbg">>> Importing $file"):
              given TL = tl
              val artifact = cctx.getElaboratedBlock(file, prelude)
              artifact.compilationUnit.defaultExport.getOrElse:
                lastWords(s"File $file does not define a symbol named $nme")
            val sym: VarSymbol | BlockMemberSymbol = alias.fold(importedSym): alias =>
              VarSymbol(alias, erasedType = N)

            // An import alias denotes the imported value, just like a local
            // binding. Publish its shapes so selection and opens can follow it.
            if newResolution then sym match
              case local: VarSymbol =>
                val ref = Term.MemberRef(importedSym)(N, FlowSymbol.memSym(importedSym))
                rctx.recordLexicalBinders(ref, ctx.typeBinders)
                pipeTerm(ref, local)
              case _: BlockMemberSymbol => ()

            val jsFile = file.up / io.RelPath(file.baseName + ".mjs")
            Import(sym, jsFile.toString, jsFile)(loc)
        
      case _ =>
        if file.ext =/= "mls" then raise:
          ErrorReport(msg"Unsupported file extension: ${file.ext}" -> N :: Nil)
        Import(sym, path, file)(loc)
      
    else
      if newResolution then sym.currentShapes.add(DynShape())
      Import(sym, path, file)(loc)
    
