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
import hkmc2.syntax.{LetBind, Tree}, Tree.StrLit


class Importer:
  self: Elaborator =>
  import tl.*
  
  def importPath(rawPath: StrLit, alias: Opt[syntax.Tree.Ident])(using cfg: Config): Import =
    cctx.moduleResolver.tryResolveModulePath(rawPath.value, wd) match
      case S(ModuleResolver.ResolvedModule.Verbatim(specifier, moduleName)) =>
        // The path resolves to a platform dependent specifier, which is NOT a
        // path and should be used as-is, e.g., Node.js built-in modules.
        val id = alias.getOrElse(new syntax.Tree.Ident(moduleName)) // TODO loc
        val sym = TermSymbol(LetBind, N, id)
        Import(sym, specifier, wd / io.RelPath(rawPath.value)) // hmm, the third arg is dummy???
      case S(ModuleResolver.ResolvedModule.File(sourceFile, targetFile, moduleName)) =>
        // The specifier is resolved to a file path.
        importFile(rawPath, sourceFile, targetFile, moduleName, alias)
      case N =>
        // The specifier could not be resolved. We treat it as a file path.
        val actualFile =
          if rawPath.value.startsWith("/") then io.Path(rawPath.value)
          else wd / io.RelPath(rawPath.value)
        val targetFile = cctx.moduleResolver.targetPathForSource(actualFile).getOrElse(actualFile)
        importFile(rawPath, actualFile, targetFile, actualFile.baseName, alias)
  
  private def importFile(rawPath: StrLit, actualFile: io.Path, targetFile: io.Path, nme: Str, alias: Opt[syntax.Tree.Ident])(using cfg: Config): Import =
    val id = alias.getOrElse(new syntax.Tree.Ident(nme)) // TODO loc
    
    lazy val sym = TermSymbol(LetBind, N, id)
    
    log(s"importing $actualFile")
    
    if cctx.fs.exists(actualFile) then
      
      actualFile.ext match
      
      case "mjs" | "js" =>
        Import(sym, targetFile.toString, targetFile)
        
      case "mls" if {
        !cctx.beingCompiled.contains(actualFile) `||`:
          raise:
            ErrorReport:
                msg"Circular imports of `mls` files are not yet supported" -> N
                :: (cctx.allFilesBeingImported :+ actualFile).map(f => msg"  importing ${f.toString}" -> N)
          false
      } =>
        
        val importedSym = tl.trace(s">>> Importing $actualFile"):
          given TL = tl
          val artifact = cctx.getElaboratedBlock(actualFile, prelude)
          artifact.tree.definedSymbols.find(_._1 === nme) match
          case Some(nme -> imsym) => imsym
          case None => lastWords(s"File $actualFile does not define a symbol named $nme")
        val sym = alias.fold(importedSym): alias =>
          val res = BlockMemberSymbol(alias.name, importedSym.trees, importedSym.nameIsMeaningful)
          res.tsym = importedSym.tsym
          res
        
        val jsFile =
          if targetFile.ext === "mjs" then targetFile
          else targetFile.up / io.RelPath(targetFile.baseName + ".mjs")
        Import(sym, jsFile.toString, jsFile)
        
      case _ =>
        if actualFile.ext =/= "mls" then raise:
          ErrorReport(msg"Unsupported file type" -> rawPath.toLoc :: Nil)
        Import(sym, rawPath.value, actualFile)
      
    else
      raise:
        ErrorReport(msg"Cannot resolve the import path ${actualFile.toString}" -> rawPath.toLoc :: Nil)
      Import(sym, rawPath.value, actualFile)
