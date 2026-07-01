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
import hkmc2.syntax.Tree, Tree.{Ident, StrLit}

enum ImportSelection:
  case Default(alias: Opt[Ident])
  case Namespace(alias: Ident)
  case Named(imported: Ident, alias: Opt[Ident])

class Importer:
  self: Elaborator =>
  import tl.*
  import ImportKind.{Default as DefaultImport, Namespace as NamespaceImport, Named as NamedImport}
  import ImportSelection.{Default as DefaultSelection, Namespace as NamespaceSelection, Named as NamedSelection}
  
  def importPath(rawPath: StrLit, selection: ImportSelection)(using cfg: Config): Import =
    cctx.moduleResolver.tryResolveModulePath(rawPath.value, wd) match
      case S(ModuleResolver.ResolvedModule.Verbatim(specifier, moduleName)) =>
        // The path resolves to a platform dependent specifier, which is NOT a
        // path and should be used as-is, e.g., Node.js built-in modules.
        val id = localId(selection, moduleName)
        val sym = VarSymbol(id)
        Import(sym, specifier, wd / io.RelPath(moduleName), importKind(selection, moduleName))
      case S(ModuleResolver.ResolvedModule.File(sourceFile, targetFile, moduleName)) =>
        // The specifier is resolved to a file path.
        importFile(rawPath, sourceFile, targetFile, moduleName, selection)
      case N =>
        // The specifier could not be resolved. We treat it as a file path.
        val actualFile =
          if rawPath.value.startsWith("/") then io.Path(rawPath.value)
          else wd / io.RelPath(rawPath.value)
        val targetFile = cctx.moduleResolver.targetPathForSource(actualFile).getOrElse(actualFile)
        importFile(rawPath, actualFile, targetFile, actualFile.baseName, selection)
  
  private def localId(selection: ImportSelection, moduleName: Str): Ident = selection match
    case DefaultSelection(alias) => alias.getOrElse(new Ident(moduleName)) // TODO loc
    case NamespaceSelection(alias) => alias
    case NamedSelection(imported, alias) => alias.getOrElse(imported)
  
  private def importKind(selection: ImportSelection, moduleName: Str): ImportKind = selection match
    case DefaultSelection(_) => DefaultImport
    case NamespaceSelection(_) => NamespaceImport
    case NamedSelection(imported, _) =>
      if imported.name === moduleName then DefaultImport else NamedImport(imported.name)
  
  private def importFile(rawPath: StrLit, actualFile: io.Path, targetFile: io.Path, nme: Str, selection: ImportSelection)(using cfg: Config): Import =
    val id = localId(selection, nme)
    val kind = importKind(selection, nme)
    
    lazy val sym = VarSymbol(id)
    
    log(s"importing $actualFile")
    
    if cctx.fs.exists(actualFile) then
      
      actualFile.ext match
      
      case "mjs" | "js" =>
        Import(sym, targetFile.toString, targetFile, kind)
        
      case "mls" if {
        !cctx.beingCompiled.contains(actualFile) `||`:
          raise:
            ErrorReport:
                msg"Circular imports of `mls` files are not yet supported" -> N
                :: (cctx.allFilesBeingImported :+ actualFile).map(f => msg"  importing ${f.toString}" -> N)
          false
      } =>
        
        val importedSym: ImportSymbol = tl.trace(s">>> Importing $actualFile"):
          given TL = tl
          val artifact = cctx.getElaboratedBlock(actualFile, prelude)
          kind match
          case DefaultImport =>
            artifact.tree.definedSymbols.find(_._1 === nme) match
            case Some(nme -> imsym) => imsym
            case None => lastWords(s"File $actualFile does not define a symbol named $nme")
          case NamespaceImport =>
            sym
          case NamedImport(importedName) =>
            raise:
              ErrorReport(
                msg"Named imports from MLscript sources currently support only the default module name '$nme'" ->
                  rawPath.toLoc :: Nil)
            sym
        val selectedSym = (selection, importedSym) match
          case (DefaultSelection(S(alias)), _) => VarSymbol(alias)
          case (NamedSelection(_, S(alias)), _) if kind === DefaultImport => VarSymbol(alias)
          case _ => importedSym
        
        val jsFile =
          if targetFile.ext === "mjs" then targetFile
          else targetFile.up / io.RelPath(targetFile.baseName + ".mjs")
        Import(selectedSym, jsFile.toString, jsFile, kind)
        
      case _ =>
        if actualFile.ext =/= "mls" then raise:
          ErrorReport(msg"Unsupported file type" -> rawPath.toLoc :: Nil)
        Import(sym, rawPath.value, actualFile, kind)
      
    else
      raise:
        ErrorReport(msg"Cannot resolve the import path ${actualFile.toString}" -> rawPath.toLoc :: Nil)
      Import(sym, rawPath.value, actualFile, kind)
