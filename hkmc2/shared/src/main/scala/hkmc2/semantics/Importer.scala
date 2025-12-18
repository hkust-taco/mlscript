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
  
  import Importer.*
  
  /**
    * Resolve an imported module name to a directory (or file) path. This method
    * should be overridden by subclasses to provide module resolution logic.
    *
    * @param orgName the optional organization name of the module
    * @param moduleName the name of the module being imported
    * @param noSubPath if the import does not have a sub-path (i.e., only the module name)
    * @return the resolved path and module identifier, if any.
    */
  def resolveModule(orgName: Opt[Str], moduleName: Str, noSubPath: Bool): Opt[(io.Path, Str)] = N
  
  /**
    * Try to resolve path if it refers to a module or a source file in a module.
    *
    * @param path the import path
    * @return the resolved path and module identifier, if any.
    */
  private def tryResolveModulePath(path: Str): Opt[(io.Path, Str)] = path match
    case r(orgName, modName, subPath) =>
      val orgNameOpt = if orgName is null then N else S(orgName)
      if subPath is null then
        resolveModule(orgNameOpt, modName, true)
      else
        resolveModule(orgNameOpt, modName, false).map:
          case (p, id) => (p / io.RelPath(subPath), id)
    case _ => N
  
  def importPath(path: Str)(using cfg: Config): Import =
    // Here we handle the path of `import`.
    
    val (file, nme) = tryResolveModulePath(path).getOrElse:
      // Fallback local file resolution.
      val p = if path.startsWith("/") then io.Path(path) else wd / io.RelPath(path)
      (p, p.baseName)
    
    val id = new syntax.Tree.Ident(nme) // TODO loc
    
    lazy val sym = TermSymbol(LetBind, N, id)
    
    if path.startsWith(".") || path.startsWith("/") then // leave alone imports like "fs"
      log(s"importing $file")
      
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
        
        val sym = tl.trace(s">>> Importing $file"):
          given TL = tl
          val artifact = cctx.getElaboratedBlock(file, prelude)
          artifact.tree.definedSymbols.find(_._1 === nme) match
          case Some(nme -> imsym) => imsym
          case None => lastWords(s"File $file does not define a symbol named $nme")
        
        val jsFile = file.up / io.RelPath(file.baseName + ".mjs")
        Import(sym, jsFile.toString, jsFile)
        
      case _ =>
        if file.ext =/= "mls" then raise:
          ErrorReport(msg"Unsupported file extension: ${file.ext}" -> N :: Nil)
        Import(sym, path, file)
      
    else
      Import(sym, path, file)
    

object Importer:
  /**
    * To be compatible with JavaScript ecosystem, we currently use the format of npm.
    * 
    * 1. **Group 1:** Scope (no `@`)
    *      + Example: `@my-org/foo/bar` → `"my-org"`
    * 2. **Group 2:** Package name
    *      + Example: `@my-org/foo/bar` → `"foo"`
    *      + Example: `mypkg/test` → `"mypkg"`
    * 3. **Group 3:** The remaining text after the first slash
    *      + Example: `@my-org/foo/bar/baz` → `"bar/baz"`
    *      + Example: `mypkg/sub/path` → `"sub/path"`
    *      + Example: `mypkg` → `null`
    */
  private val r = """^(?:@([a-z0-9-~][a-z0-9-._~]*)\/)?([a-z0-9-~][a-z0-9-._~]*)(?:\/(.*))?$""".r
