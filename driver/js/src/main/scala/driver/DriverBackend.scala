package driver

import mlscript._
import mlscript.codegen._
import mlscript.utils._, shorthands._, algorithms._
import mlscript.codegen.Helpers._
import ts2mls.TSPathResolver

class JSDriverBackend extends JSBackend(allowUnresolvedSymbols = false) {
  def declareJSBuiltin(pgrm: Pgrm): Unit = {
    val (typeDefs, otherStmts) = pgrm.tops.partitionMap {
      case ot: Terms => R(ot)
      case fd: NuFunDef => R(fd)
      case nd: NuTypeDef => L(nd)
      case _ => die
    }

    declareNewTypeDefs(typeDefs, false)(topLevelScope)
    otherStmts.foreach {
      case NuFunDef(_, Var(name), _, _) =>
        topLevelScope.declareStubValue(name)(true)
      case _ => ()
    }
  }

  private def generateNewDef(pgrm: Pgrm, topModuleName: Str, exported: Bool, commonJS: Bool): Ls[Str] = {
    val (typeDefs, otherStmts) = pgrm.tops.partitionMap {
      case ot: Terms => R(ot)
      case fd: NuFunDef => R(fd)
      case nd: NuTypeDef => L(nd)
      case _ => die
    }

    val topModule = topLevelScope.declareTopModule(topModuleName, otherStmts, typeDefs, false)
    val moduleDecl = translateTopModuleDeclaration(topModule, false, true)(topLevelScope)
    val initMethod = moduleDecl.methods.lastOption match {
      case Some(JSClassMethod(name, _, _)) => name
      case _ => throw new CodeGenError(s"can not get $$init method of module $topModuleName.")
    }
    val invoke = JSInvoke(JSIdent(topModuleName).member(initMethod), Nil).stmt
    val insDecl = JSConstDecl(topModuleName, JSNew(JSClassExpr(moduleDecl)))

    val ins =
      if (exported) {
        if (commonJS) insDecl :: invoke :: JSExport(R(JSIdent(topModuleName))) :: Nil
        else JSExport(L(insDecl)) :: invoke :: Nil
      }
      else insDecl :: invoke :: Nil

    SourceCode.fromStmts(polyfill.emit() ++ ins).toLines
  }

  import JSDriverBackend.ModuleType

  private def translateImport(imp: Import with ModuleType, commonJS: Bool) = {
    val path = imp.path
    val ext = TSPathResolver.extname(path)
    JSImport(
      TSPathResolver.basename(path), if (ext.isEmpty()) path else path.replace(ext, ".js"),
      imp.isESModule, commonJS
    )
  }

  def apply(pgrm: Pgrm, topModuleName: Str, imports: Ls[Import with ModuleType], exported: Bool, commonJS: Bool): Ls[Str] = {
    imports.flatMap (imp => {
      topLevelScope.declareValue(TSPathResolver.basename(imp.path), Some(false), false)
      translateImport(imp, commonJS).toSourceCode.toLines 
    }) ::: generateNewDef(pgrm, topModuleName, exported, commonJS)
  }
}

object JSDriverBackend {
   // N -> mls module, S(true) -> ES module, S(false) -> CommonJS module
  trait ModuleType {
    val isESModule: Opt[Bool]
  }
}
