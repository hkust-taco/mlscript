package driver

import mlscript._
import mlscript.codegen._
import mlscript.utils._, shorthands._, algorithms._
import mlscript.codegen.Helpers._

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

  private def generateNewDef(pgrm: Pgrm, topModuleName: Str, exported: Bool): Ls[Str] = {
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
      if (exported) JSExport(insDecl) :: invoke :: Nil
      else insDecl :: invoke :: Nil

    SourceCode.fromStmts(polyfill.emit() ++ ins).toLines
  }

  import JSDriverBackend.ModuleType

  private def translateImport(imp: Import with ModuleType) = {
    val path = imp.path
    val last = path.lastIndexOf(".")
    JSImport(
      path.substring(path.lastIndexOf("/") + 1, if (last < 0) path.length() else last),
      path.substring(0, if (last < 0) path.length() else last) + (if (last < 0) "" else ".js"),
      imp.isESModule
    )
  }

  def apply(pgrm: Pgrm, topModuleName: Str, imports: Ls[Import with ModuleType], exported: Bool): Ls[Str] = {
    imports.flatMap (imp => {
      val path = imp.path
      val last = path.lastIndexOf(".")
        val moduleName = path.substring(path.lastIndexOf("/") + 1, if (last < 0) path.length() else last)
        topLevelScope.declareValue(moduleName, Some(false), false)
        translateImport(imp).toSourceCode.toLines 
    }) ::: generateNewDef(pgrm, topModuleName, exported)
  }
}

object JSDriverBackend {
   // N -> mls module, S(true) -> ES module, S(false) -> CommonJS module
  trait ModuleType {
    val isESModule: Opt[Bool]
  }
}
