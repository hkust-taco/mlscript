package ts2mls

import scala.collection.mutable.HashMap
import mlscript.utils._
import ts2mls.types.{TSTypeAlias, TSReferenceType, Converter}

final case class TSReExport(alias: String, filename: String, memberName: Option[String])

trait TSImport { self =>
  val filename: String

  def resolveTypeAlias(name: String): Option[String] = self match {
    case TSFullImport(filename, _) => Some(s"${TSModuleResolver.basename(filename)}.$name")
    case TSSingleImport(filename, items) =>
      items.collect {
        case (originalName, _) if (originalName === name) =>
          s"${TSModuleResolver.basename(filename)}.$name"
      }.headOption
  }

  def createAlias: List[TSReExport] = self match {
    case TSFullImport(filename, alias) =>
      TSReExport(alias, filename, None) :: Nil
    case TSSingleImport(filename, items) =>
      items.map{ case (name, alias) =>
        TSReExport(alias.getOrElse(name), filename, Some(name))
      }
  }

  def generate(ns: TSNamespace, writer: JSWriter): Unit = self match {
    case _: TSFullImport => ns.generate(writer, "  ")
    case TSSingleImport(_, items) => items.foreach((pair) => pair match {
      case (name, _) => writer.writeln(Converter.convert(ns.get(name), true)("  "))
    })
  }
}

object TSImport {
  def createInterfaceForNode(path: String): String = {
    val moduleName = TSModuleResolver.basename(path)
    val topLevelModule =
      if (path.contains("/")) path.substring(0, path.indexOf("/"))
      else moduleName
    s"node_modules/$topLevelModule/$moduleName.mlsi"
  }
}

// import * as alias from "filename"
case class TSFullImport(filename: String, alias: String) extends TSImport
// import { s1, s2 as a } from "filename"
// export { s1, s2 as a } from "filename"
case class TSSingleImport(filename: String, items: List[(String, Option[String])]) extends TSImport

class TSImportList {
  private val singleList = new HashMap[String, TSSingleImport]()
  private val fullList = new HashMap[String, TSFullImport]()

  def add(fullPath: String, imp: TSImport): Unit = imp match {
    case imp: TSFullImport => fullList.addOne((fullPath, imp))
    case imp @ TSSingleImport(filename, items) =>
      if (singleList.contains(fullPath))
        singleList.update(fullPath, TSSingleImport(filename, singleList(fullPath).items ::: items)) 
      else singleList.addOne((fullPath, imp))
  }

  def resolveTypeAlias(modulePath: String, name: String): String = {
    val singleAlias =
      if (singleList.contains(modulePath)) singleList(modulePath).resolveTypeAlias(name)
      else None
    singleAlias match {
      case Some(alias) => alias
      case None =>
        val fullAlias =
          if (fullList.contains(modulePath)) fullList(modulePath).resolveTypeAlias(name)
          else None
        fullAlias.getOrElse(throw new AssertionError(s"unresolved imported name $name at $modulePath."))
    }
  }

  def getFilelist: List[TSImport] =
    (singleList.values.toList ::: fullList.values.toList)
}

object TSImportList {
  def apply() = new TSImportList()
}
