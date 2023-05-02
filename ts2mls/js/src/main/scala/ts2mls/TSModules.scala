package ts2mls

import scala.collection.mutable.HashMap
import mlscript.utils._
import ts2mls.types.{TSTypeAlias, TSReferenceType}

trait TSImport { self =>
  def resolveTypeAlias(name: String): Option[String] = self match {
    case TSFullImport(_, alias, _) => Some(s"$alias.$name")
    case TSSingleImport(_, items) =>
      items.collect {
        case (originalName, alias, _) if (originalName === name) =>
          alias.getOrElse(originalName)
      }.headOption
  }

  def convertAlias: List[(TSTypeAlias, Boolean)] = self match {
    case TSFullImport(filename, alias, reExp) =>
      val originalName = TSImport.getModuleName(filename)
      if (originalName === alias) Nil
      else (TSTypeAlias(alias, TSReferenceType(originalName), Nil), reExp) :: Nil
    case TSSingleImport(filename, items) =>
      val moduleName = TSImport.getModuleName(filename)
      items.map {
        case (originalName, Some(alias), reExp) =>
          (TSTypeAlias(alias, TSReferenceType(s"$moduleName.$originalName"), Nil), reExp)
        case (originalName, None, reExp) =>
          (TSTypeAlias(originalName, TSReferenceType(s"$moduleName.$originalName"), Nil), reExp)
      }
  }
}

object TSImport {
  def getModuleName(filename: String): String =
    if (filename.endsWith(".d") || filename.endsWith(".ts"))
      getModuleName(filename.substring(filename.lastIndexOf('/') + 1, filename.lastIndexOf('.')))
    else
      filename.substring(filename.lastIndexOf('/') + 1)
}

// import * as alias from "filename"
case class TSFullImport(filename: String, alias: String, reExported: Boolean) extends TSImport
// import { s1, s2 as a } from "filename"
// export { s1, s2 as a } from "filename"
case class TSSingleImport(filename: String, items: List[(String, Option[String], Boolean)]) extends TSImport

class TSImportList {
  private val singleList = new HashMap[String, TSSingleImport]()
  private val fullList = new HashMap[String, TSFullImport]()

  def +=(imp: TSImport): Unit = imp match {
    case imp @ TSFullImport(filename, _, _) => fullList.addOne((filename, imp))
    case imp @ TSSingleImport(filename, items) =>
      if (singleList.contains(filename))
        singleList.update(filename, TSSingleImport(filename, singleList(filename).items ::: items)) 
      else singleList.addOne((filename, imp))
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

  def convertAlias: List[(TSTypeAlias, Boolean)] =
    singleList.values.flatMap(_.convertAlias).toList ::: fullList.values.flatMap(_.convertAlias).toList

  def getFilelist: List[String] =
    (singleList.keys.toList ::: fullList.keys.toList).distinct
}

object TSImportList {
  def apply() = new TSImportList()
}
