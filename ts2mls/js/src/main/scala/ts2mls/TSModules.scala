package ts2mls

import scala.collection.mutable.HashMap
import mlscript.utils._
import ts2mls.types.{TSTypeAlias, TSReferenceType}

trait TSImport { self =>
  def resolveTypeAlias(name: String): Option[String] = self match {
    case TSFullImport(filename, _) => Some(s"${TSImport.getModuleName(filename)}.$name")
    case TSSingleImport(filename, items) =>
      items.collect {
        case (originalName, _) if (originalName === name) =>
          s"${TSImport.getModuleName(filename)}.$name"
      }.headOption
  }

  def createAlias: List[TSTypeAlias] = self match {
    case TSFullImport(filename, alias) =>
      TSTypeAlias(alias, TSReferenceType(TSImport.getModuleName(filename)), Nil) :: Nil
    case TSSingleImport(filename, items) =>
      items.map{ case (name, alias) =>
        TSTypeAlias(alias.getOrElse(name), TSReferenceType(s"${TSImport.getModuleName(filename)}.$name"), Nil)
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
case class TSFullImport(filename: String, alias: String) extends TSImport
// import { s1, s2 as a } from "filename"
// export { s1, s2 as a } from "filename"
case class TSSingleImport(filename: String, items: List[(String, Option[String])]) extends TSImport

class TSImportList {
  private val singleList = new HashMap[String, TSSingleImport]()
  private val fullList = new HashMap[String, TSFullImport]()

  def +=(imp: TSImport): Unit = imp match {
    case imp @ TSFullImport(filename, _) => fullList.addOne((filename, imp))
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

  def getFilelist: List[String] =
    (singleList.keys.toList ::: fullList.keys.toList).distinct
}

object TSImportList {
  def apply() = new TSImportList()
}
