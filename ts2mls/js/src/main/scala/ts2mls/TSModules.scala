package ts2mls

import scala.collection.mutable.HashMap
import mlscript.utils._
import ts2mls.types.{TSTypeAlias, TSReferenceType, Converter}

final case class TSReExport(alias: String, filename: String, memberName: Option[String])

trait TSImport { self =>
  val filename: String
  val `import`: String

  def resolveTypeAlias(name: String): Option[String] = self match {
    case TSFullImport(filename, _, _) => Some(s"${TSImport.getModuleName(filename, false)}.$name")
    case TSSingleImport(filename, _, items) =>
      items.collect {
        case (originalName, _) if (originalName === name) =>
          s"${TSImport.getModuleName(filename, false)}.$name"
      }.headOption
  }

  def createAlias: List[TSReExport] = self match {
    case TSFullImport(filename, _, alias) =>
      TSReExport(alias, filename, None) :: Nil
    case TSSingleImport(filename, _, items) =>
      items.map{ case (name, alias) =>
        TSReExport(alias.getOrElse(name), filename, Some(name))
      }
  }

  def generate(ns: TSNamespace, writer: JSWriter): Unit = self match {
    case _: TSFullImport => ns.generate(writer, "  ")
    case TSSingleImport(_, _, items) => items.foreach((pair) => pair match {
      case (name, _) => writer.writeln(Converter.convert(ns.get(name), true)("  "))
    })
  }
}

object TSImport {
  def getModuleName(filename: String, requirePrefix: Boolean): String =
    if (filename.endsWith(".d") || filename.endsWith(".ts"))
      getModuleName(filename.substring(filename.lastIndexOf('/') + 1, filename.lastIndexOf('.')), requirePrefix)
    else if (!requirePrefix)
      filename.substring(filename.lastIndexOf('/') + 1)
    else filename
}

// import * as alias from "`import`"; // filename is absolute
case class TSFullImport(filename: String, `import`: String, alias: String) extends TSImport
// import { s1, s2 as a } from "`import`"; // filename is absolute
// export { s1, s2 as a } from "`import`"; // filename is absolute
case class TSSingleImport(filename: String, `import`: String, items: List[(String, Option[String])]) extends TSImport

class TSImportList {
  private val singleList = new HashMap[String, TSSingleImport]()
  private val fullList = new HashMap[String, TSFullImport]()

  def +=(imp: TSImport): Unit = imp match {
    case imp @ TSFullImport(filename, _, _) => fullList.addOne((filename, imp))
    case imp @ TSSingleImport(filename, impName, items) =>
      if (singleList.contains(filename))
        singleList.update(filename, TSSingleImport(filename, impName, singleList(filename).items ::: items)) 
      else singleList.addOne((filename, imp))
  }

  def resolveTypeAlias(modulePath: String, name: String): String = {
    val absPath = TSModuleResolver.resolve(modulePath)
    val singleAlias =
      if (singleList.contains(absPath)) singleList(absPath).resolveTypeAlias(name)
      else None
    singleAlias match {
      case Some(alias) => alias
      case None =>
        val fullAlias =
          if (fullList.contains(absPath)) fullList(absPath).resolveTypeAlias(name)
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
