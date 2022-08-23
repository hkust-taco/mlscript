package ts2mls

import scala.collection.mutable.{HashMap, ListBuffer}
import types._

class TSNamespace(name: String, parent: Option[TSNamespace]) {
  private val subSpace = HashMap[String, TSNamespace]()
  private val members = HashMap[String, TSType]()

  // write down the order of members
  // easier to check the output one by one
  private val order = ListBuffer.empty[Either[String, String]]

  private lazy val showPrefix = if (name.equals("")) "" else s"$name."

  def derive(name: String): TSNamespace = {
    if (subSpace.contains(name)) subSpace(name) // if the namespace has appeared in another file, just return it
    else {
      val sub = new TSNamespace(name, Some(this))
      subSpace.put(name, sub)
      order += Left(name)
      sub
    }
  }

  def put(name: String, tp: TSType): Unit = {
    if (!members.contains(name)) order += Right(name)
    members.put(name, tp)
  }

  def get(name: String): TSType =
    members.getOrElse(name,
      if (!parent.isEmpty) parent.get.get(name) else throw new Exception(s"member $name not found."))

  def containsMember(name: String, searchParent: Boolean = true): Boolean = 
    if (parent.isEmpty) members.contains(name) else (members.contains(name) || (searchParent && parent.get.containsMember(name)))

  // an overload version for searching members like `Namespace1.Namespace2.ClassName`
  def containsMember(path: List[String]): Boolean = path match {
    case name :: Nil => containsMember(name)
    case sub :: rest if (subSpace.contains(sub)) => subSpace(sub).containsMember(rest)
    case _ => false
  }

  def generate(writer: JSWriter, prefix: String): Unit = {
    order.toList.foreach((p) => p match {
      case Left(name) => subSpace(name).generate(writer, prefix + showPrefix)
      case Right(name) => {
        val mem = members(name)
        mem match {
          case inter: TSIntersectionType => { // overloaded functions
            val fullName = getFullPath(name)
            val params = TSIntersectionType.getOverloadTypeVariables(inter).map((t) => t.name) 

            if (params.isEmpty)
              writer.writeln(s"def ${fullName}: ${TSProgram.getMLSType(inter)}")
            else // TODO: add constraints
              writer.writeln(s"def ${fullName}[${params.reduceLeft((r, s) => s"$r, $s")}]: ${TSProgram.getMLSType(inter)}")
          }
          case f: TSFunctionType => {
            val fullName = getFullPath(name)
            val params = f.typeVars.map((t) => t.name) 
            if (params.isEmpty)
              writer.writeln(s"def ${fullName}: ${TSProgram.getMLSType(f)}")
            else // TODO: add constraints
              writer.writeln(s"def ${fullName}[${params.reduceLeft((r, s) => s"$r, $s")}]: ${TSProgram.getMLSType(f)}")
          }
          case _ => writer.writeln(TSProgram.getMLSType(mem))
        }
      }
    })
  }

  // generate full path with namespaces
  def getFullPath(nm: String): String = parent match {
    case Some(p) => p.getFullPath(s"$name'$nm")
    case _ => nm
  }
}

object TSNamespace {
  def apply() = new TSNamespace("", None)
}
