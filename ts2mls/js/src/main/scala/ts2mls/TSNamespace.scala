package ts2mls

import scala.collection.mutable.{HashMap, ListBuffer}
import types._

class TSNamespace(name: String, parent: Option[TSNamespace]) {
  private val subSpace = HashMap[String, TSNamespace]()
  private val members = HashMap[String, TSType]()

  // write down the order of members
  // easier to check the output one by one
  private val order = ListBuffer.empty[Either[String, String]]

  def derive(name: String): TSNamespace = {
    if (subSpace.contains(name)) subSpace(name) // if the namespace has appeared in another file, just return it
    else {
      val sub = new TSNamespace(name, Some(this))
      subSpace.put(name, sub)
      order += Left(name)
      sub
    }
  }

  def put(name: String, tp: TSType): Unit =
    if (!members.contains(name)) {
      order += Right(name)
      members.put(name, tp)
    }
    else members.update(name, tp)

  def get(name: String): TSType =
    members.getOrElse(name,
      if (!parent.isEmpty) parent.get.get(name) else throw new Exception(s"member $name not found."))

  def containsMember(name: String, searchParent: Boolean = true): Boolean =
    if (parent.isEmpty) members.contains(name) else (members.contains(name) || (searchParent && parent.get.containsMember(name)))

  def generate(writer: JSWriter): Unit =
    order.toList.foreach((p) => p match {
      case Left(name) => subSpace(name).generate(writer)
      case Right(name) => {
        val mem = members(name)
        val fullName = getFullPath(name)
        mem match {
          case inter: TSIntersectionType => { // overloaded functions
            val typeParams = TSIntersectionType.getOverloadTypeParameters(inter).map((t) => t.name)

            if (typeParams.isEmpty)
              writer.writeln(s"def ${fullName}: ${Converter.convert(inter)}")
            else // TODO: add constraints
              writer.writeln(s"def ${fullName}[${typeParams.reduceLeft((r, s) => s"$r, $s")}]: ${Converter.convert(inter)}")
          }
          case f: TSFunctionType => {
            val typeParams = f.typeVars.map((t) => t.name)
            if (typeParams.isEmpty)
              writer.writeln(s"def ${fullName}: ${Converter.convert(f)}")
            else // TODO: add constraints
              writer.writeln(s"def ${fullName}[${typeParams.reduceLeft((r, s) => s"$r, $s")}]: ${Converter.convert(f)}")
          }
          case _ => writer.writeln(Converter.convert(mem))
        }
      }
    })

  // generate full path with namespaces' names
  // e.g. f => Namespace1.Namespace2.f
  def getFullPath(nm: String): String = parent match {
    case Some(p) => p.getFullPath(s"$name'$nm")
    case _ => nm
  }
}

object TSNamespace {
  def apply() = new TSNamespace("", None) // global namespace
}
