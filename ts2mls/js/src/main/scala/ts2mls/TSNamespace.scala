package ts2mls

import scala.collection.mutable.{HashMap, ListBuffer}
import types._

class TSNamespace(name: String, parent: Option[TSNamespace]) extends Module {
  private val subSpace = HashMap[String, TSNamespace]()
  private val members = HashMap[String, TSType]()

  private val order = ListBuffer.empty[Either[String, String]]

  private lazy val showPrefix = if (name.equals("globalThis")) "" else s"$name."

  def derive(name: String): TSNamespace = {
    val sub = new TSNamespace(name, Some(this))
    subSpace.put(name, sub)
    order += Left(name)
    sub
  }

  def put(name: String, tp: TSType): Unit = {
    if (!members.contains(name)) order += Right(name)
    
    members.put(name, tp)
  }

  override def >(name: String): TSType = members.get(name) match {
    case Some(tst) => tst
    case None if (!parent.isEmpty) => parent.get.>(name)
    case _ => throw new java.lang.Exception(s"member $name not found.")
  }
  override def >>(name: String): TSNamespace = subSpace.getOrElse(name, throw new java.lang.Exception(s"namespace $name not found."))

  override def toString(): String = s"namespace $name"

  def containsMember(name: String, searchParent: Boolean = true): Boolean = 
    if (parent.isEmpty) members.contains(name) else (members.contains(name) || (searchParent && parent.get.containsMember(name)))

  def containsMember(path: List[String]): Boolean = path match {
    case name :: Nil => containsMember(name)
    case sub :: rest if (subSpace.contains(sub)) => subSpace(sub).containsMember(rest)
    case _ => false
  }

  override def visit(writer: DecWriter, prefix: String): Unit = {
    order.toList.foreach((p) => p match {
      case Left(name) => subSpace(name).visit(writer, prefix + showPrefix)
      case Right(name) => {
        val mem = members(name)
        mem match {
          case inter: TSIntersectionType => {
            val nsName = getFullName()
            val fullName = if (nsName.equals("")) name else s"$nsName'${name}"
            val params = TSNamespace.getOverloadTypeVariables(inter).foldLeft("")((p, t) => s"$p${t.name}, ") // TODO: add constraints

            if (params.length() == 0)
              writer.generate(s"def ${fullName}: ${TSProgram.getMLSType(inter)}")
            else
              writer.generate(s"def ${fullName}[${params.substring(0, params.length() - 2)}]: ${TSProgram.getMLSType(inter)}")
          }
          case f: TSFunctionType => {
            if (f.dbg) writer.debug(s"${prefix}$showPrefix${name}", f.toString)
          
            val nsName = getFullName()
            val fullName = if (nsName.equals("")) name else s"$nsName'${name}"
            val params = f.typeVars.foldLeft("")((p, t) => s"$p${t.name}, ") // TODO: add constraints
            if (params.length() == 0)
              writer.generate(s"def ${fullName}: ${TSProgram.getMLSType(f)}")
            else
              writer.generate(s"def ${fullName}[${params.substring(0, params.length() - 2)}]: ${TSProgram.getMLSType(f)}")
          }
          case _ => writer.generate(TSProgram.getMLSType(mem))
        }
      }
    })
  }

  def getFullName(): String = parent match {
    case Some(p) => {
      val pn = p.getFullName()
      if (pn.equals("")) name
      else s"$pn'$name"
    }
    case _ => ""
  }
}

object TSNamespace {
  def apply() = new TSNamespace("globalThis", None)

  private def getOverloadTypeVariables(inter: TSIntersectionType): List[TSTypeVariable] = inter match {
    case TSIntersectionType(lhs, rhs) => {
      val left = lhs match {
        case i: TSIntersectionType => getOverloadTypeVariables(i)
        case TSFunctionType(_, _, v) => v
      }

      val right = rhs match {
        case i: TSIntersectionType => getOverloadTypeVariables(i)
        case TSFunctionType(_, _, v) => v
      }

      (left ::: right).distinct
    }
    case _ => List()
  }
}
